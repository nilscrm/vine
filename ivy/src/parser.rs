use vine_util::{
  lexer::TokenSet,
  parser::{Parser, ParserState},
};

use crate::{
  ast::{Net, Nets, Polarity, PrimitiveType, Tree, TreeNode, Type},
  lexer::Token,
};

pub struct IvyParser<'src> {
  pub state: ParserState<'src, Token>,
}

#[derive(Debug, Clone)]
pub enum ParseError<'src> {
  LexError,
  UnexpectedToken { expected: TokenSet<Token>, found: &'src str },
  InvalidNum(&'src str),
  InvalidLabel(&'src str),
  InvalidExtFn(&'src str),
}

type Parse<'src, T = ()> = Result<T, ParseError<'src>>;

impl<'src> Parser<'src> for IvyParser<'src> {
  type Token = Token;
  type Error = ParseError<'src>;

  fn state(&mut self) -> &mut ParserState<'src, Self::Token> {
    &mut self.state
  }

  fn lex_error(&self) -> Self::Error {
    ParseError::LexError
  }

  fn unexpected_error(&self) -> ParseError<'src> {
    ParseError::UnexpectedToken { expected: self.state.expected, found: self.state.lexer.slice() }
  }
}

impl<'src> IvyParser<'src> {
  pub fn parse(src: &'src str) -> Parse<'src, Nets> {
    let mut parser = IvyParser { state: ParserState::new(src) };
    parser.bump()?;
    let mut nets = Nets::default();
    while parser.state.token.is_some() {
      let name = parser.expect(Token::Global)?.to_owned();
      let net = parser.parse_net()?;
      nets.insert(name, net);
    }
    Ok(nets)
  }

  fn parse_n32(&mut self) -> Parse<'src, u32> {
    let token = self.expect(Token::N32)?;
    self.parse_u32_like(token, ParseError::InvalidNum)
  }

  fn parse_f32(&mut self) -> Parse<'src, f32> {
    let token = self.expect(Token::F32)?;
    self.parse_f32_like(token, ParseError::InvalidNum)
  }

  fn parse_net(&mut self) -> Parse<'src, Net> {
    self.expect(Token::OpenBrace)?;
    let net = self.parse_net_inner()?;
    self.expect(Token::CloseBrace)?;
    Ok(net)
  }

  #[doc(hidden)] // used by Vine to parse `inline_ivy!`
  pub fn parse_net_inner(&mut self) -> Parse<'src, Net> {
    let root = self.parse_tree()?;
    let mut pairs = Vec::new();
    while !self.check(Token::CloseBrace) {
      pairs.push(self.parse_pair()?);
    }
    Ok(Net { root, pairs })
  }

  pub(super) fn parse_pair(&mut self) -> Parse<'src, (Tree, Tree)> {
    let a = self.parse_tree()?;
    self.expect(Token::Eq)?;
    let b = self.parse_tree()?;
    Ok((a, b))
  }

  fn parse_tree(&mut self) -> Parse<'src, Tree> {
    let tree = self.parse_tree_node()?;
    if self.eat(Token::Colon)? {
      let ty = self.parse_type()?;
      Ok(Tree { tree_node: tree, ty: Some(ty) })
    } else {
      Ok(Tree { tree_node: tree, ty: None })
    }
  }

  fn parse_tree_node(&mut self) -> Parse<'src, TreeNode> {
    if self.check(Token::N32) {
      return Ok(TreeNode::N32(self.parse_n32()?));
    }

    if self.check(Token::F32) {
      return Ok(TreeNode::F32(self.parse_f32()?));
    }

    if self.check(Token::Global) {
      return Ok(TreeNode::Global(self.expect(Token::Global)?.to_owned()));
    }

    if self.check(Token::Ident) {
      let ident = self.expect(Token::Ident)?.to_owned();
      if self.eat(Token::OpenParen)? {
        let label = ident;
        let a = self.parse_tree()?;
        let b = self.parse_tree()?;
        self.expect(Token::CloseParen)?;
        return Ok(TreeNode::Comb(label, Box::new(a), Box::new(b)));
      } else {
        return Ok(TreeNode::Var(ident));
      }
    }

    if self.eat(Token::At)? {
      let name = self.expect(Token::Ident)?;
      let ext_fn = name.to_string();
      let swapped = self.eat(Token::Dollar)?;
      self.expect(Token::OpenParen)?;
      let a = self.parse_tree()?;
      let b = self.parse_tree()?;
      self.expect(Token::CloseParen)?;
      return Ok(TreeNode::ExtFn(ext_fn, swapped, Box::new(a), Box::new(b)));
    }

    if self.eat(Token::Question)? {
      self.expect(Token::OpenParen)?;
      let a = self.parse_tree()?;
      let b = self.parse_tree()?;
      let c = self.parse_tree()?;
      self.expect(Token::CloseParen)?;
      return Ok(TreeNode::Branch(Box::new(a), Box::new(b), Box::new(c)));
    }

    if self.eat(Token::Hole)? {
      return Ok(TreeNode::Erase);
    }

    if self.eat(Token::Hash)? {
      self.expect(Token::OpenBracket)?;
      let inner = self.parse_tree()?;
      self.expect(Token::CloseBracket)?;
      return Ok(TreeNode::BlackBox(Box::new(inner)));
    }

    self.unexpected()
  }

  fn parse_type(&mut self) -> Parse<'src, Type> {
    if self.check(Token::Ident) {
      let label = self.expect(Token::Ident)?.to_owned();
      if self.eat(Token::OpenParen)? {
        let left = self.parse_type()?;
        let right = self.parse_type()?;
        self.expect(Token::CloseParen)?;
        return Ok(Type::Pair { label, left: Box::new(left), right: Box::new(right) });
      }
    }

    let polarity = self.parse_polarity()?;
    let primitive_type = self.parse_primitive_type()?;
    let lifetime = if self.eat(Token::SingleQuote)? {
      let lifetime = self.expect(Token::Ident)?.to_string();
      Some(lifetime)
    } else {
      None
    };

    Ok(Type::Primitive { ty: primitive_type, polarity, lifetime })
  }

  fn parse_primitive_type(&mut self) -> Parse<'src, PrimitiveType> {
    if self.eat(Token::N32Ty)? {
      Ok(PrimitiveType::N32)
    } else if self.eat(Token::F32Ty)? {
      Ok(PrimitiveType::F32)
    } else if self.eat(Token::IOTy)? {
      Ok(PrimitiveType::IO)
    } else {
      self.unexpected()
    }
  }

  fn parse_polarity(&mut self) -> Parse<'src, Polarity> {
    if self.eat(Token::Tilde)? {
      Ok(Polarity::In)
    } else {
      Ok(Polarity::Out)
    }
  }
}
