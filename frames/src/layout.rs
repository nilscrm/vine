use vine_util::{idx::IdxVec, new_idx};

new_idx!(pub LayoutId; n => ["L{n}"]);

/// Describes how a value is stored in words, as far as is needed to deeply
/// copy or free it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Layout {
  /// The number of words the value occupies.
  pub size: u32,
  /// The parts of the value that own heap data, or that cannot be copied or
  /// freed; words not covered by any field are plain data.
  pub fields: Vec<Field>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Field {
  /// A pointer to a heap object containing a value of the given layout.
  Box { offset: u32, layout: LayoutId },
  /// A tag word, followed by the payload of the selected variant; the payload
  /// occupies the words after the tag, padded to the largest variant.
  Enum { offset: u32, variants: Vec<LayoutId> },
  /// A value of the given layout, stored inline.
  Inline { offset: u32, layout: LayoutId },
  /// A value that cannot be copied or freed generically, such as a space, a
  /// promise, a hole, or the variants of an untagged union.
  Opaque { offset: u32, what: &'static str },
}

impl Layout {
  pub const EMPTY: Layout = Layout { size: 0, fields: Vec::new() };

  pub fn data(size: u32) -> Layout {
    Layout { size, fields: Vec::new() }
  }

  /// Whether a value of this layout is plain data, which can be copied and
  /// freed by copying and dropping its words.
  pub fn is_plain(&self) -> bool {
    self.fields.is_empty()
  }
}

/// The layouts used by a program.
#[derive(Debug, Default, Clone)]
pub struct Layouts {
  pub layouts: IdxVec<LayoutId, Layout>,
}

impl Layouts {
  pub fn add(&mut self, layout: Layout) -> LayoutId {
    self.layouts.push(layout)
  }

  /// Reserves an id for a layout that will be defined later with
  /// [`Layouts::define`]; used for recursive layouts.
  pub fn reserve(&mut self) -> LayoutId {
    self.layouts.push(Layout::EMPTY)
  }

  pub fn define(&mut self, id: LayoutId, layout: Layout) {
    self.layouts[id] = layout;
  }
}
