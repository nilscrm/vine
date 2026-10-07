use std::fmt;

/// The address of a heap object; an index of a word in the heap.
///
/// Address `0` is never allocated, so it can be used as a null pointer.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Addr(pub u64);

impl Addr {
  pub const NULL: Addr = Addr(0);

  pub fn offset(self, offset: u32) -> Addr {
    Addr(self.0 + offset as u64)
  }
}

impl fmt::Debug for Addr {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "@{}", self.0)
  }
}

/// A heap of words, with free lists for each object size.
///
/// Objects are freed explicitly; the caller is responsible for passing the
/// same size to [`Heap::free`] as was passed to [`Heap::alloc`].
#[derive(Debug)]
pub struct Heap {
  words: Vec<u64>,
  free: Vec<Vec<Addr>>,
  pub stats: HeapStats,
}

#[derive(Debug, Default, Clone)]
pub struct HeapStats {
  /// The number of objects allocated.
  pub allocs: u64,
  /// The number of objects freed.
  pub frees: u64,
  /// The number of words currently allocated.
  pub live_words: u64,
  /// The maximum number of words allocated at once.
  pub peak_words: u64,
}

impl Default for Heap {
  fn default() -> Self {
    Self::new()
  }
}

impl Heap {
  pub fn new() -> Self {
    Heap { words: vec![0], free: Vec::new(), stats: HeapStats::default() }
  }

  /// Allocates an object of `len` words, whose contents are unspecified.
  ///
  /// Zero-sized objects are allocated one word, so that every object has a
  /// distinct address.
  pub fn alloc(&mut self, len: u32) -> Addr {
    let len = len.max(1);
    self.stats.allocs += 1;
    self.stats.live_words += len as u64;
    self.stats.peak_words = self.stats.peak_words.max(self.stats.live_words);
    if let Some(addr) = self.free.get_mut(len as usize).and_then(Vec::pop) {
      return addr;
    }
    let addr = Addr(self.words.len() as u64);
    self.words.resize(self.words.len() + len as usize, 0);
    addr
  }

  /// Frees an object of `len` words.
  pub fn free(&mut self, addr: Addr, len: u32) {
    debug_assert!(addr != Addr::NULL);
    let len = len.max(1);
    self.stats.frees += 1;
    self.stats.live_words -= len as u64;
    if self.free.len() <= len as usize {
      self.free.resize_with(len as usize + 1, Vec::new);
    }
    self.free[len as usize].push(addr);
  }

  pub fn live_objects(&self) -> u64 {
    self.stats.allocs - self.stats.frees
  }

  pub fn get(&self, addr: Addr) -> u64 {
    self.words[addr.0 as usize]
  }

  pub fn set(&mut self, addr: Addr, word: u64) {
    self.words[addr.0 as usize] = word;
  }

  pub fn slice(&self, addr: Addr, len: u32) -> &[u64] {
    &self.words[addr.0 as usize..addr.0 as usize + len as usize]
  }

  pub fn slice_mut(&mut self, addr: Addr, len: u32) -> &mut [u64] {
    &mut self.words[addr.0 as usize..addr.0 as usize + len as usize]
  }
}
