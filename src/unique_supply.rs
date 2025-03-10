pub struct UniqueSupply<T, F>
where T: Copy, F: FnMut(T) -> T {
  seed  : T,
  update: F  
}


impl<T,F> UniqueSupply<T,F> 
where T: Copy, F : FnMut(T) -> T { 
   pub fn new_unique(mut self: UniqueSupply<T,F>) -> T {
      let t = self.seed;
      self.seed = (self.update)(self.seed); 
      return t;
  }

  pub fn new(t:T, f: F) -> Self {
    Self { seed: t, update: f }
  }
}