use std::marker::PhantomData;


#[derive(PartialEq, PartialOrd, Eq, Ord, Clone, Copy)]
enum Constraint { Constraint }  
#[derive(PartialEq, PartialOrd, Eq, Ord, Clone, Copy)]
enum Stack { Stack }  
#[derive(PartialEq, PartialOrd, Eq, Ord, Clone, Copy)]
enum Heap { Heap }

enum ProgramCounter { PC } 
enum Supply<I> { Supply(I) } 

#[derive(PartialEq, PartialOrd, Eq, Ord, Clone, Copy)]
pub struct Fragment{
  constraint : Constraint,
  stack      : Stack,
  heap       : Heap,
}

impl Abstraction<Constraint, Stack, Heap> for Fragment{
  fn get_cnstr(&self) -> Constraint { return self.constraint }
  fn get_stack(&self) -> Stack      { return self.stack      }
  fn get_heap( &self) -> Heap       { return self.heap       }

  fn alt_cnstr(&self, alter: fn(&Constraint) -> ()) -> (){ alter (&self.constraint)}
  fn alt_stack(&self, alter: fn(&Stack) -> ())      -> (){ alter (&self.stack)}
  fn alt_heap( &self, alter: fn(&Heap) -> ())       -> (){ alter (&self.heap)}

  fn lower(fragment : Fragment) -> Self      { return fragment}
  fn upper(&self)               -> &Fragment { return self }

}

pub trait Abstraction<C,S,H> : Ord
{
  fn get_cnstr(&self) -> C;
  fn get_stack(&self) -> S;
  fn get_heap( &self) -> H;
  
  fn alt_cnstr(&self, alter: fn(&C) -> ()) -> ();
  fn alt_stack(&self, alter: fn(&S) -> ()) -> ();
  fn alt_heap( &self, alter: fn(&H) -> ()) -> ();
  
  fn lower(fragment : Fragment) -> Self ;
  fn upper(&self)               -> &Fragment;
}

pub struct State<F, C, S, H>
  where F : Abstraction<C,S,H>
{
  phantom_c : PhantomData<C>,
  phantom_s : PhantomData<S>,
  phantom_h : PhantomData<H>,


  pointer : ProgramCounter,
  uniques : Supply<String>,
  all : Vec<F>,
}

