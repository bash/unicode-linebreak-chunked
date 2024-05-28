use core::iter::FusedIterator;

pub(crate) struct ExhaustOnDrop<I>(pub(crate) I)
where
    I: Iterator;

impl<I> Drop for ExhaustOnDrop<I>
where
    I: Iterator,
{
    fn drop(&mut self) {
        for _ in self.0.by_ref() {}
    }
}

impl<I> Iterator for ExhaustOnDrop<I>
where
    I: Iterator,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl<I> FusedIterator for ExhaustOnDrop<I> where I: FusedIterator {}
