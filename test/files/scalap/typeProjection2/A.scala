trait TypeProjection2[A] {
 trait GroupedIterator[B >: A] {
    def withPadding(x: => B): this.type
 }
 def sliding[B >: A](size: Int, step: Int = 1): GroupedIterator[B]
}