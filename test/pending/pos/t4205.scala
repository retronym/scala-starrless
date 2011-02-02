object t4205 {
  trait A[M[_]] {
    null.asInstanceOf[B[M]].b1("")
  }

  trait B[N[_]] {
    def b1[A](a: A) = b2[N]
    def b2[O[_]] = ()
  }
}
