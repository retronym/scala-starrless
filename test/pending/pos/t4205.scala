object t4205 {
  new B[Nothing]().b1

  class B[N[_]] {
    def b1 = b2[N]
    def b2[O[_]] {}
  }
}
