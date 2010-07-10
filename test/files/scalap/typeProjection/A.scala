// #3555
object test {
  abstract class A {
    class B1
    type B2
    def b1: A#B1
    def b2: A#B2
  }

  trait C {
    def b1: A#B1
    def b2: A#B2
  }
}