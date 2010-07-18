// #3555
class ClassNestedInObject {
  object A {
    class B
    val b: B = new B

    object C
    val c: C.type = C
  }

}