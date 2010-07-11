object AnonymousTypeFunctions {
  def foo[N[_]] = 0
  trait A[X]
  foo[[X](A[X])]
}
