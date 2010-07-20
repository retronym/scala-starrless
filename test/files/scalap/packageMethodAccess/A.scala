package object PackageMethodAccess {
  class MethodAccess {
    protected[this] def foo1 = 1

    private[this] def foo2 = 1

    protected[PackageMethodAccess] def foo3 = 1

    private[PackageMethodAccess] def foo4 = 1

    protected def foo5 = 1

    private def foo6 = 1
  }
}
