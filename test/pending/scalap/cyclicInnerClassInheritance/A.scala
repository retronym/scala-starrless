class CyclicInnerClassInheritance extends CyclicInnerClassInheritanceBase {
  class Inner extends super.Inner
}
class CyclicInnerClassInheritanceBase {
  class Inner
}
