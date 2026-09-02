import Stellmacher.SectionOne.Defs
variable {G : Type*} [Group G]
#synth MulDistribMulAction G G
#synth MulAction G G
#check MulDistribMulAction.toMulAut
#check MulDistribMulAction.compHom
#check MulDistribMulAction.ofMul
#check MulDistribMulAction.ofLeft
#check ConjAct
