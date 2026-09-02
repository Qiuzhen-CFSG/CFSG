import Stellmacher.SectionOne.Defs
#check ConjAct.toConjAct
#check ConjAct.toConjAct_hom
#check ConjAct.toMulAut
#check MulDistribMulAction.ofMul
#check MulDistribMulAction.compHom
#check ConjAct.mulDistribMulAction
#check ConjAct.instMulDistribMulAction
#check MonoidHom.comp
variable {G : Type*} [Group G]
#check (ConjAct.toConjAct G)
#check (ConjAct.toConjAct G).toMonoidHom
#synth MulDistribMulAction (ConjAct G) G
