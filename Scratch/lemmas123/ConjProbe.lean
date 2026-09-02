import Stellmacher.SectionOne.Defs
variable {G : Type*} [Group G] (A : Subgroup G)
example : MulDistribMulAction A G := by
  let φ : A →* ConjAct G := ConjAct.toConjAct.toMonoidHom.comp A.subtype
  exact MulDistribMulAction.compHom G φ

example (a : A) (g : G) : (a • g) = (a:G) * g * (a:G)⁻¹ := by
  let φ : A →* ConjAct G := ConjAct.toConjAct.toMonoidHom.comp A.subtype
  letI : MulDistribMulAction A G := MulDistribMulAction.compHom G φ
  rfl
