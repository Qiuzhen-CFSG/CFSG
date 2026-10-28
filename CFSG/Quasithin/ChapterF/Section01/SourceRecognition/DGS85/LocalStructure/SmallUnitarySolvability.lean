module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EnlargementCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceLocalResidual
public import Theory.SpecificGroups.SU3.FixedFieldTwo
public import Theory.SpecificGroups.SU3.PrimeCentralKernel

/-!
# Solvability of the degree-one unitary rows

The fixed-field-two projective unitary carrier has order `72`, hence is
solvable by the proved two-prime theorem.  The special unitary carrier maps
onto it; its kernel embeds in the scalar kernel and is cyclic of order
 dividing three.  Thus both literal degree-one rows are solvable.  Transport
through the source local quotient equivalence makes a degree-one unitary
alternative incompatible with a nonsolvable F.1.1 parabolic.

This closes the small-unitary premise needed by the exhaustive DGS endpoint
catalogue while retaining the original quotient and parabolic interfaces.
Source: DGS85, 6.1 and 6.5, pp.118--122; the order-72 and scalar-kernel
calculations are the concrete SU₃ model facts in `FixedFieldTwo` and
`PrimeCentralKernel`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source

/-- The genuine projective unitary group over the field of order four is
solvable, transported through any literal model equivalence. -/
theorem projective_unitary_two_isSolvable
    {H : Type*} [Group H]
    (hm : ClassicalGroup.IsPSU H 3 2) : Group.IsSolvable H := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hm
  let : Group.IsSolvable (ProjectiveSpecialUnitaryMatrixGroup J) :=
    HermitianForm.FixedFieldTwo.projective_isSolvable J hcard hconj
  exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- The special unitary degree-one cover is solvable: its kernel in the
projective quotient is cyclic of prime-divisor order at most three. -/
theorem special_unitary_two_isSolvable
    {H : Type*} [Group H]
    (hm : IsSU H 3 2) : Group.IsSolvable H := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hm
  let f : H →* ProjectiveSpecialUnitaryMatrixGroup J :=
    J.specialToProjective.comp e.toMonoidHom
  have hf : Function.Surjective f :=
    J.specialToProjective_surjective.comp e.surjective
  have hker_card : Nat.card f.ker ∣ 3 := by
    let i : f.ker →* J.specialToProjective.ker :=
      (e.toMonoidHom.comp f.ker.subtype).codRestrict _ (fun x => x.property)
    have hi : Function.Injective i := fun x y hh =>
      Subtype.ext (e.injective (congrArg Subtype.val hh))
    exact (card_dvd_of_injective i hi).trans J.card_specialToProjective_ker_dvd_three
  let : IsCyclic f.ker := isCyclic_of_card_dvd_prime (p := 3) hker_card
  let : CommGroup f.ker := IsCyclic.commGroup
  let : Group.IsSolvable f.ker := inferInstance
  let : Group.IsSolvable (ProjectiveSpecialUnitaryMatrixGroup J) :=
    HermitianForm.FixedFieldTwo.projective_isSolvable J hcard hconj
  apply Group.isSolvable_of_ker_le_range f.ker.subtype f
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

/-- A degree-one projective unitary local quotient makes its source parabolic
solvable, using the literal F.1.1 quotient criterion. -/
theorem parabolic_solvable_of_projective_unitary_two
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2) :
    Group.IsSolvable (parabolic L S i) := by
  let : Group.IsSolvable (L i ⧸ pCore 2 (L i)) := projective_unitary_two_isSolvable hm
  exact (h.parabolic_solvable_iff_local_quotient i).mpr inferInstance

/-- A degree-one special unitary local quotient likewise makes its source
parabolic solvable. -/
theorem parabolic_solvable_of_special_unitary_two
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (i : Fin 2)
    (hm : IsSU (L i ⧸ pCore 2 (L i)) 3 2) :
    Group.IsSolvable (parabolic L S i) := by
  let : Group.IsSolvable (L i ⧸ pCore 2 (L i)) := special_unitary_two_isSolvable hm
  exact (h.parabolic_solvable_iff_local_quotient i).mpr inferInstance

namespace Reduction
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Nonsolvable source parabolics exclude both retained degree-one unitary
alternatives in the exhaustive endpoint split. -/
theorem no_small_unitary_of_nonsolvable_parabolics
    (h : HypothesisF11 L S)
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L S i)) :
    ∀ i : Fin 2,
      ¬ ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2 ∧
      ¬ IsSU (L i ⧸ pCore 2 (L i)) 3 2 := by
  intro i
  constructor
  · intro hm
    exact hns i (parabolic_solvable_of_projective_unitary_two h i hm)
  · intro hm
    exact hns i (parabolic_solvable_of_special_unitary_two h i hm)

/-- Actual catalogue consumer: once the two source parabolics are known
nonsolvable, every reduced graph vertex has a genuine rank-one actor model. -/
theorem reduced_actor_models_of_nonsolvable_parabolics
    (h : HypothesisF11 L S)
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L S i))
    (v : Vertex (reducedFamily L S)) :
    IsRankOneModel (graphLocalGroup (reducedFamily L S) v ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) v)) :=
  reduced_actor_models_of_no_small_unitary h
    (no_small_unitary_of_nonsolvable_parabolics h hns) v

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
