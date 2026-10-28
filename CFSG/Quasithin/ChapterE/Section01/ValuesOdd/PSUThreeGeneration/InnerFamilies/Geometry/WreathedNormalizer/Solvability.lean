module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.WreathedNormalizer.Base
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.FactorPosition.TorusAction.MatrixReduction
public import Theory.Representation.RankThreeDeterminantCentralizer
public import Theory.SpecificGroups.SymmetricFourSolvable
public import ABG.ChapterII.Section1.WreathedFusionFrame
public import ABG.ChapterII.Section1.WreathedUFrattiniAction

/-!
# Solvability of the intrinsic wreathed base normalizer

The abelian Sylow base is noncyclic because its Frattini quotient is a four-group.
Lift it through the actual odd scalar kernel of SU₃ to PSU₃. The existing
faithful determinant-one matrix calculation gives three distinct character
lines and hence an abelian centralizer. The normalizer action on the base is
faithful on its four-element Frattini quotient. Its image is therefore solvable,
and the abelian centralizer kernel makes the entire intrinsic normalizer solvable.

All matrix premises are discharged, with the field of order p² and the actual
projective quotient retained, including p=3. No centralizer-structure result
from the surrounding Chapter E campaign is used.
Source: the matrix calculation in Aschbacher--Smith A.3.21(c), printed pp.55--56,
and the wreathed base action in ABG II.1 Proposition 2.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.WreathedNormalizer
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition

private theorem kleinFour_aut_solvable (Q : Type*) [Group Q] [Finite Q] [IsKleinFour Q] :
    Group.IsSolvable (MulAut Q) := by
  classical
  let e : Q ↪ Fin 4 := (Finite.equivFinOfCardEq (IsKleinFour.card_four (G := Q))).toEmbedding
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm Q) := Group.isSolvable_of_isSolvable_injective
    (Equiv.Perm.viaEmbeddingHom_injective e)
  let f : MulAut Q →* Equiv.Perm Q :=
    { toFun := fun a => a.toEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact Group.isSolvable_of_isSolvable_injective (f := f)
    (fun a b h => MulEquiv.ext (fun x => Equiv.congr_fun h x))

/-- The base normalizer is an extension of its abelian matrix centralizer
by a faithful group of automorphisms of the Klein four Frattini quotient. -/
theorem presentation_normalizer_isSolvable {K : Type*} [Group K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hmodel : ClassicalGroup.IsPSU K 3 p)
    (S : Sylow 2 K) {n : ℕ} (P : ABG.Wreathed.Presentation S n) :
    Group.IsSolvable (normalizer (P.U.map (S : Subgroup K).subtype : Set K)) := by
  let : Fact p.Prime := ⟨hp⟩
  let U := P.U.map (S : Subgroup K).subtype
  have hf := P.fusionFrame S
  obtain ⟨hfour, hfaith⟩ := ABG.Wreathed.u_frattini_action S n _ _ hf
  let := hfour
  let : IsMulCommutative U := hf.2.2.1
  have hn : ¬ IsCyclic U := by
    intro hc
    let := hc
    exact IsKleinFour.not_isCyclic (G := U ⧸ frattini U) inferInstance
  have hU : IsPGroup 2 U := (S.isPGroup'.to_subgroup P.U).map (S : Subgroup K).subtype
  obtain ⟨hC, _⟩ := isPSU_centralizer_bound_of_matrix_centralizers (p := 2) (q := p)
    (by decide) (fun he => hodd.not_two_dvd_nat (he ▸ dvd_rfl)) hmodel U hU hn
    (fun F _ _ R hcomm horder hnR hdet => by
      let := hcomm
      exact Representation.rankThreeDeterminantCentralizer R horder hnR hdet)
  let : IsMulCommutative (centralizer (U : Set K)) := hC
  let : Group.IsSolvable (MulAut (U ⧸ frattini U)) := kleinFour_aut_solvable _
  let : Group.IsSolvable U.normalizerMonoidHom.range :=
    Group.isSolvable_of_isSolvable_injective hfaith
  let f := U.normalizerMonoidHom.rangeRestrict
  have hk : f.ker = (centralizer (U : Set K)).subgroupOf (normalizer (U : Set K)) := by
    rw [MonoidHom.ker_rangeRestrict, U.normalizerMonoidHom_ker]
  let : Group.IsSolvable f.ker := by
    rw [hk]
    let : IsMulCommutative ((centralizer (U : Set K)).subgroupOf (normalizer (U : Set K))) :=
      subgroupOf_isMulCommutative _ _
    exact Group.isSolvable_of_comm (fun a b => mul_comm a b)
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [range_subtype])

/-- The intrinsic normalizer-solvability contract for every specified Sylow
of PSU₃(p), including characteristic three and arbitrary Hermitian forms. -/
theorem intrinsicSolvability_of_isPSU {K : Type*} [Group K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hmod : p % 4 = 3)
    (hmodel : ClassicalGroup.IsPSU K 3 p) : IntrinsicSolvability K := by
  intro S A ha hi
  obtain ⟨n, hn⟩ := isPSU_sylow_wreathed hp hodd hmod hmodel S
  obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation hn
  have he : A = P.U := P.abelian_eq_U_of_card_eq A ha (by
    have hA := A.card_mul_index
    have hU := P.U.card_mul_index
    rw [hi] at hA
    rw [P.index_U] at hU
    omega)
  rw [he]
  exact presentation_normalizer_isSolvable hp hodd hmodel S P
end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.WreathedNormalizer
