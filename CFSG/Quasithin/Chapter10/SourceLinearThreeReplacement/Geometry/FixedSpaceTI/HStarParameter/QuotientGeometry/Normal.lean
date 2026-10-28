module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.NormalOuter
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Cases
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.LinearCovered
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.SymplecticCovered
public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.TwoSylowSource
public import Theory.Alternating.Aut

/-!
# Excluding the normal field-four components

The actual marked Borel has odd index above its two-core in each of the
PSL₂(4), PSL₃(4), and Sp₄(4) rows. The original dihedral overlap quotient
would therefore force eight to divide the component's outer automorphism
order. Actual automorphism calculations bound these orders by divisors of
two, twelve, and four respectively, excluding all three normal rows.

The isomorphisms use the original source image KJ/J, the given field-four
marking, and the full derived symplectic carrier. No generation parameter
is transported through an arbitrary solvable cover. Source:
Aschbacher--Smith E.2.2 and 10.2.3(3), printed pp.215--216,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
open ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels

private theorem alternatingFive_outer_card_dvd_two :
    Nat.card (MulAut.Outer (alternatingGroup (Fin 5))) ∣ 2 := by
  let A := alternatingGroup (Fin 5)
  have hs : Function.Surjective (MulAut.outerAction A) := by
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
    obtain ⟨σ,rfl⟩ :=
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
        (by decide) (by decide)).surjective a
    exact ⟨QuotientGroup.mk' A σ,rfl⟩
  have hd := card_dvd_of_surjective (MulAut.outerAction A) hs
  rw [← A.index_eq_card,alternatingGroup.index_eq_two] at hd
  exact hd

private theorem bender_overlap_odd_index {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) {K : Subgroup X}
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (hm : ExchangedModel (minimalParabolicMax S hP) K 2) :
    Odd (pCore 2 (K.subgroupOf (minimalParabolicMax S hP))).index := by
  let M := minimalParabolicMax S hP
  let N := K.subgroupOf M
  have ha := bender_overlap_core_quotient S hP hc (Or.inl hm)
  let e : N ≃* (M ⊓ K : Subgroup X) :=
    (MulEquiv.subgroupCongr (show N = (M ⊓ K).subgroupOf M from by
      ext x
      exact ⟨fun hx => ⟨x.property,hx⟩,fun hx => hx.2⟩)).trans
      (subgroupOfEquivOfLe inf_le_left)
  let eq := e.toMonoidHom.pCoreQuotientEquiv (p := 2) e.surjective
    (IsPGroup.ker_isPGroup_of_injective e.injective)
  let : IsMulCommutative (N ⧸ pCore 2 N) := by
    refine ⟨⟨fun a b => eq.injective ?_⟩⟩
    simp only [map_mul]
    exact ha.is_comm.comm _ _
  let P : Sylow 2 N := Classical.choice inferInstance
  have he := sylow_eq_core_of_commutative_quotient P
  rw [← he]
  exact Nat.not_even_iff_odd.mp (P.not_dvd_index ∘ even_iff_two_dvd.mp)

/-- None of the normal field-four source rows has the literal dihedral overlap quotient. -/
theorem normal_fieldFour_false {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hs : ¬ Group.IsSolvable X) (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (hM : IsPGroup 6 (minimalParabolicMax S hP))
    (hd : Nonempty (((minimalParabolicMax S hP) ⧸
      (pCore 3 ((minimalParabolicMax S hP) ⧸ pCore 2 (minimalParabolicMax S hP))).comap
        (QuotientGroup.mk' (pCore 2 (minimalParabolicMax S hP)))) ≃* DihedralGroup 4))
    (hm : ExchangedModel (minimalParabolicMax S hP) K 2 ∨
      DiagramModel (minimalParabolicMax S hP) K S 2) : False := by
  rcases hm with hm | hm
  · have hi := bender_overlap_odd_index S hP hc hm
    have he := normal_dihedral_outer_divisor S hP hs K hK hgen hc hM hi hd
    obtain ⟨e⟩ := exchanged_two_component_equiv_alternatingFive hm
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv] at he
    exact (by decide : ¬ (8 : ℕ) ∣ 2) (he.trans alternatingFive_outer_card_dvd_two)
  · rcases hm with hm | hm
    · obtain ⟨F,hF,hfin,hchar,_,hcard,e,hb,_⟩ := hm
      have hi := DiagramHall.linear_coveredBorel_odd_index (by decide : 0 < 2) hcard S hP K hc e hb
      have he := normal_dihedral_outer_divisor S hP hs K hK hgen hc hM hi hd
      let : Fintype F := Fintype.ofFinite F
      let : Fintype (GaloisField 2 2) := Fintype.ofFinite _
      let eF : F ≃+* GaloisField 2 2 := FiniteField.ringEquivOfCardEq (by
        rw [Fintype.card_eq_nat_card,Fintype.card_eq_nat_card,hcard,
          GaloisField.card 2 2 (by decide)])
      let a := e.trans (Atlas.fieldEquivPSL 3 eF)
      rw [Nat.card_congr (MulAut.outerCongr a).toEquiv] at he
      exact (by decide : ¬ (8 : ℕ) ∣ 12)
        (he.trans Matrix.PSL3Four.OuterThreeStructure.outer_card_dvd_twelve)
    · obtain ⟨F,hF,hfin,hchar,_,hcard,e,hb,_⟩ := hm
      have hi := DiagramHall.symplectic_coveredBorel_odd_index S hP hc hcard e hb
      have he := normal_dihedral_outer_divisor S hP hs K hK hgen hc hM hi hd
      let a := e.trans
        (Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two (by omega))
      rw [Nat.card_congr (MulAut.outerCongr a).toEquiv,
        Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.card_outer_eq_two_mul
          hcard (by decide : 1 < 2)] at he
      exact (by decide : ¬ (8 : ℕ) ∣ 2 * 2) he

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
