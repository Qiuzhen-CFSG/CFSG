module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.Completion
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.RadicalModels
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Factors.Orbit
public import Theory.GroupTheory.CComponent.AbelianSylowPair
public import Theory.SpecificGroups.PSL2.SmallSourceAbelianSylows
public import Theory.Mathieu.M22.TripleCover.AbelianSylowObstruction

/-!
# Excluding the actual triple-Mathieu section of Kc

The literal 15.2.12(2) alternatives make Kc solvable or give it abelian
Sylow three-subgroups. For the invariant component, use its actual PSL₄(2)
or PSL₅(2) quotient. For the pair, retain the two conjugate relative
C-components, their genuine rank-one quotient models and their join Kc;
the proved two-group radical lets the direct-product argument lift.

A section of a solvable group is solvable. A section of a group with
abelian Sylow three-subgroups has abelian Sylow three-subgroups. The
genuine triple Mathieu cover is perfect with a central subgroup of order
three, so central transfer excludes the second alternative as well.
This closes the final J₄ section obstruction without replacing O² by O₂.

The StructuralAlternatives premise retains its plane-geometry producer
and final discharge by qt-e-152-chosen-action-contradiction.
Source: Aschbacher--Smith 15.2.12(2) and final proof of 15.2.15, pp.1111,1118.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
open ChapterD ChapterD.UniqueFactor PlaneUniquenessPreceding
variable {G : Type*} [Group G] [Finite G]

private theorem three_coprime_card_of_twoGroup {A : Type*} [Group A] [Finite A]
    (h : IsPGroup 2 A) : Nat.Coprime 3 (Nat.card A) := by
  obtain ⟨n,hn⟩ := h.exists_card_eq
  rw [hn]
  exact (by decide : Nat.Coprime 3 2).pow_right n

private theorem abelian_three_of_core_model (L : Subgroup G)
    (hm : (∃ n : ℕ, Even n ∧ ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)) ∨
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p) :
    HasAbelianSylow 3 L := by
  have hq : HasAbelianSylow 3 (L ⧸ pCore 2 L) := by
    rcases hm with ⟨n,_,F,_,_,hF,⟨e⟩⟩ | ⟨p,hp,_,F,_,_,hF,⟨e⟩⟩
    · exact (Matrix.ProjectiveSpecialLinearGroup.abelianSylow_three_even_rank_two hF).of_injective
        e.toMonoidHom e.injective
    · exact (Matrix.ProjectiveSpecialLinearGroup.abelianSylow_three_prime_rank_two hp hF).of_injective
        e.toMonoidHom e.injective
  apply hq.of_coprime_kernel (QuotientGroup.mk' (pCore 2 L))
  rw [QuotientGroup.ker_mk']
  exact three_coprime_card_of_twoGroup pCore_isPGroup

variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The exact 15.2.12 alternatives yield a solvable Kc or abelian Sylow three-subgroups. -/
theorem partner_solvable_or_abelianSylow
    (hc : ChosenGeometry.StructuralAlternatives T H Mc) :
    Group.IsSolvable (smallActionKc H Mc) ∨ HasAbelianSylow 3 (smallActionKc H Mc) := by
  have hc0 := hc
  rcases hc with he | ⟨_,hcomp,n,hn,hm,_⟩ | ⟨L,t,_,hcomp,ht,htn,he,_,hm⟩
  · left
    change smallActionKc H Mc = smallActionK H at he
    rw [he]
    let := source_H_solvable d
    exact Group.isSolvable_of_surjective
      (f := H.subtype.subgroupMap (pResidual 2 H)) (H.subtype.subgroupMap_surjective _)
  · right
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    change (smallActionKc H Mc ⧸ pCore 2 (smallActionKc H Mc)) ≃* _ at e
    have hq := (Matrix.ProjectiveSpecialLinearGroup.abelianSylow_three_binary_small_rank hn hF).of_injective
      e.toMonoidHom e.injective
    apply hq.of_coprime_kernel (QuotientGroup.mk' (pCore 2 (smallActionKc H Mc)))
    rw [QuotientGroup.ker_mk']
    exact three_coprime_card_of_twoGroup pCore_isPGroup
  · by_cases heK : smallActionKc H Mc = smallActionK H
    · left
      rw [heK]
      let := source_H_solvable d
      exact Group.isSolvable_of_surjective
        (f := H.subtype.subgroupMap (pResidual 2 H)) (H.subtype.subgroupMap_surjective _)
    right
    have hr := (LinearThree.partner_radical_alternative d hc0).resolve_left heK
    let U := smallActionKc H Mc
    let A := L.subgroupOf U
    let B := (L.conjBy t).subgroupOf U
    change U = L ⊔ L.conjBy t at he
    have hLU : L ≤ U := he ▸ le_sup_left
    have hBU : L.conjBy t ≤ U := he ▸ le_sup_right
    have hUM : U ≤ Mc := by
      rw [show U = (primeToResidual 3 Mc).map Mc.subtype from d.orbit_residual]
      exact map_subtype_le _
    have htM : t ∈ Mc :=
      (d.geometry.outside.1.1.2.trans d.geometry.in_partner) ht
    have hbc := Chapter1.XiEmbedding.SwappedFactorsProof.conjugate_component hcomp htM
    have hA : A.IsCComponent := hcomp.2.subgroupOf_of_le hLU hUM
    have hB : B.IsCComponent := hbc.2.subgroupOf_of_le hBU hUM
    have hne : A ≠ B := by
      intro h
      have hh := congrArg (map U.subtype) h
      rw [map_subgroupOf_eq_of_le hLU,map_subgroupOf_eq_of_le hBU] at hh
      exact htn (mem_normalizer_iff_map_conj_eq.mpr hh.symm)
    have hgen : A ⊔ B = ⊤ := by
      rw [← subgroupOf_sup hLU hBU,←he,subgroupOf_self]
    have hl : HasAbelianSylow 3 L := abelian_three_of_core_model L hm
    let ea := subgroupOfEquivOfLe hLU
    let eb := (subgroupOfEquivOfLe hBU).trans ((MulAut.conj t).subgroupMap L).symm
    exact HasAbelianSylow.of_cComponent_pair hA hB hne hgen
      (three_coprime_card_of_twoGroup hr)
      (hl.of_injective ea.toMonoidHom ea.injective)
      (hl.of_injective eb.toMonoidHom eb.injective)

/-- The literal triple-Mathieu section is incompatible with every original Kc alternative. -/
theorem no_mathieu_section_in_partner
    (hc : ChosenGeometry.StructuralAlternatives T H Mc)
    (R : Subgroup G) (hR : R ≤ smallActionKc H Mc)
    (e : (R ⧸ pCore 2 R) ≃* M22TripleCover) : False := by
  rcases partner_solvable_or_abelianSylow d hc with hs | ha
  · let := hs
    let : Group.IsSolvable R := Group.isSolvable_of_isSolvable_injective
      (f := inclusion hR) (inclusion_injective hR)
    let : Group.IsSolvable M22TripleCover := Group.isSolvable_of_surjective
      (f := e.toMonoidHom) e.surjective
    let : IsSimpleGroup (M22TripleCover ⧸ center M22TripleCover) := IsQuasisimple.simple
    let : Nontrivial M22TripleCover := (QuotientGroup.mk'_surjective (center M22TripleCover)).nontrivial
    exact Group.IsPerfect.not_isSolvable M22TripleCover inferInstance
  · have hr := ha.of_injective (inclusion hR) (inclusion_injective hR)
    exact M22TripleCover.not_hasAbelianSylow_three
      ((hr.of_surjective (QuotientGroup.mk' (pCore 2 R)) (QuotientGroup.mk'_surjective _)).of_surjective
        e.toMonoidHom e.surjective)
end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
