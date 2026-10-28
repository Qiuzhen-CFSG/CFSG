module
public import Theory.SpecificGroups.GL2.ThreeSylowNormalTower
public import Theory.Frattini.SquareImage
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallProjectiveGraphCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicSylowSeparation

/-!
# The normal projective subgroup and Frattini Sylow separation

The exceptional enlarged quotient contains the actual starred PSU₃(2)
image as a normal subgroup of index two. This marking is retained through
the original reduced endpoint and graph conjugation. A nontrivial elementary
subgroup of a Sylow Frattini subgroup lies in that normal image, since the
quotient has exponent two. Involution separation in PSU₃(2), followed by
injective Sylow restriction, then determines the whole enlarged Sylow.

The distance-three moving-edge consumer combines this with the predecessor
normality tower. This does not assert unrestricted local innerness or exclude
the order-144 enlargement. Source: DGS, *Groups and Graphs* (1985),
5.1(c,d), 6.1, 8.1(g), printed pp.104--105,118--119,133.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open CommutingNontrivial Theory.GroupTheory.AmalgamGraph

/-- A common nontrivial elementary subgroup in one Sylow Frattini subgroup determines the Sylow. -/
theorem small_projective_normal_sylow_eq_of_frattini
    {D : Type*} [Group D] [Finite D] (I : Subgroup D) [I.Normal]
    (hm : ClassicalGroup.IsPSU I 3 2) (hi : I.index ≤ 2)
    (hc : pCore 2 D = ⊥) (R T : Sylow 2 D) (E : Subgroup D)
    [IsElementaryAbelian 2 E] (hne : E ≠ ⊥)
    (hER : E ≤ R) (hET : E ≤ T)
    (hEf : E.subgroupOf (R : Subgroup D) ≤ frattini R) : R = T := by
  have hq : IsPGroup 2 (D ⧸ I) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    change I.index ∣ 2^1
    have hn := I.index_ne_zero_of_finite
    have he : I.index = 1 ∨ I.index = 2 := by omega
    rcases he with he | he <;> simp [he]
  have hIcore : pCore 2 I = ⊥ := by
    rw [pCore_eq_comap_of_normal,hc]
    exact (MonoidHom.ker_eq_bot_iff I.subtype).mpr I.subtype_injective
  have hEI : E ≤ I := by
    let f : R →* D ⧸ I := (QuotientGroup.mk' I).comp (R : Subgroup D).subtype
    have hf : frattini R ≤ f.ker := Theory.GroupTheory.frattini_le_ker_of_square_image f (by
      intro r
      have hn := I.index_ne_zero_of_finite
      have he : I.index = 1 ∨ I.index = 2 := by omega
      have hh := pow_card_eq_one' (x := f r)
      change (f r) ^ I.index = 1 at hh
      rcases he with he | he
      · rw [he,pow_one] at hh
        simp [hh]
      · rwa [he] at hh)
    intro x hx
    exact (QuotientGroup.eq_one_iff _).mp (hf (hEf (show
      (⟨x,hER hx⟩ : R) ∈ E.subgroupOf (R : Subgroup D) from hx)))
  obtain ⟨x,hx,hx1⟩ := (E.bot_or_exists_ne_one).resolve_left hne
  obtain ⟨U,hU⟩ := R.exists_subgroupOf_eq_of_normal I
  obtain ⟨W,hW⟩ := T.exists_subgroupOf_eq_of_normal I
  have hUW : U = W := source_rank_one_sylow_eq_of_common_involution
    (.projective_unitary 1 (by decide) (by simpa using hm)) hIcore U W ⟨x,hEI hx⟩
    (by change (⟨x,hEI hx⟩ : I) ∈ (U : Subgroup I); rw [hU]; exact hER hx)
    (by change (⟨x,hEI hx⟩ : I) ∈ (W : Subgroup I); rw [hW]; exact hET hx)
    (fun hh => hx1 (congrArg Subtype.val hh))
    (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx))
  apply Sylow.eq_of_restriction_of_normal_self_normalizing I hq
    (isPSU_two_sylow_normalizer_eq hm) R T
  have hh := congrArg (fun U : Sylow 2 I => (U : Subgroup I).map I.subtype) hUW
  rwa [hU,hW,subgroupOf_map_subtype,subgroupOf_map_subtype] at hh

/-- The literal starred image has index two in a strict projective enlargement. -/
theorem localEnlargement_projective_normal_index_two
    {G : Type*} [Group G] {P B : Subgroup G} (d : LocalRankOneData P B)
    (hm : ClassicalGroup.IsPSU (d.Pstar ⧸ pCore 2 d.Pstar) 3 2)
    (hD : Nat.card (localEnlargement d ⧸ pCore 2 (localEnlargement d)) = 144) :
    ∃ I : Subgroup (localEnlargement d ⧸ pCore 2 (localEnlargement d)),
      I.Normal ∧ ClassicalGroup.IsPSU I 3 2 ∧ I.index = 2 := by
  obtain ⟨K,hK,hfin,J,hc,hconj,⟨e⟩⟩ := hm
  let := hK
  let := hfin
  let := d.finite_P
  let M := localEnlargement d
  let C := d.Pstar.subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  let I := C.map q
  let : Finite M := Finite.of_injective (inclusion (localEnlargement_le d))
    (inclusion_injective _)
  let : C.Normal := normal_subgroupOf_of_le_normalizer ((localEnlargement_le d).trans
    ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal))
  let : I.Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  let f : C ≃* d.Pstar := subgroupOfEquivOfLe le_sup_left
  let g := (coreQuotientEquivImage 2 C).symm.trans
    ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e)
  have hI : Nat.card I = 72 := (Nat.card_congr g.toEquiv).trans
    (HermitianForm.FixedFieldTwo.card_projective J hc hconj)
  refine ⟨I,inferInstance,⟨K,inferInstance,inferInstance,J,hc,hconj,⟨g⟩⟩,?_⟩
  have hh := I.card_mul_index
  rw [hI,hD] at hh
  omega

namespace Reduction
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S

/-- The original endpoint catalogue retains the normal starred marking in its exceptional row. -/
theorem reduced_enlargement_rankOne_or_projective_index_two (h : HypothesisF11 L S) (i : Fin 2) :
    IsRankOneModel (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) ∨
      (Nat.card (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) = 144 ∧
        ∃ I : Subgroup (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)),
          I.Normal ∧ ClassicalGroup.IsPSU I 3 2 ∧ I.index = 2) := by
  rcases reduced_enlargement_rankOne_or_small_unitary h i with hm | hp | hs
  · exact Or.inl hm
  · rcases original_small_projective_enlarged_marking_or_card h i hp with hm | hc
    · exact Or.inl (.projective_unitary 1 (by decide) (by simpa using hm))
    · refine Or.inr ⟨hc,?_⟩
      obtain ⟨K,hK,hfin,J,hcard,hconj,⟨e⟩⟩ := hp
      have hm : ClassicalGroup.IsPSU
          ((h.starredLocalRankOneData i).Pstar ⧸ pCore 2 (h.starredLocalRankOneData i).Pstar) 3 2 :=
        ⟨K,hK,hfin,J,hcard,hconj,⟨(h.starredQuotientEquiv i).symm.trans e⟩⟩
      exact localEnlargement_projective_normal_index_two (h.starredLocalRankOneData i) hm hc
  · exact Or.inl (.special_unitary 1 (by decide)
      (by simpa using original_small_special_enlarged_marking h i hs))

/-- The actual graph quotient retains the normal PSU₃(2) image and its exact index. -/
theorem reduced_graph_rankOne_or_projective_index_two (h : HypothesisF11 L S) (v : Vertex F) :
    IsRankOneModel (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ∨
      (Nat.card (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) = 144 ∧
        ∃ I : Subgroup (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)),
          I.Normal ∧ ClassicalGroup.IsPSU I 3 2 ∧ I.index = 2) := by
  have hb (j : Bool) :
      IsRankOneModel (family (enlargedEndpoint L S) j ⧸ pCore 2 (family (enlargedEndpoint L S) j)) ∨
        (Nat.card (family (enlargedEndpoint L S) j ⧸ pCore 2 (family (enlargedEndpoint L S) j)) = 144 ∧
          ∃ I : Subgroup (family (enlargedEndpoint L S) j ⧸ pCore 2 (family (enlargedEndpoint L S) j)),
            I.Normal ∧ ClassicalGroup.IsPSU I 3 2 ∧ I.index = 2) := by
    cases j
    · exact reduced_enlargement_rankOne_or_projective_index_two h 0
    · exact reduced_enlargement_rankOne_or_projective_index_two h 1
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  let M := graphLocalGroup F (base F v.type)
  have heq : M.map (MulAut.conj g).toMonoidHom = graphLocalGroup F v :=
    (graphLocalGroup_conjugate (reduced_triple h) g (base F v.type)).symm.trans
      (congrArg (graphLocalGroup F) hg)
  let a : M ≃* graphLocalGroup F v :=
    (M.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr heq)
  let e := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
    (reduced_graphEnlargementQuotient h v.type)
  rcases hb v.type with hm | ⟨hc,I,hI,hmodel,hi⟩
  · exact Or.inl (hm.of_equiv e)
  · let := hI
    let I' := I.map e.symm.toMonoidHom
    let f : I ≃* I' := I.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
    obtain ⟨K,hK,hfin,J,hcard,hconj,⟨a⟩⟩ := hmodel
    refine Or.inr ⟨(Nat.card_congr e.toEquiv).trans hc,I',
      hI.map e.symm.toMonoidHom e.symm.surjective,
      ⟨K,hK,hfin,J,hcard,hconj,⟨f.symm.trans a⟩⟩,?_⟩
    exact (index_map_equiv I e.symm).trans hi

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
