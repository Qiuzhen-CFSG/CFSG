module
public import Theory.GroupTheory.SylowRestrictionInjective
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallProjectiveUnitarySections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallSpecialUnitaryEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EnlargementCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.SylowSeparation

/-!
# Elementary intersections of the intrinsic quotient Sylows

The normal starred PSU₃(2) image has index at most two in its actual
enlargement. Its Sylows are self-normalizing and a nontrivial involution
determines its Sylow. The Sylow restriction theorem therefore bounds an
elementary subgroup common to two distinct enlarged quotient Sylows by two.
All other source rows have the usual involution separation property.

The original F.1.1 application and graph conjugation retain the same
full-Borel enlargement and actual two-core quotient. No enlarged model
is assumed in the possible order-144 case. `IntrinsicMovingGeneration`
uses this estimate on the literal terminal actor V_beta, removing the
terminal model premise whenever its quotient image has order above two.
The order-two case and unrestricted 6.1 enlargement remain separate.
Source: DGS, Groups and Graphs (1985), 5.1(c,d), 6.1 and 8.1(g),
pp.104--105,118--119,133.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open CommutingNontrivial
variable {G : Type*} [Group G] {P B : Subgroup G}

private theorem small_projective_normal_sylow_separation
    {D : Type*} [Group D] [Finite D] (I : Subgroup D) [I.Normal]
    (hm : ClassicalGroup.IsPSU I 3 2) (hi : I.index ≤ 2)
    (hc : pCore 2 D = ⊥) (R T : Sylow 2 D) (A : Subgroup D)
    [IsElementaryAbelian 2 A] (hAR : A ≤ R) (hAT : A ≤ T) :
    R = T ∨ Nat.card A ≤ 2 := by
  have hq : IsPGroup 2 (D ⧸ I) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    change I.index ∣ 2^1
    have hn := I.index_ne_zero_of_finite
    have he : I.index = 1 ∨ I.index = 2 := by omega
    rcases he with he | he <;> simp [he]
  have hIcore : pCore 2 I = ⊥ := by
    rw [pCore_eq_comap_of_normal,hc]
    exact (MonoidHom.ker_eq_bot_iff I.subtype).mpr I.subtype_injective
  rcases Sylow.eq_or_card_le_index_of_normal_self_normalizing I hq
      (isPSU_two_sylow_normalizer_eq hm)
      (source_rank_one_sylow_eq_of_common_involution
        (.projective_unitary 1 (by decide) (by simpa using hm)) hIcore)
      R T A hAR hAT with he | he
  · exact Or.inl he
  · exact Or.inr (he.trans hi)

/-- A common elementary subgroup of distinct small-projective quotient Sylows has order at most two. -/
theorem localEnlargement_small_projective_sylow_separation
    (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hm : ClassicalGroup.IsPSU (d.Pstar ⧸ pCore 2 d.Pstar) 3 2)
    (R T : Sylow 2 (localEnlargement d ⧸ pCore 2 (localEnlargement d)))
    (A : Subgroup (localEnlargement d ⧸ pCore 2 (localEnlargement d)))
    [IsElementaryAbelian 2 A] (hAR : A ≤ R) (hAT : A ≤ T) :
    R = T ∨ Nat.card A ≤ 2 := by
  obtain ⟨F,hF,hfin,J,hc,hconj,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  let M := localEnlargement d
  let D := M ⧸ pCore 2 M
  let C := d.Pstar.subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  let I := C.map q
  let := d.finite_P
  let : Finite M := Finite.of_injective (inclusion (localEnlargement_le d)) (inclusion_injective _)
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  let : C.Normal := normal_subgroupOf_of_le_normalizer ((localEnlargement_le d).trans
    ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal))
  let : I.Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  let f : C ≃* d.Pstar := subgroupOfEquivOfLe (show d.Pstar ≤ M from le_sup_left)
  let g := (coreQuotientEquivImage 2 C).symm.trans
    ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e)
  have hI : Nat.card I = 72 := (Nat.card_congr g.toEquiv).trans
    (BenderSuzuki.MatrixGroups.HermitianForm.FixedFieldTwo.card_projective J hc hconj)
  have hD : Nat.card D ≤ 144 := by
    rcases localEnlargement_small_projective_alternatives d hB J hc hconj e with he | he
    · let f := MulEquiv.subgroupCongr he
      have hh := Nat.card_congr ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e).toEquiv
      rw [BenderSuzuki.MatrixGroups.HermitianForm.FixedFieldTwo.card_projective J hc hconj] at hh
      exact hh.le.trans (by decide)
    · exact he.le
  apply small_projective_normal_sylow_separation I
    ⟨F,inferInstance,inferInstance,J,hc,hconj,⟨g⟩⟩ ?_ (pCore_quotient_pCore_eq_bot 2) R T A hAR hAT
  have hh := I.card_mul_index
  rw [hI] at hh
  nlinarith

private theorem rankOne_sylow_separation
    {D : Type*} [Group D] [Finite D] (hm : IsRankOneModel D)
    (hc : pCore 2 D = ⊥) (R T : Sylow 2 D) (A : Subgroup D)
    [IsElementaryAbelian 2 A] (hAR : A ≤ R) (hAT : A ≤ T) :
    R = T ∨ Nat.card A ≤ 2 := by
  rcases A.bot_or_exists_ne_one with he | ⟨x,hx,hx1⟩
  · right; rw [he,card_bot]; decide
  · exact Or.inl (source_rank_one_sylow_eq_of_common_involution hm hc R T x
      (hAR hx) (hAT hx) hx1 (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx))

/-- Uniform elementary intersection bound for every original rank-one enlargement. -/
theorem localEnlargement_quotient_sylow_separation
    (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (R T : Sylow 2 (localEnlargement d ⧸ pCore 2 (localEnlargement d)))
    (A : Subgroup (localEnlargement d ⧸ pCore 2 (localEnlargement d)))
    [IsElementaryAbelian 2 A] (hAR : A ≤ R) (hAT : A ≤ T) :
    R = T ∨ Nat.card A ≤ 2 := by
  let := d.finite_P
  let : Finite (localEnlargement d) := Finite.of_injective
    (inclusion (localEnlargement_le d)) (inclusion_injective _)
  rcases localEnlargement_rankOne_or_small_unitary d hB with hm | hp | hs
  · exact rankOne_sylow_separation hm (pCore_quotient_pCore_eq_bot 2) R T A hAR hAT
  · exact localEnlargement_small_projective_sylow_separation d hB hp R T A hAR hAT
  · obtain ⟨F,hF,hfin,J,hc,hconj,⟨f⟩⟩ := hs
    let := hF
    let := hfin
    have he := localEnlargement_eq_star_of_small_special d hB J hc hconj f
    let e := MulEquiv.subgroupCongr he
    have hm := d.quotient.of_equiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
    exact rankOne_sylow_separation hm (pCore_quotient_pCore_eq_bot 2) R T A hAR hAT

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The full original Borel enlargement satisfies the same bound on its literal quotient. -/
theorem original_enlarged_quotient_sylow_separation (h : HypothesisF11 L S) (i : Fin 2)
    (R T : Sylow 2 (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)))
    (A : Subgroup (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)))
    [IsElementaryAbelian 2 A] (hAR : A ≤ R) (hAT : A ≤ T) :
    R = T ∨ Nat.card A ≤ 2 := by
  let hh := SuzukiContainment.reduced_hypothesis h
  have hB : ∃ T : Sylow 2 (commonBorel L (SuzukiContainment.reducedSylow L S)),
      (T : Subgroup _) = pCore 2 (commonBorel L (SuzukiContainment.reducedSylow L S)) := by
    apply f11_borel_core_sylow hh
    exact (normal_subgroupOf_iff_le_normalizer
      (show SuzukiContainment.reducedSylow L S ≤ commonBorel L (SuzukiContainment.reducedSylow L S)
        from le_sup_right)).mp (SuzukiContainment.reduced_sylow_normal h)
  have hs := localEnlargement_quotient_sylow_separation (hh.starredLocalRankOneData i) hB
  rw [reduced_localEnlargement_eq h i] at hs
  exact hs R T A hAR hAT

private theorem marked_enlarged_sylow_separation (h : HypothesisF11 L S) (i : Fin 2)
    {D : Type*} [Group D] [Finite D]
    (e : D ≃* (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)))
    (R T : Sylow 2 D) (A : Subgroup D) [IsElementaryAbelian 2 A]
    (hAR : A ≤ R) (hAT : A ≤ T) : R = T ∨ Nat.card A ≤ 2 := by
  let R' := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let : IsElementaryAbelian 2 (A.map e.toMonoidHom) := IsElementaryAbelian.map e.toMonoidHom
  rcases original_enlarged_quotient_sylow_separation h i R' T' (A.map e.toMonoidHom)
      (map_mono hAR) (map_mono hAT) with he | he
  · left
    have hh : (R : Subgroup D).map e.toMonoidHom = (T : Subgroup D).map e.toMonoidHom :=
      congrArg Sylow.toSubgroup he
    exact Sylow.ext ((Subgroup.map_injective e.injective) hh)
  · right
    rwa [card_map_of_injective e.injective] at he

open Subgroup.CosetGeometry.RankTwo in
/-- Conjugation transports the bound to the actual two-core quotient at every graph vertex. -/
theorem reduced_graph_quotient_sylow_separation (h : HypothesisF11 L S)
    (v : Vertex (reducedFamily L S))
    (R T : Sylow 2 (graphLocalGroup (reducedFamily L S) v ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) v)))
    (A : Subgroup (graphLocalGroup (reducedFamily L S) v ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) v)))
    [IsElementaryAbelian 2 A] (hAR : A ≤ R) (hAT : A ≤ T) :
    R = T ∨ Nat.card A ≤ 2 := by
  let : ∀ j, Finite ((reducedFamily L S) j) := finite_endpoints (reduced_triple h)
  let : Finite (graphLocalGroup (reducedFamily L S) v) := Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let F := reducedFamily L S
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
  let i : Fin 2 := if v.type then 1 else 0
  have hj : family (enlargedEndpoint L S) v.type = enlargedEndpoint L S i := by
    dsimp only [i]
    cases v.type <;> rfl
  let b := MulEquiv.subgroupCongr hj
  exact marked_enlarged_sylow_separation h i
    (e.trans (QuotientGroup.congr _ _ b (pCore_map_iso 2 b))) R T A hAR hAT

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
