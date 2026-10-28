module

public import CFSG.Quasithin.ChapterF.Section06.Elementary.Rigidity
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.LocalCubic
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.SylowNormalizerOuterAction
public import Theory.Frattini.PGroup

/-!
# The cubic local-residual part of Goldschmidt rigidity

A local residual contained in a three-group has order three, by its actual
cubic quotient and coprimeness of its intrinsic two-core. Its automorphism
group has order two, so the Frattini subgroup of the opposite local core
centralizes it. F.6.12 then kills that Frattini subgroup. The same invariant
subgroup theorem kills the two-core of the opposite residual whenever it
is normal in the specified product.

These are precisely the F.6.13 conclusions needed by the contained-residual
branch of F.6.16. They require no recognition of the arbitrary normal-X
case of F.6.13. Source: Aschbacher--Smith, F.6.12--13 and F.6.16,
printed pp.307--309, manuscript of 1 March 2004.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- A three-group local residual has the original cubic order. -/
theorem local_residual_card_three_of_isThreeGroup
    (h : IsGoldschmidtTriple G₁ G₂)
    (hp : IsPGroup 3 ((pResidual 2 G₁).map G₁.subtype)) :
    Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3 := by
  let R := pResidual 2 G₁
  let e := equivMapOfInjective R G₁.subtype G₁.subtype_injective
  have hR : IsPGroup 3 R := hp.of_equiv e.symm
  have hK : pCore 2 R = ⊥ := by
    have hd : Disjoint (⊤ : Subgroup R) (pCore 2 R) :=
      (hR.to_subgroup ⊤).disjoint_of_coprime pCore_isPGroup (by decide)
    exact hd.symm.eq_bot_of_le le_top
  have hc := Noncyclic.local_residual_quotient_card_three h.quotient_left
  change Nat.card (R ⧸ pCore 2 R) = 3 at hc
  rw [hK, Nat.card_congr QuotientGroup.quotientBot.toEquiv] at hc
  exact (Nat.card_congr e.symm.toEquiv).trans hc

/-- F.6.13(3)'s elementary conclusion once the actual local residual is cubic. -/
theorem right_core_elementary_of_left_residual_card_three
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    IsElementaryAbelian 2 ((pCore 2 G₂).map G₂.subtype) := by
  let Q := (pCore 2 G₂).map G₂.subtype
  let L := (pResidual 2 G₁).map G₁.subtype
  let F := (frattini Q).map Q.subtype
  let : Fact (IsPGroup 2 Q) := ⟨pCore_isPGroup.map G₂.subtype⟩
  let : IsCyclic L := isCyclic_of_prime_card hc
  have hn : Q ≤ normalizer (L : Set G) := by
    have hQT : Q ≤ G₁ ⊓ G₂ := by
      simpa only [inf_comm G₂ G₁] using h.symm.local_twoCore_le_intersection
    exact hQT.trans h.intersection_normalizes_left_residual
  have hAut : Nat.card (MulAut L) = 2 := by
    rw [IsCyclic.card_mulAut, hc]
    decide
  have hFc : F ≤ centralizer (L : Set G) := by
    have hd : Nat.card (Theory.GroupTheory.normalizerAction Q L).range ∣ 2 :=
      hAut ▸ card_subgroup_dvd_card _
    have hh := Theory.GroupTheory.normalizerAction_frattini_centralizes Q L hd
    have he : (Q ⊓ normalizer L : Subgroup G) = Q := inf_eq_left.mpr hn
    rw [he] at hh
    exact hh
  have hFn : normalizer (Q : Set G) ≤ normalizer (F : Set G) :=
    normalizer_le_normalizer_characteristic_image Q (frattini Q)
  have hFbot : F = ⊥ := by
    apply h.right_invariant_subgroup_eq_bot hcore (Classical.choice inferInstance) F
      (map_subtype_le _) ?_ ?_
    · exact (map_subtype_le _).trans (h.symm.left_core_normalized.trans hFn)
    · apply (normal_subgroupOf_iff_le_normalizer ((map_subtype_le _).trans le_sup_left)).mpr
      exact sup_le (Q.le_normalizer.trans hFn)
        ((le_centralizer_iff.mpr hFc).trans (Subgroup.centralizer_le_normalizer _))
  apply (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
  apply map_injective Q.subtype_injective
  simpa only [Subgroup.map_bot] using hFbot

/-- The precise contained-three-group hypothesis in the later F.6.16 proof. -/
theorem right_core_elementary_of_left_residual_le_threeGroup
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (X : Subgroup G) (hX : IsPGroup 3 X)
    (hL : (pResidual 2 G₁).map G₁.subtype ≤ X) :
    IsElementaryAbelian 2 ((pCore 2 G₂).map G₂.subtype) :=
  right_core_elementary_of_left_residual_card_three h hcore
    (local_residual_card_three_of_isThreeGroup h (hX.to_le hL))

/-- F.6.13(3)'s intrinsic residual-core clause, using both literal inclusions. -/
theorem right_residual_core_eq_bot_of_normal
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hN : (((pCore 2 (pResidual 2 G₂)).map
      (G₂.subtype.comp (pResidual 2 G₂).subtype)).subgroupOf
        ((pCore 2 G₂).map G₂.subtype ⊔ (pResidual 2 G₁).map G₁.subtype)).Normal) :
    (pCore 2 (pResidual 2 G₂)).map
      (G₂.subtype.comp (pResidual 2 G₂).subtype) = ⊥ := by
  let R := pResidual 2 G₂
  let K := (pCore 2 R).map R.subtype
  have hKQ : K ≤ pCore 2 G₂ := le_sSup ⟨inferInstance, pCore_isPGroup.map R.subtype⟩
  have hKG : G₂ ≤ normalizer (K.map G₂.subtype : Set G) := by
    have hn := K.le_normalizer_map G₂.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn
  have hN' : ((K.map G₂.subtype).subgroupOf
      ((pCore 2 G₂).map G₂.subtype ⊔ (pResidual 2 G₁).map G₁.subtype)).Normal := by
    simpa only [K, R, map_map] using hN
  have hh := h.right_invariant_subgroup_eq_bot hcore
    (Classical.choice inferInstance) (K.map G₂.subtype) (map_mono hKQ)
    ((map_subtype_le _).trans hKG) hN'
  simpa only [K, R, map_map] using hh

end CFSG.Quasithin.ChapterF.SourceAssembly
