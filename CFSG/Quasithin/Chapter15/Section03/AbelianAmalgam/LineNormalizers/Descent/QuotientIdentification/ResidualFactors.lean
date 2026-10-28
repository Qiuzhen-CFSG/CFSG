module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.QuotientIdentification.Original
public import Stellmacher.TwoResidualSylowSupplement
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Residual factors in the original line-normalizer quotient

The original product map sends `X_E = O²(C_G(E))` onto the alternating
subgroup in its second `S₃` factor. This follows by transporting residuals
inside `G_E` and calculating `O²(S₃) = A₃` using index two and a Sylow
supplement.

The residual-perfect group `Y_E` maps into the first `A₃`. Its image is
nontrivial: otherwise the marked generator `τ`, which lies in the original
Sylow two-subgroup, would alone map onto the first `S₃`. Since `|A₃| = 3`,
this determines that image as well.

The restricted maps have the intrinsic two-cores as kernels. The first
isomorphism theorem therefore gives both cyclic quotients of order three,
with explicit compatibility with the marked product map. The input consists
of the preceding quotient-identification data; neither residual image nor
cyclic quotient is assumed. Assembly of full Lemma 15.3.67 remains with the
parent development.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 15.3.67(3), printed pp.1153–1154, PDF pp.1170–1171.
-/

public section
open Subgroup Stellmacher BenderSuzuki.External
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification

private theorem alternating_card : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup]
  norm_num

private theorem perm_not_two : ¬ IsPGroup 2 (Equiv.Perm (Fin 3)) := by
  intro h
  have hc := (h.to_subgroup (alternatingGroup (Fin 3))).card_eq_or_dvd
  rw [alternating_card] at hc
  norm_num at hc

private theorem eq_of_le_card_three {G : Type*} [Group G] [Finite G]
    {R A : Subgroup G} (hRA : R ≤ A) (hA : Nat.card A = 3) (hR : R ≠ ⊥) : R = A := by
  let : Fact (Nat.Prime (Nat.card A)) := ⟨by rw [hA]; exact Nat.prime_three⟩
  have hm := map_subgroupOf_eq_of_le hRA
  rcases (R.subgroupOf A).eq_bot_or_eq_top_of_prime_card with hb | ht
  · rw [hb, Subgroup.map_bot] at hm
    exact (hR hm.symm).elim
  · rw [ht, ← MonoidHom.range_eq_map, range_subtype] at hm
    exact hm.symm

private theorem perm_three_twoResidual :
    twoResidualAmbient (⊤ : Subgroup (Equiv.Perm (Fin 3))) = alternatingGroup (Fin 3) := by
  apply eq_of_le_card_three ?_ alternating_card ?_
  · have hn : ((alternatingGroup (Fin 3)).subgroupOf ⊤).Normal :=
      (inferInstance : (alternatingGroup (Fin 3)).Normal).subgroupOf ⊤
    have hi : ((alternatingGroup (Fin 3)).subgroupOf ⊤).index = 2 ^ 1 := by
      change (alternatingGroup (Fin 3)).relIndex ⊤ = _
      rw [relIndex_top_right, alternatingGroup.index_eq_two]
      rfl
    have hle : twoResidualSubgroup (⊤ : Subgroup (Equiv.Perm (Fin 3))) ≤
        (alternatingGroup (Fin 3)).subgroupOf ⊤ := sInf_le ⟨hn, 1, hi⟩
    exact (map_mono hle).trans_eq (map_subgroupOf_eq_of_le le_top)
  · intro hb
    let S : Sylow 2 (Equiv.Perm (Fin 3)) := default
    have ht : (S : Subgroup (Equiv.Perm (Fin 3))) = ⊤ := by
      simpa [hb] using twoResidualAmbient_top_sup_sylow S
    have hp := S.isPGroup'
    rw [ht] at hp
    exact perm_not_two (hp.of_equiv Subgroup.topEquiv)

private theorem map_inr {G K : Type*} [Group G] [Group K] (A : Subgroup K) :
    A.map (MonoidHom.inr G K) = (⊥ : Subgroup G).prod A := by
  ext ⟨a, b⟩
  change (∃ x, x ∈ A ∧ (1, x) = (a, b)) ↔ a = 1 ∧ b ∈ A
  constructor
  · rintro ⟨x, hx, he⟩
    cases he
    exact ⟨rfl, hx⟩
  · rintro ⟨rfl, hb⟩
    exact ⟨b, hb, rfl⟩

private theorem second_factor_twoResidual :
    twoResidualAmbient ((⊥ : Subgroup (Equiv.Perm (Fin 3))).prod ⊤) =
      (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3)) := by
  have h := map_twoResidualAmbient_of_subgroup_image _
    (MonoidHom.inr (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3))) _ (map_inr ⊤)
  rw [perm_three_twoResidual, map_inr] at h
  exact h.symm

private theorem perfect_maps_to_alternating {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 3)) (hG : hktPResidual 2 G = ⊤) (x : G) :
    f x ∈ alternatingGroup (Fin 3) := by
  let q := (QuotientGroup.mk' (alternatingGroup (Fin 3))).comp f
  have hp : IsPGroup 2 (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) := by
    apply IsPGroup.of_card (n := 1)
    rw [← index_eq_card, alternatingGroup.index_eq_two]
    rfl
  have hq : IsPGroup 2 (G ⧸ q.ker) :=
    (hp.to_subgroup q.range).of_equiv (QuotientGroup.quotientKerEquivRange q).symm
  have hk := hktPResidual_le q.ker inferInstance hq
  rw [hG] at hk
  exact (QuotientGroup.eq_one_iff (f x)).mp (hk (mem_top x))

variable {G : Type*} [Group G] [Finite G]
variable {M Y T V E : Subgroup G} [IsMulCommutative V]

/-- The original centralizer residual has exactly the second alternating factor as image. -/
theorem originalProductMap_lineX (s : Inputs M Y T V E) :
    ((lineX E).subgroupOf (lineNormalizer E)).map (originalProductMap s) =
      (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3)) := by
  have hX : lineX E ≤ lineNormalizer E :=
    (lineX_le_centralizer E).trans (centralizer_le_normalizer (E : Set G))
  have hr : (lineX E).subgroupOf (lineNormalizer E) =
      twoResidualAmbient ((centralizer (E : Set G)).subgroupOf (lineNormalizer E)) := by
    apply map_injective (lineNormalizer E).subtype_injective
    rw [map_subgroupOf_eq_of_le hX,
      map_twoResidualAmbient_of_subgroup_image _ (lineNormalizer E).subtype
        (centralizer (E : Set G))
        (map_subgroupOf_eq_of_le (centralizer_le_normalizer (E : Set G)))]
    rfl
  rw [hr, map_twoResidualAmbient_of_subgroup_image _ _ _
    (originalProductMap_second_factor s), second_factor_twoResidual]

/-- The original normalizer residual has exactly the first alternating factor as image. -/
theorem originalProductMap_lineY (s : Inputs M Y T V E) :
    ((lineY Y E).subgroupOf (lineNormalizer E)).map (originalProductMap s) =
      (alternatingGroup (Fin 3)).prod (⊥ : Subgroup (Equiv.Perm (Fin 3))) := by
  let H := lineNormalizer E
  let f := originalProductMap s
  let J := ((lineY Y E).subgroupOf H).map f
  have hY : lineY Y E ≤ H := (lineY_le Y E).trans inf_le_right
  have hZ : zpowers s.marked.tau ≤ H :=
    (zpowers_le.mpr s.marked.tau_mem).trans inf_le_right
  have hfirst : J ≤ (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥ := by
    rw [← originalProductMap_first_factor s]
    exact map_mono (comap_mono le_sup_left)
  apply eq_of_le_card_three ?_ ?_ ?_
  · rintro z ⟨y, hy, rfl⟩
    refine ⟨?_, (hfirst (mem_map_of_mem f hy)).2⟩
    exact perfect_maps_to_alternating
      ((MonoidHom.fst _ _).comp (f.comp (inclusion hY)))
      (twoResidualAmbient_has_top_twoResidual (Y ⊓ H)) ⟨y, hy⟩
  · rw [Nat.card_congr (prodEquiv (alternatingGroup (Fin 3))
      (⊥ : Subgroup (Equiv.Perm (Fin 3)))).toEquiv, Nat.card_prod,
      alternating_card, Subgroup.card_bot]
  · intro hb
    have hgen := originalProductMap_first_factor s
    rw [subgroupOf_sup hY hZ, Subgroup.map_sup, hb, bot_sup_eq] at hgen
    have htwoT : IsPGroup 2 (lineT T E) := by
      rw [← s.sylow_map]
      exact s.sylow.isPGroup'.map H.subtype
    have htwoZ : IsPGroup 2 (zpowers s.marked.tau) :=
      htwoT.to_le (zpowers_le.mpr s.marked.tau_mem)
    have htwo : IsPGroup 2 (((zpowers s.marked.tau).subgroupOf H).map
        (originalProductMap s)) := htwoZ.comap_subtype.map f
    rw [hgen] at htwo
    have he : ((⊤ : Subgroup (Equiv.Perm (Fin 3))).prod
        (⊥ : Subgroup (Equiv.Perm (Fin 3)))) ≃* Equiv.Perm (Fin 3) :=
      ((prodEquiv _ _).trans MulEquiv.prodUnique).trans Subgroup.topEquiv
    exact perm_not_two (htwo.of_equiv he)

private noncomputable def coreEquivMap (s : Inputs M Y T V E)
    (A : Subgroup G) (hA : A ≤ lineNormalizer E)
    (hn : (A.subgroupOf (lineNormalizer E)).Normal) :
    (A ⧸ pCore 2 A) ≃* ((A.subgroupOf (lineNormalizer E)).map (originalProductMap s)) :=
  ((QuotientGroup.quotientMulEquivOfEq (originalProductMap_restrict_ker s A hA hn).symm).trans
    (QuotientGroup.quotientKerEquivRange ((originalProductMap s).comp (inclusion hA)))).trans
      (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, inclusion_range]))

/-- The intrinsic core quotient of `X_E`, identified with its actual marked image. -/
noncomputable def lineXCoreEquivImage (s : Inputs M Y T V E) :
    (lineX E ⧸ pCore 2 (lineX E)) ≃*
      ((⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3))) :=
  (coreEquivMap s (lineX E)
    ((lineX_le_centralizer E).trans (centralizer_le_normalizer (E : Set G)))
    (lineX_normal_in_lineNormalizer E)).trans
      (MulEquiv.subgroupCongr (originalProductMap_lineX s))

/-- The intrinsic core quotient of `Y_E`, identified with its actual marked image. -/
noncomputable def lineYCoreEquivImage (s : Inputs M Y T V E) :
    (lineY Y E ⧸ pCore 2 (lineY Y E)) ≃*
      ((alternatingGroup (Fin 3)).prod (⊥ : Subgroup (Equiv.Perm (Fin 3)))) :=
  (coreEquivMap s (lineY Y E) ((lineY_le Y E).trans inf_le_right) s.Y_normal).trans
    (MulEquiv.subgroupCongr (originalProductMap_lineY s))

/-- The image equivalence on `X_E` is induced by the original product map. -/
theorem lineXCoreEquivImage_mk (s : Inputs M Y T V E) (x : lineX E) :
    (lineXCoreEquivImage s (QuotientGroup.mk' (pCore 2 (lineX E)) x) :
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) =
    originalProductMap s (inclusion
      ((lineX_le_centralizer E).trans (centralizer_le_normalizer (E : Set G))) x) := by
  rfl

/-- The image equivalence on `Y_E` is induced by the original product map. -/
theorem lineYCoreEquivImage_mk (s : Inputs M Y T V E) (y : lineY Y E) :
    (lineYCoreEquivImage s (QuotientGroup.mk' (pCore 2 (lineY Y E)) y) :
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) =
    originalProductMap s (inclusion ((lineY_le Y E).trans inf_le_right) y) := by
  rfl

/-- A fixed identification of the order-three alternating group with the cyclic model. -/
noncomputable def alternatingThreeEquivCyclic :
    alternatingGroup (Fin 3) ≃* Multiplicative (ZMod 3) :=
  mulEquivOfPrimeCardEq alternating_card (by change Nat.card (ZMod 3) = 3; simp)

/-- The original `X_E` modulo its intrinsic two-core is cyclic of order three. -/
noncomputable def lineXCoreEquivCyclic (s : Inputs M Y T V E) :
    (lineX E ⧸ pCore 2 (lineX E)) ≃* Multiplicative (ZMod 3) :=
  (((lineXCoreEquivImage s).trans (prodEquiv _ _)).trans MulEquiv.uniqueProd).trans
    alternatingThreeEquivCyclic

/-- The original `Y_E` modulo its intrinsic two-core is cyclic of order three. -/
noncomputable def lineYCoreEquivCyclic (s : Inputs M Y T V E) :
    (lineY Y E ⧸ pCore 2 (lineY Y E)) ≃* Multiplicative (ZMod 3) :=
  (((lineYCoreEquivImage s).trans (prodEquiv _ _)).trans MulEquiv.prodUnique).trans
    alternatingThreeEquivCyclic

/-- The cyclic coordinates of `X_E` recover its actual second-factor image. -/
theorem lineXCoreEquivCyclic_compatible (s : Inputs M Y T V E) (x : lineX E) :
    originalProductMap s (inclusion
      ((lineX_le_centralizer E).trans (centralizer_le_normalizer (E : Set G))) x) =
      (1, (alternatingThreeEquivCyclic.symm
        (lineXCoreEquivCyclic s (QuotientGroup.mk' (pCore 2 (lineX E)) x)) :
          Equiv.Perm (Fin 3))) := by
  change _ = (1, ((alternatingThreeEquivCyclic.symm
    (alternatingThreeEquivCyclic _)) : Equiv.Perm (Fin 3)))
  rw [MulEquiv.symm_apply_apply, ← lineXCoreEquivImage_mk s x]
  exact Prod.ext (lineXCoreEquivImage s
    (QuotientGroup.mk' (pCore 2 (lineX E)) x)).property.1 rfl

/-- The cyclic coordinates of `Y_E` recover its actual first-factor image. -/
theorem lineYCoreEquivCyclic_compatible (s : Inputs M Y T V E) (y : lineY Y E) :
    originalProductMap s (inclusion ((lineY_le Y E).trans inf_le_right) y) =
      ((alternatingThreeEquivCyclic.symm
        (lineYCoreEquivCyclic s (QuotientGroup.mk' (pCore 2 (lineY Y E)) y)) :
          Equiv.Perm (Fin 3)), 1) := by
  change _ = (((alternatingThreeEquivCyclic.symm
    (alternatingThreeEquivCyclic _)) : Equiv.Perm (Fin 3)), 1)
  rw [MulEquiv.symm_apply_apply, ← lineYCoreEquivImage_mk s y]
  exact Prod.ext rfl (lineYCoreEquivImage s
    (QuotientGroup.mk' (pCore 2 (lineY Y E)) y)).property.2

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification
