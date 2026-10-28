module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.InvariantProjection
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Local control of the Borel in 15.3.49(k)

A normal subgroup meeting the two-perfect Y₀ in an element of order three
contains Y₀, because Y₀/O₂(Y₀) has order three. Under noncontainment, theta
control therefore removes the prime three from the supplement intersection.
Its order has no other odd prime, so Sylow maximality identifies the
intersection as T ∩ L₀ and proves its invariance. The relative Sylow normalizer
is then invariant too. If it is solvable, universal (j) places it in M ∩ H;
theta control makes it a 3′-group and N_G(Y₀) = M makes it act on Y₀.

L₀ remains the literal T-conjugate span of L. Normality is only relative to H.
No identification of L with L₀, or of Y₀* with a group of order three, is used.
The model identification and solvability of the Borel remain explicit inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1144.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner
variable {G : Type*} [Group G] [Finite G]

private lemma normal_intersection_three_free (Y L : Subgroup G) [L.Normal]
    (hY : IsPPerfect 2 Y) (hcard : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hout : ¬ Y ≤ L) : ¬ 3 ∣ Nat.card (Y ⊓ L : Subgroup G) := by
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (Y ⊓ L : Subgroup G)) 3 hd
  apply hout
  let _ : (L.map (MonoidHom.id G)).Normal := by simpa only [Subgroup.map_id] using ‹L.Normal›
  apply pPerfect_le_of_cubic_image_intersection (MonoidHom.id G)
    (IsPGroup.ker_isPGroup_of_injective Function.injective_id) Y L hY hcard
  simpa only [Subgroup.map_id] using
    (show ∃ z ∈ Y ⊓ L, orderOf z = 3 from
      ⟨x, x.property, (Subgroup.orderOf_coe x).trans hx⟩)

private lemma theta_control_three_free (M Y L B : Subgroup G) [L.Normal]
    (hθ : theta M = Y) (hcard : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hout : ¬ Y ≤ L) (hBM : B ≤ M) (hBL : B ≤ L) : ¬ 3 ∣ Nat.card B := by
  intro hd
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 hd
  have hb3 : orderOf (b : G) = 3 := (Subgroup.orderOf_coe b).trans hb
  have hbY : (b : G) ∈ Y := hθ ▸ subset_closure ⟨hBM b.property, hb3⟩
  apply normal_intersection_three_free Y L
    (hθ ▸ ComponentIntersection.theta_isPPerfect M) hcard hout
  have hd' := orderOf_dvd_natCard (⟨b, hbY, hBL b.property⟩ : (Y ⊓ L : Subgroup G))
  rwa [← Subgroup.orderOf_coe, hb3] at hd'

private lemma two_group_of_three_free_in_join (Y T K : Subgroup G)
    (hTY : T ≤ normalizer (Y : Set G)) (hT : IsPGroup 2 T)
    (hcard : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hKS : K ≤ Y ⊔ T) (hK : ¬ 3 ∣ Nat.card K) : IsPGroup 2 K := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := Y))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hT
  have hYcard : Nat.card Y = 3 * 2 ^ n := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 Y), hcard, hn]
  have hdiv : Nat.card K ∣ 3 * 2 ^ (n + m) := by
    have hj : Nat.card (Y ⊔ T : Subgroup G) ∣ Nat.card Y * Nat.card T := by
      rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes Y T hTY]
      exact dvd_mul_left _ _
    have hh := (card_dvd_of_le hKS).trans hj
    simpa only [hYcard, hm, pow_add, mul_assoc] using hh
  apply IsPGroup.of_card_dvd_pow (n := n + m)
  exact ((Nat.prime_three.coprime_iff_not_dvd.mpr hK).symm).dvd_of_dvd_mul_left hdiv

private lemma supplement_intersection_eq (M Y L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (hθ : theta M = Y) (hTM : (T : Subgroup G) ≤ M)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hcard : Nat.card (Y ⧸ pCore 2 Y) = 3) (hout : ¬ Y ≤ L) :
    (Y ⊔ (T : Subgroup G)) ⊓ L = (T : Subgroup G) ⊓ L := by
  let K := (Y ⊔ (T : Subgroup G)) ⊓ L
  have hKS : K ≤ Y ⊔ (T : Subgroup G) := inf_le_left
  have hSM : Y ⊔ (T : Subgroup G) ≤ M := sup_le (hθ ▸ theta_le M) hTM
  have hp : IsPGroup 2 K := two_group_of_three_free_in_join Y T K hTY T.isPGroup'
    hcard hKS (theta_control_three_free M Y L K hθ hcard hout (hKS.trans hSM) inf_le_right)
  have hn : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (le_inf ((show (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G) from le_sup_right).trans
      (Y ⊔ (T : Subgroup G)).le_normalizer) (le_normalizer_of_normal)).trans
        inf_normalizer_le_normalizer_inf
  have hKT : K ≤ T := by
    have he : K ⊔ (T : Subgroup G) = T :=
      T.is_maximal' (hp.to_sup_of_normal_left' T.isPGroup' hn) le_sup_right
    exact le_sup_left.trans_eq he
  exact le_antisymm (le_inf hKT inf_le_right) (inf_le_inf le_sup_right le_rfl)

private lemma invariant_sylow_intersection (M Y L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (hθ : theta M = Y) (hTM : (T : Subgroup G) ≤ M)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hcard : Nat.card (Y ⧸ pCore 2 Y) = 3) (hout : ¬ Y ≤ L) :
    Y ⊔ (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
  rw [← supplement_intersection_eq M Y L T hθ hTM hTY hcard hout]
  exact (le_inf (Y ⊔ (T : Subgroup G)).le_normalizer
    le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf

omit [Finite G] in
private lemma invariant_normalizer (S A : Subgroup G) (hSA : S ≤ normalizer (A : Set G)) :
    S ≤ normalizer (normalizer (A : Set G) : Set G) := by
  intro s hs
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (normalizer (A : Set G)).map (MulAut.conj s).toMonoidHom = _
  rw [map_equiv_normalizer_eq]
  have he : A.map (MulAut.conj s).toMonoidHom = A :=
    mem_normalizer_iff_map_conj_eq.mp (hSA hs)
  rw [he]

omit [Finite G] in
private lemma invariant_relative_normalizer (S L A : Subgroup G)
    (hSL : S ≤ normalizer (L : Set G)) (hSA : S ≤ normalizer (A : Set G)) :
    S ≤ normalizer ((L ⊓ normalizer (A : Set G) : Subgroup G) : Set G) :=
  (le_inf hSL (invariant_normalizer S A hSA)).trans inf_normalizer_le_normalizer_inf

omit [Finite G] in
private lemma solvable_normalized_join (A B : Subgroup G)
    [Group.IsSolvable A] [Group.IsSolvable B]
    (hn : B ≤ normalizer (A : Set G)) : Group.IsSolvable (A ⊔ B : Subgroup G) := by
  let A' := A.subgroupOf (A ⊔ B)
  let B' := B.subgroupOf (A ⊔ B)
  let : A'.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le A.le_normalizer hn)
  let : Group.IsSolvable A' := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show A ≤ A ⊔ B from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show A ≤ A ⊔ B from le_sup_left)).injective
  let : Group.IsSolvable B' := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show B ≤ A ⊔ B from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show B ≤ A ⊔ B from le_sup_right)).injective
  exact Group.isSolvable_of_normal_sup_eq_top A' B' (codisjoint_subgroupOf_sup A B).eq_top

omit [Finite G] in
private lemma normalized_solvable_le (H M Y T B : Subgroup G)
    [Group.IsSolvable (M ⊓ H : Subgroup G)] [Group.IsSolvable B]
    (hYS : Y ⊔ T ≤ M ⊓ H) (hBH : B ≤ H)
    (hn : Y ⊔ T ≤ normalizer (B : Set G))
    (hj : ∀ K : Subgroup G, Group.IsSolvable K → Y ⊔ T ≤ K → K ≤ H → K ≤ M ⊓ H) :
    B ≤ M ⊓ H := by
  let : Group.IsSolvable (Y ⊔ T : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hYS)
  let : Group.IsSolvable (B ⊔ (Y ⊔ T) : Subgroup G) := solvable_normalized_join B (Y ⊔ T) hn
  exact le_sup_left.trans (hj _ inferInstance le_sup_right (sup_le hBH (hYS.trans inf_le_right)))

omit [Finite G] in
private lemma theta_subgroupOf (H M Y : Subgroup G) (hθ : theta (M ⊓ H) = Y) :
    theta ((M ⊓ H).subgroupOf H) = Y.subgroupOf H := by
  apply map_injective H.subtype_injective
  rw [theta_map_of_injective _ H.subtype_injective,
    map_subgroupOf_eq_of_le inf_le_right, hθ,
    map_subgroupOf_eq_of_le ((hθ ▸ theta_le _).trans inf_le_right)]

private lemma theta_control_three_free_in (H M Y L B : Subgroup G)
    (hLH : L ≤ H) (hn : H ≤ normalizer (L : Set G))
    (hθ : theta (M ⊓ H) = Y)
    (hcard : Nat.card ((Y.subgroupOf H) ⧸ pCore 2 (Y.subgroupOf H)) = 3)
    (hout : ¬ Y ≤ L) (hBM : B ≤ M ⊓ H) (hBL : B ≤ L) :
    ¬ 3 ∣ Nat.card B := by
  let _ := (normal_subgroupOf_iff_le_normalizer hLH).mpr hn
  have hYH : Y ≤ H := (hθ ▸ theta_le _).trans inf_le_right
  have hout' : ¬ Y.subgroupOf H ≤ L.subgroupOf H := by
    intro he
    exact hout (fun x hx => he (show (⟨x, hYH hx⟩ : H) ∈ Y.subgroupOf H from hx))
  have hh := theta_control_three_free ((M ⊓ H).subgroupOf H) (Y.subgroupOf H)
    (L.subgroupOf H) (B.subgroupOf H) (theta_subgroupOf H M Y hθ) hcard hout'
    (comap_mono hBM) (comap_mono hBL)
  rwa [Nat.card_congr (subgroupOfEquivOfLe (hBM.trans inf_le_right)).toEquiv] at hh

/-- Under noncontainment, the intersection with the solvable supplement is the
actual Sylow intersection, and the supplement preserves it. -/
lemma replacement_sylow_intersection (H M Y L : Subgroup G) (T : Sylow 2 G)
    (hgen : H = reducedOvergroup L Y T) (hTM : (T : Subgroup G) ≤ M)
    (hθ : theta (M ⊓ H) = Y) (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hcomm : L = ⁅L, Y⁆)
    (hcard : Nat.card ((Y.subgroupOf H) ⧸ pCore 2 (Y.subgroupOf H)) = 3)
    (hout : ¬ Y ≤ localSpan L T) :
    (Y ⊔ (T : Subgroup G)) ⊓ localSpan L T = (T : Subgroup G) ⊓ localSpan L T ∧
    Y ⊔ (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ localSpan L T : Subgroup G) : Set G) := by
  let L0 := localSpan L (T : Subgroup G)
  have hL0H : L0 ≤ H := hgen ▸ le_sup_left
  have hTH : (T : Subgroup G) ≤ H := hgen ▸ le_sup_right.trans le_sup_right
  have hYH : Y ≤ H := (hθ ▸ theta_le _).trans inf_le_right
  have hn := componentClosure_normal_in_replacement L Y (T : Subgroup G)
    (le_normalizer_iff_commutator_le_left.mpr hcomm.ge) hTY
  rw [← hgen] at hn
  let _ := hn
  have hout' : ¬ Y.subgroupOf H ≤ L0.subgroupOf H := by
    intro he
    exact hout (fun x hx => he (show (⟨x, hYH hx⟩ : H) ∈ Y.subgroupOf H from hx))
  have hTY' : (T : Subgroup G).subgroupOf H ≤ normalizer (Y.subgroupOf H : Set H) := by
    apply le_normalizer_iff.mpr
    intro t ht y hy
    exact le_normalizer_iff.mp hTY t ht y hy
  have he := supplement_intersection_eq ((M ⊓ H).subgroupOf H)
    (Y.subgroupOf H) (L0.subgroupOf H) (T.subtype hTH)
    (theta_subgroupOf H M Y hθ) (fun x hx => ⟨hTM hx, x.property⟩) hTY' hcard hout'
  have he' : (Y ⊔ (T : Subgroup G)) ⊓ L0 = (T : Subgroup G) ⊓ L0 := by
    have hm := congrArg (Subgroup.map H.subtype) he
    simpa only [Sylow.coe_subtype, ← subgroupOf_sup hYH hTH,
      map_inf _ _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le (sup_le hYH hTH),
      map_subgroupOf_eq_of_le hTH, map_subgroupOf_eq_of_le hL0H] using hm
  refine ⟨he', ?_⟩
  rw [← he']
  exact (le_inf (Y ⊔ (T : Subgroup G)).le_normalizer
    ((hgen ▸ (show Y ⊔ (T : Subgroup G) ≤ reducedOvergroup L Y T from le_sup_right)).trans
      ((normal_subgroupOf_iff_le_normalizer hL0H).mp hn))).trans
        inf_normalizer_le_normalizer_inf

/-- The actual relative Sylow normalizer is controlled by universal (j).
Its solvability and identification with the Borel are separate model inputs.
The result derives invariance, containment, its 3′ order, and its action on Y₀. -/
lemma replacement_borel_control (H M Y L B : Subgroup G) (T : Sylow 2 G)
    [Group.IsSolvable (M ⊓ H : Subgroup G)] [Group.IsSolvable B]
    (hgen : H = reducedOvergroup L Y T) (hTM : (T : Subgroup G) ≤ M)
    (hθ : theta (M ⊓ H) = Y) (hN : normalizer (Y : Set G) = M)
    (hcomm : L = ⁅L, Y⁆)
    (hcard : Nat.card ((Y.subgroupOf H) ⧸ pCore 2 (Y.subgroupOf H)) = 3)
    (hout : ¬ Y ≤ localSpan L T)
    (hB : B = localSpan L T ⊓ normalizer (((T : Subgroup G) ⊓ localSpan L T : Subgroup G) : Set G))
    (hj : ∀ K : Subgroup G, Group.IsSolvable K → Y ⊔ (T : Subgroup G) ≤ K → K ≤ H → K ≤ M ⊓ H) :
    (Y ⊔ (T : Subgroup G)) ⊓ localSpan L T = (T : Subgroup G) ⊓ localSpan L T ∧
    Y ⊔ (T : Subgroup G) ≤ normalizer (B : Set G) ∧
    B ≤ M ⊓ H ∧ ¬ 3 ∣ Nat.card B ∧ B ≤ normalizer (Y : Set G) := by
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) := hTM.trans_eq hN.symm
  have hL0H : localSpan L T ≤ H := hgen ▸ le_sup_left
  have hTH : (T : Subgroup G) ≤ H := hgen ▸ le_sup_right.trans le_sup_right
  have hYS : Y ⊔ (T : Subgroup G) ≤ M ⊓ H :=
    sup_le (hθ ▸ theta_le _) (le_inf hTM hTH)
  have hn := componentClosure_normal_in_replacement L Y (T : Subgroup G)
    (le_normalizer_iff_commutator_le_left.mpr hcomm.ge) hTY
  rw [← hgen] at hn
  have hHL0 := (normal_subgroupOf_iff_le_normalizer hL0H).mp hn
  obtain ⟨he, hi⟩ := replacement_sylow_intersection H M Y L T hgen hTM hθ hTY hcomm hcard hout
  have hBS : Y ⊔ (T : Subgroup G) ≤ normalizer (B : Set G) := by
    rw [hB]
    exact invariant_relative_normalizer _ _ _ ((hYS.trans inf_le_right).trans hHL0) hi
  have hBL : B ≤ localSpan L T := hB ▸ inf_le_left
  have hBM := normalized_solvable_le H M Y T B hYS (hBL.trans hL0H) hBS hj
  exact ⟨he, hBS, hBM,
    theta_control_three_free_in H M Y (localSpan L T) B hL0H hHL0 hθ hcard hout hBM hBL,
    (hBM.trans inf_le_left).trans_eq hN.symm⟩
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner
