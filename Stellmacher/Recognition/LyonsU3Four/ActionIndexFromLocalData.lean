module
public import Stellmacher.Recognition.LyonsU3Four.NTwoLocalStructure
public import Theory.GroupTheory.PGroup.CentralFourOddIndex

/-!
# The Lyons action-index obstruction from explicit local data

The quotient supplied by local centralizer data forces the Sylow normalizer
in an involution centralizer to centralize the whole Sylow center: the cyclic
five-complement acts trivially on the central four-group, and injectivity of
the Sylow embedding lifts this centrality. The local factorization therefore
identifies the centralizer index with a fixed-point index in the actual odd core.

Compatible invariant Sylow subgroups of that odd core reduce the obstruction
to the intrinsic central-four coprime-action theorem. No ambient character
calculation, Schur bound, or vanishing of a local odd core is assumed.

Source: Lyons, A Characterization of the Group U₃(4) (1972), §5, p.386.
-/

namespace Stellmacher.Recognition.LyonsU3Four
open Subgroup

private theorem five_action_fixes_center
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (h : SylowStructure S)
    (α : Multiplicative (ZMod 5) →* MulAut S) (a : Multiplicative (ZMod 5))
    (w : S) (hw : w ∈ center S) : α a w = w := by
  let W := center S
  let := h.center_elementary
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card (center S)
    rw [h.center_card]
    decide)
  let : IsKleinFour W := ⟨h.center_card, IsElementaryAbelian.exponent_eq_prime⟩
  let f := (MulAut.characteristic W).comp α
  have hd6 : orderOf (f a) ∣ 6 := IsKleinFour.card_mulAut W ▸ orderOf_dvd_natCard _
  have hd5 : orderOf (f a) ∣ 5 := (orderOf_map_dvd f a).trans (by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] using
      orderOf_dvd_natCard a)
  have he : f a = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 6 5) hd6 hd5)
  exact congrArg Subtype.val (DFunLike.congr_fun he (⟨w, hw⟩ : W))

private theorem local_five_center_central
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (h : SylowStructure S)
    (α : Multiplicative (ZMod 5) →* MulAut S)
    (w : S) (hw : w ∈ center S) :
    (SemidirectProduct.inl w : S ⋊[α] Multiplicative (ZMod 5)) ∈ center _ := by
  apply mem_center_iff.mpr
  intro a
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply,
      five_action_fixes_center S h α a.right w hw]
    exact mem_center_iff.mp hw a.left
  · simp

/-- The local Sylow normalizer centralizes the whole center of the supplied Sylow. -/
public theorem local_normalizer_le_center_centralizer
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    {z : G} (hz : z ∈ centerImage S) (hz1 : z ≠ 1) :
    normalizer (centralizerSylow S hz : Set (centralizer ({z} : Set G))) ≤
      (centralizer (centerImage S : Set G)).subgroupOf (centralizer ({z} : Set G)) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pPrimeCore 2 C)
  let f := involutionCentralizerQuotientMap S hz
  obtain ⟨β, α, _, _, e, he⟩ := d.involution_quotient z hz hz1
  intro n hn
  have hnG : (n : G) ∈ normalizer (S : Set G) := by
    change n ∈ normalizer ((S : Subgroup G).subgroupOf C : Set C) at hn
    rw [← subgroupOf_normalizer_eq (sylow_le_involutionCentralizer S hz)] at hn
    exact hn
  let γ : MulAut S := (S : Subgroup G).normalizerMonoidHom ⟨n, hnG⟩
  apply mem_centralizer_iff.mpr
  rintro w ⟨s, hs, rfl⟩
  have hcomm : q n * f s * (q n)⁻¹ = f s := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, he]
    rw [mem_center_iff.mp (local_five_center_central S h α s hs) (e (q n)),
      mul_inv_cancel_right]
  have heq : γ s = s := by
    apply involutionCentralizerQuotientMap_injective S hz
    change q (n * inclusion (sylow_le_involutionCentralizer S hz) s * n⁻¹) = f s
    change q n * q (inclusion (sylow_le_involutionCentralizer S hz) s) * (q n)⁻¹ = f s at hcomm
    simpa only [map_mul, map_inv] using hcomm
  have hh : (n : G) * (s : G) * (n : G)⁻¹ = (s : G) := congrArg Subtype.val heq
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The actual odd core supplements the full Sylow-center centralizer. -/
public theorem local_oddCore_sup_center_centralizer
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    {z : G} (hz : z ∈ centerImage S) (hz1 : z ≠ 1) :
    pPrimeCore 2 (centralizer ({z} : Set G)) ⊔
      (centralizer (centerImage S : Set G)).subgroupOf (centralizer ({z} : Set G)) = ⊤ := by
  apply top_unique
  intro c _
  obtain ⟨o, ho, n, hn, rfl⟩ := d.involution_factorization z hz hz1 c
  exact mul_mem (mem_sup_left ho)
    (mem_sup_right (local_normalizer_le_center_centralizer S h d hz hz1 hn))

private theorem index_eq_relIndex_of_normal_supplement
    {H : Type*} [Group H] [Finite H] (O D : Subgroup H) [O.Normal]
    (hsup : O ⊔ D = ⊤) : D.index = D.relIndex O := by
  have h1 := relIndex_mul_index (show D ⊓ O ≤ D from inf_le_left)
  rw [inf_relIndex_left, ← relIndex_sup_left D O, hsup, relIndex_top_right] at h1
  have h2 := relIndex_mul_index (show D ⊓ O ≤ O from inf_le_right)
  rw [inf_relIndex_right] at h2
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (index_ne_zero_of_finite : O.index ≠ 0))
    (h1.trans (by simpa only [Nat.mul_comm] using h2.symm))

/-- Every proper involution-centralizer index has a fourth-power prime divisor,
using only the explicit local data and the intrinsic supplied Sylow structure. -/
public theorem exists_prime_fourth_pow_dvd_centralizer_relIndex_of_local_data
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    {z : G} (hz : z ∈ centerImage S) (hz1 : z ≠ 1)
    (hne : centralizer ({z} : Set G) ≠ centralizer (centerImage S : Set G)) :
    ∃ p : ℕ, p.Prime ∧ p ^ 4 ∣
      (centralizer (centerImage S : Set G)).relIndex (centralizer ({z} : Set G)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := h.center_elementary
  let C := centralizer ({z} : Set G)
  let D := centralizer (centerImage S : Set G)
  let O := pPrimeCore 2 C
  let D' := D.subgroupOf C
  let i : S →* C := inclusion (sylow_le_involutionCentralizer S hz)
  let ρ : S →* MulAut O := MulAut.conjNormal.comp i
  let : MulDistribMulAction S O := MulDistribMulAction.compHom O ρ
  let F := FixedPoints.subgroup (center S) O
  have hDC : D ≤ C := centralizer_le (Set.singleton_subset_iff.mpr hz)
  have hsup : O ⊔ D' = ⊤ := local_oddCore_sup_center_centralizer S h d hz hz1
  have hF : F = D'.subgroupOf O := by
    ext x
    change (∀ w : center S, ρ w x = x) ↔ ((x : C) : G) ∈ D
    constructor
    · intro hx
      apply mem_centralizer_iff.mpr
      rintro w ⟨s, hs, rfl⟩
      have he := congrArg (fun y : O => ((y : C) : G)) (hx ⟨s, hs⟩)
      change (s : G) * ((x : C) : G) * (s : G)⁻¹ = ((x : C) : G) at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · intro hx w
      apply Subtype.ext
      apply Subtype.ext
      change (w.val : G) * ((x : C) : G) * (w.val : G)⁻¹ = ((x : C) : G)
      rw [mem_centralizer_iff.mp hx w.val ⟨w.val, w.property, rfl⟩, mul_inv_cancel_right]
  have hnot : ¬ center S ≤ ρ.ker := by
    intro hh
    have hOD : O ≤ D' := by
      intro o ho
      have hfixed : (⟨o, ho⟩ : O) ∈ F := by
        intro w
        exact DFunLike.congr_fun (hh w.property) ⟨o, ho⟩
      rw [hF] at hfixed
      exact hfixed
    have hDtop : D' = ⊤ := by simpa only [sup_eq_right.mpr hOD] using hsup
    exact hne ((subgroupOf_eq_top.mp hDtop).antisymm hDC)
  have hkernel : ∃ w : S, w ∈ center S ∧ w ≠ 1 ∧ ρ w = 1 := by
    obtain ⟨w, hw, hwz⟩ := hz
    change (w : G) = z at hwz
    refine ⟨w, hw, ?_, ?_⟩
    · intro he
      exact hz1 (hwz.symm.trans (congrArg Subtype.val he))
    · apply MulEquiv.ext
      intro o
      apply Subtype.ext
      apply Subtype.ext
      change (w : G) * ((o : C) : G) * (w : G)⁻¹ = ((o : C) : G)
      rw [hwz, ← mem_centralizer_singleton_iff.mp (o : C).property, mul_inv_cancel_right]
  have hcent : ∀ t : S, t ∉ center S → Nat.card (centralizer ({t} : Set S)) = 16 := by
    intro t ht
    exact order_four_centralizer_card_of_automizer_eq_fifteen S h d.automizer_fifteen t
      ((order_four_iff_not_mem_center S h t).mpr ht)
  obtain ⟨p, hp, hdiv⟩ := CentralFourCoprimeIndex.exists_prime_fourth_pow_dvd_center_fixed_index
    S.isPGroup' h.card h.center_card h.center_eq_frattini.symm hcent
    (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := C))) ρ hkernel hnot
  refine ⟨p, hp, ?_⟩
  change p ^ 4 ∣ D'.index
  rw [index_eq_relIndex_of_normal_supplement O D' hsup]
  change p ^ 4 ∣ (D'.subgroupOf O).index
  rwa [← hF]

end Stellmacher.Recognition.LyonsU3Four
