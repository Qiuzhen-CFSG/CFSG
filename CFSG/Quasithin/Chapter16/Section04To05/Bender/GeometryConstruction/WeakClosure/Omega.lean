module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.LocalAction
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Omega
public import Theory.GroupAction.SylowPointwiseInner

/-!
# The center-free omega route to weak closure

When all two-elements of Aut(L) are inner and Z(L) is trivial, a Sylow
normalizing L is the product T_L T_C: its inner representative normalizes
T_L and is a two-element, hence lies in T_L by Sylow maximality. An
involution in this commuting product has both factors involutory, because
their common square lies in the trivial center of L. Thus the elementary
Bender space is Ω₁(T), and equal orders prove its weak closure.

The final odd-outer-index corollary is conditional on the actual full
automorphism index. It does not assert that index is odd for every binary
PSL₂ parameter. The Suzuki model discharge is in `WeakClosure.Suzuki`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
16.5.1, printed p.1194, and the automorphism input in 16.1.4(4).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure
open Subgroup
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z : G}
  {L R : Subgroup G} {n : ℕ}

/-- Inner representatives of Sylow elements lie in the specified component Sylow. -/
theorem sylow_inner_witness (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hinner : ∀ (α : MulAut L) (k : ℕ), α ^ (2 ^ k) = 1 → ∃ b : L, α = MulAut.conj b)
    {a : G} (ha : a ∈ T) :
    ∃ b ∈ componentSylow T L, b⁻¹ * a ∈ commutingSylow T L := by
  let an : normalizer (L : Set G) := ⟨a, h.sylow_normalizes ha⟩
  let α := L.normalizerMonoidHom an
  obtain ⟨k, hk⟩ := T.isPGroup' ⟨a, ha⟩
  have ha2 : a ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hα2 : α ^ (2 ^ k) = 1 := by
    change L.normalizerMonoidHom an ^ (2 ^ k) = 1
    rw [← map_pow, show an ^ (2 ^ k) = 1 from Subtype.ext ha2, map_one]
  obtain ⟨b, hb⟩ := hinner α k hα2
  have hbC : b ^ (2 ^ k) ∈ center L := by
    apply mem_center_iff.mpr
    intro x
    have he : MulAut.conj (b ^ (2 ^ k)) = 1 := by rw [map_pow, ← hb, hα2]
    have hx := DFunLike.congr_fun he x
    change b ^ (2 ^ k) * x * (b ^ (2 ^ k))⁻¹ = x at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  have hb2 : b ^ (2 ^ k) = 1 := mem_bot.mp (hZ ▸ hbC)
  have hp : IsPGroup 2 (zpowers b) := isPGroup_iff_card_dvd_pow.mpr
    ⟨k, by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hb2⟩
  obtain ⟨P, hP⟩ := h.toCentralComponentSetup.exists_component_sylow
  have hbn : b ∈ normalizer (P : Set L) := by
    rw [← P.coe_coe, hP]
    apply mem_normalizer_iff.mpr
    intro x
    have hx := congrArg L.subtype (DFunLike.congr_fun hb x)
    change a * (x : G) * a⁻¹ = ((b * x * b⁻¹ : L) : G) at hx
    change (x : G) ∈ T ↔ ((b * x * b⁻¹ : L) : G) ∈ T
    rw [← hx]
    exact (T : Subgroup G).le_normalizer ha x
  have hbP : b ∈ P := by
    have hi := hp.inf_normalizer_sylow P
    have hm : b ∈ zpowers b ⊓ normalizer (P : Set L) := ⟨mem_zpowers b, hbn⟩
    rw [hi] at hm
    exact hm.2
  have hbT : (b : G) ∈ T := by
    change b ∈ (P : Subgroup L) at hbP
    rw [hP] at hbP
    exact hbP
  refine ⟨b, ⟨hbT, b.property⟩, ⟨T.mul_mem (T.inv_mem hbT) ha, ?_⟩⟩
  intro x hx
  have he := congrArg L.subtype (DFunLike.congr_fun hb ⟨x, hx⟩)
  change a * x * a⁻¹ = (b : G) * x * (b : G)⁻¹ at he
  have he' : a * x = (b : G) * x * (b : G)⁻¹ * a := mul_inv_eq_iff_eq_mul.mp he
  calc
    x * ((b : G)⁻¹ * a) = (b : G)⁻¹ * ((b : G) * x * (b : G)⁻¹ * a) := by group
    _ = (b : G)⁻¹ * (a * x) := by rw [← he']
    _ = ((b : G)⁻¹ * a) * x := (mul_assoc _ _ _).symm

/-- The two commuting Sylow factors generate the whole Sylow subgroup. -/
theorem sylow_eq_sup (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hinner : ∀ (α : MulAut L) (k : ℕ), α ^ (2 ^ k) = 1 → ∃ b : L, α = MulAut.conj b) :
    (T : Subgroup G) = componentSylow T L ⊔ commutingSylow T L := by
  apply le_antisymm
  · intro t ht
    obtain ⟨b, hb, hc⟩ := sylow_inner_witness h hZ hinner ht
    simpa only [mul_inv_cancel_left] using mul_mem_sup hb hc
  · exact sup_le inf_le_left inf_le_left

/-- Centerlessness forces both factors of each involution to be involutory. -/
theorem space_eq_omega_of_inner (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hinner : ∀ (α : MulAut L) (k : ℕ), α ^ (2 ^ k) = 1 → ∃ b : L, α = MulAut.conj b)
    (d : LocalAction T L R n) : benderSpace T L = omegaOneAmbient (T : Subgroup G) := by
  let := d.commuting_elementary
  let := d.component_elementary
  let := space_elementary_of_factors (T := T) (L := L)
  apply le_antisymm
  · intro v hv
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl v (benderSpace_le_sylow T L hv)
      (elemPow_eq_one_of_isElementaryAbelian v hv)
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro t ht ht2
    apply TorusConstruction.involution_mem_space h
      (TorusConstruction.involutionLifting_of_center_eq_bot hZ) ht ht2
    rw [sylow_eq_sup h hZ hinner] at ht
    exact (show componentSylow T L ⊔ commutingSylow T L ≤
      centralizer (L : Set G) ⊔ L from
        sup_le (inf_le_right.trans le_sup_right) (inf_le_right.trans le_sup_left)) ht

/-- Conjugates of the elementary omega subgroup contained in T have the same order. -/
theorem space_weakly_closed_of_inner (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hinner : ∀ (α : MulAut L) (k : ℕ), α ^ (2 ^ k) = 1 → ∃ b : L, α = MulAut.conj b)
    (d : LocalAction T L R n) (a : G)
    (ha : (benderSpace T L).conjBy a ≤ (T : Subgroup G)) :
    (benderSpace T L).conjBy a = benderSpace T L := by
  let := d.commuting_elementary
  let := d.component_elementary
  let := space_elementary_of_factors (T := T) (L := L)
  have he : IsElementaryAbelian 2 ((benderSpace T L).conjBy a) :=
    IsElementaryAbelian.map (MulAut.conj a).toMonoidHom
  let := he
  apply eq_of_le_of_card_ge
  · intro v hv
    rw [space_eq_omega_of_inner h hZ hinner d]
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl v (ha hv)
      (elemPow_eq_one_of_isElementaryAbelian v hv)
  · exact (card_map_of_injective (MulAut.conj a).injective).ge

/-- The odd-index theorem applies to all two-elements, not only involutions. -/
theorem space_weakly_closed_of_odd_outer (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hodd : Odd (MulAut.conj : L →* MulAut L).range.index)
    (d : LocalAction T L R n) (a : G)
    (ha : (benderSpace T L).conjBy a ≤ (T : Subgroup G)) :
    (benderSpace T L).conjBy a = benderSpace T L :=
  space_weakly_closed_of_inner h hZ
    (fun α _ hα => MulAut.inner_of_two_pow_eq_one_of_odd_index hodd α hα) d a ha

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure
