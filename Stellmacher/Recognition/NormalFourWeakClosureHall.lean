module

public import Theory.GroupTheory.PGroup.RankTwoNormalFour
public import Theory.GroupTheory.NormalFourSign
public import BenderSuzuki.External.Hall.theorem_14_4_1
import Mathlib.GroupTheory.Nilpotent

/-!
# Hall's obstruction to a weakly closed normal four

Let `E` be a normal elementary four in a Sylow two-subgroup `S`, whose central
first omega has order two. If every involution of `S` lies in `E`, then its
ambient image `W` cannot be weakly closed in a nonsolvable finite simple group.

The action of `N_G(W)` on the three nonidentity elements of `W` gives a sign
kernel of index two containing `W`. Simplicity makes Hall's two-residual all
of `G`, and the transfer modulus of `N_G(W)` lies in the sign kernel. The
Engel commutators `e₂(u,z)` lie in `W`. Every nontrivial one is an involution,
and every involution of `N_G(W)` lies in `W`, by Sylow conjugacy. Thus all of
Hall's generating conjugates also lie in the sign kernel, a contradiction.

Source: Janko–Thompson, Math. Z. 113 (1970), §6, printed p.395 (saved PDF p.11),
and Hall, The Theory of Groups, Theorem 14.4.1. Once containment of all Sylow
involutions in `E` is supplied, the additional fusion hypothesis is unnecessary.
-/

open Subgroup
open BenderSuzuki.External
open scoped Pointwise commutatorElement

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

private theorem residual_eq_top [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G) :
    hallPResidual 2 G = ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : (hallPResidual 2 G).Normal := hallPResidual_normal 2 G
  rcases (inferInstance : (hallPResidual 2 G).Normal).eq_bot_or_eq_top with hb | ht
  · have hp := hallPResidual_quotient_isPGroup (G := G) 2
    have hpbot := hp.of_equiv (QuotientGroup.quotientMulEquivOfEq hb)
    let : Group.IsNilpotent G := (hpbot.of_equiv QuotientGroup.quotientBot).isNilpotent
    exact (hns inferInstance).elim
  · exact ht

omit [Finite G] in
private theorem modulus_le_sign_kernel (H : Subgroup G) (f : H →* ℤˣ) :
    hallTransferModulus 2 H H ≤ f.ker.map H.subtype := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ℤˣ := fun u => ⟨1, Int.units_sq u⟩
  have hres : (hallPResidual 2 H).map H.subtype ≤ f.ker.map H.subtype :=
    map_mono (hallPResidual_le_ker_of_isPGroup f hp)
  refine sup_le (sup_le ?_ ?_) hres
  · apply (closure_le _).mpr
    rintro x ⟨h, rfl⟩
    exact mem_map.mpr ⟨h ^ 2, by simp [MonoidHom.mem_ker, Int.units_sq], rfl⟩
  · apply commutator_le.mpr
    intro x hx y hy
    refine mem_map.mpr ⟨⁅(⟨x, hx⟩ : H), (⟨y, hy⟩ : H)⁆, ?_, rfl⟩
    change f ⁅(⟨x, hx⟩ : H), (⟨y, hy⟩ : H)⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _

private theorem hall_contradiction [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (S : Sylow 2 G) (W : Subgroup G)
    (hweak : WeaklyClosedIn (S : Subgroup G) W)
    (f : normalizer (W : Set G) →* ℤˣ)
    (hf : ∃ h, f h ≠ 1)
    (heng : ∀ u z c : G, u ∈ (S : Subgroup G) → z ∈ W →
      c * engelSymbol 2 u z * c⁻¹ ∈ normalizer (W : Set G) →
      c * engelSymbol 2 u z * c⁻¹ ∈ f.ker.map (normalizer (W : Set G)).subtype) :
    False := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := normalizer (W : Set G)
  let K := f.ker.map H.subtype
  have hKH : K ≤ H := map_subtype_le _
  have hnot : ¬ H ≤ K := by
    intro h
    obtain ⟨x, hx⟩ := hf
    obtain ⟨y, hy, heq⟩ := mem_map.mp (h x.property)
    have hyx : y = x := Subtype.ext heq
    exact hx (hyx ▸ hy)
  have hresK : (hallPResidual 2 H).map H.subtype ≤ K :=
    le_sup_right.trans (modulus_le_sign_kernel H f)
  have hreslt : (hallPResidual 2 H).map H.subtype < H :=
    lt_iff_le_not_ge.mpr ⟨hresK.trans hKH, fun h => hnot (h.trans hresK)⟩
  have hR : (⊤ : Subgroup G) = hallPResidual 2 G := (residual_eq_top hns).symm
  obtain ⟨Zs, hZs, A, hA, hgen⟩ :=
    (hall_theorem_14_4_1_p_hall_of_weakly_closed 2 S W
      (normalizer ((S : Subgroup G) : Set G)) H ⊤ H (S : Subgroup G)
      rfl (weaklyClosedIn_normalizer_le_normalizer hweak) rfl hweak hR
      (by simp) (by simp)).2 hreslt
  apply hnot
  refine hgen.trans (sup_le (modulus_le_sign_kernel H f) ((closure_le _).mpr ?_))
  intro x hx
  obtain ⟨u, z, c, hu, hz, _, hxh, rfl⟩ := hA x hx
  exact heng u z c hu (hZs z hz) hxh

private theorem involution_mem_of_normal_of_sylow (S : Sylow 2 G) (W H : Subgroup G)
    (hSH : (S : Subgroup G) ≤ H) (hHN : H ≤ normalizer (W : Set G))
    (hinv : ∀ t : G, t ∈ (S : Subgroup G) → orderOf t = 2 → t ∈ W)
    (t : G) (htH : t ∈ H) (ht : orderOf t = 2) : t ∈ W := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let tH : H := ⟨t, htH⟩
  have htHorder : orderOf tH = 2 := by simpa [tH] using ht
  have hp : IsPGroup 2 (zpowers tH) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, htHorder]; rfl :
      Nat.card (zpowers tH) = 2 ^ 1)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H T (S.subtype hSH)
  have hconj : g * tH * g⁻¹ ∈ (S.subtype hSH : Subgroup H) := by
    rw [← hg]
    exact mem_map.mpr ⟨tH, hT (mem_zpowers tH), rfl⟩
  have horder : orderOf ((g : G) * t * (g : G)⁻¹) = 2 := by
    simpa using (MulAut.conj (g : G)).orderOf_eq t |>.trans ht
  have hmem := hinv _ hconj horder
  exact (mem_normalizer_iff.mp (hHN g.property) t).mpr hmem

/-- Hall transfer excludes weak closure when all Sylow involutions belong to
the normal four and the central first omega has order two. -/
public theorem false_of_weakly_closed_of_involutions_mem [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hweak : ∀ g : G,
      (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
        (S : Subgroup G) →
      (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom =
        E.map (S : Subgroup G).subtype)
    (hinv : ∀ t : S, orderOf t = 2 → t ∈ E) : False := by
  let W := E.map (S : Subgroup G).subtype
  let H := normalizer (W : Set G)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map_subtype
  have hW : Nat.card W = 4 := by
    rw [card_map_of_injective (S : Subgroup G).subtype_injective, hE]
  have hSN : (S : Subgroup G) ≤ H := by
    simpa only [E.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      E.le_normalizer_map (S : Subgroup G).subtype
  have hnc : ¬ (S : Subgroup G) ≤ centralizer (W : Set G) := by
    intro hc
    apply four_not_le_center_of_card_omega_one_center_eq_two hZ E hE
    intro e he
    apply mem_center_iff.mpr
    intro s
    apply Subtype.ext
    exact (hc s.property (e : G) (mem_map_of_mem _ he)).symm
  obtain ⟨f, hf, _hindex, hWK⟩ := exists_normalizer_sign_of_noncentral_four
    (S : Subgroup G) W S.isPGroup' hSN hW hnc
  have hweak' : WeaklyClosedIn (S : Subgroup G) W :=
    ⟨map_subtype_le E, fun g hg => hweak g⁻¹ hg⟩
  have hinv' : ∀ t : G, t ∈ (S : Subgroup G) → orderOf t = 2 → t ∈ W := by
    intro t ht ho
    exact mem_map.mpr ⟨⟨t, ht⟩, hinv ⟨t, ht⟩ (by rwa [← Subgroup.orderOf_coe]), rfl⟩
  apply hall_contradiction hns S W hweak' f hf
  intro u z c hu hz hch
  have heW : engelSymbol 2 u z ∈ W := by
    have hc : u⁻¹ * z⁻¹ * u ∈ W := by
      simpa using (mem_normalizer_iff.mp (H.inv_mem (hSN hu)) z⁻¹).mp (W.inv_mem hz)
    exact W.mul_mem hc hz
  by_cases he : engelSymbol 2 u z = 1
  · simp [he]
  have heorder : orderOf (engelSymbol 2 u z) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (A := W) _ heW) he
  have horder : orderOf (c * engelSymbol 2 u z * c⁻¹) = 2 :=
    (MulAut.conj c).orderOf_eq _ |>.trans heorder
  exact hWK (involution_mem_of_normal_of_sylow S W H hSN le_rfl hinv' _ hch horder)

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
