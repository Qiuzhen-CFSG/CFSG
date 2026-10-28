module

public import Theory.GroupTheory.WeakClosureFusion
public import Theory.GroupTheory.FusionInvariantTransfer
public import Theory.GroupTheory.SylowNormalIntersection
public import Mathlib.GroupTheory.IndexNormal

/-!
# Binary transfer from a weakly closed central subgroup

If Z is central in a Sylow two-subgroup S and weakly closed in S, its
normalizer controls fusion in S. Hence every binary character of N_G(Z)
restricts to a fusion-invariant character of S. Transfer extends that
restriction to G. A detected element of S gives an index-two normal kernel,
with precisely the prescribed intersection with S.

This is the character form of the Grün transfer step used in Parrott,
*A characterization of the Tits' simple group* (1972), §4, pp.682–683.
The local existence of the normalizer character is a separate hypothesis.
-/

open Subgroup
namespace Sylow

/-- A binary character of the normalizer of a weakly closed central subgroup
extends from the Sylow subgroup to the whole group. -/
public theorem exists_character_of_weakly_closed_normalizer
    {G A : Type*} [Group G] [Finite G] [CommGroup A] [Finite A]
    (S : Sylow 2 G) (Z : Subgroup G)
    (hZS : Z ≤ (S : Subgroup G))
    (hSC : (S : Subgroup G) ≤ centralizer (Z : Set G))
    (hweak : ∀ g : G, Z.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      Z.map (MulAut.conj g).toMonoidHom = Z)
    (φ : normalizer (Z : Set G) →* A) (hA : Nat.card A = 2) :
    ∃ τ : G →* A, ∀ x : S,
      τ (x : G) = φ ⟨(x : G), centralizer_le_normalizer _ (hSC x.property)⟩ := by
  let hSN : (S : Subgroup G) ≤ normalizer (Z : Set G) :=
    hSC.trans (centralizer_le_normalizer _)
  let χ : S →* A := φ.comp (inclusion hSN)
  have hrespect : ∀ x y : S, IsConj (x : G) (y : G) → χ x = χ y := by
    intro x y hxy
    obtain ⟨n, hn, he⟩ := S.weakly_closed_normalizer_controls_fusion Z hZS hSC
      (fun g hg => mem_normalizer_iff_map_conj_eq.mpr (hweak g hg))
      x.property y.property hxy
    have he' : (⟨n, hn⟩ : normalizer (Z : Set G)) * inclusion hSN x *
        (⟨n, hn⟩ : normalizer (Z : Set G))⁻¹ = inclusion hSN y := Subtype.ext he
    have hh := congrArg φ he'
    simp only [map_mul, map_inv] at hh
    rw [mul_comm (φ ⟨n, hn⟩), mul_assoc, mul_inv_cancel, mul_one] at hh
    exact hh
  exact ⟨χ.transfer, fun x => S.transfer_apply_eq_of_fusion_invariant χ hA hrespect x⟩

/-- A detected Sylow element produces a normal index-two subgroup; transfer
preserves the entire restriction of the normalizer character. -/
public theorem exists_normal_index_two_of_weakly_closed_normalizer
    {G A : Type*} [Group G] [Finite G] [CommGroup A] [Finite A]
    (S : Sylow 2 G) (Z : Subgroup G)
    (hZS : Z ≤ (S : Subgroup G))
    (hSC : (S : Subgroup G) ≤ centralizer (Z : Set G))
    (hweak : ∀ g : G, Z.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      Z.map (MulAut.conj g).toMonoidHom = Z)
    (φ : normalizer (Z : Set G) →* A) (hA : Nat.card A = 2)
    (b : S) (hb : φ ⟨(b : G), centralizer_le_normalizer _ (hSC b.property)⟩ ≠ 1) :
    ∃ L : Subgroup G, L.Normal ∧ L.index = 2 ∧ (b : G) ∉ L ∧
      ∀ x : S, (x : G) ∈ L ↔
        φ ⟨(x : G), centralizer_le_normalizer _ (hSC x.property)⟩ = 1 := by
  obtain ⟨τ, hτ⟩ := S.exists_character_of_weakly_closed_normalizer Z hZS hSC hweak φ hA
  have hbL : (b : G) ∉ τ.ker := by simpa only [MonoidHom.mem_ker, hτ b] using hb
  have hidx : τ.ker.index = 2 := by
    have hd : τ.ker.index ∣ 2 := by
      rw [index_ker]
      simpa only [hA] using card_subgroup_dvd_card τ.range
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hone | htwo
    · exact (hbL (index_eq_one.mp hone ▸ mem_top _)).elim
    · exact htwo
  exact ⟨τ.ker, inferInstance, hidx, hbL, fun x => by rw [MonoidHom.mem_ker, hτ x]⟩

/-- Intersecting a Sylow image with a normal index-two subgroup halves its
order as soon as the Sylow subgroup is not contained in that subgroup. The
intersection is the image of an actual Sylow subgroup of the normal subgroup. -/
public theorem image_inf_normal_index_two
    {G H : Type*} [Group G] [Group H] [Finite H]
    (S : Sylow 2 H) (j : H →* G) (hj : Function.Injective j)
    (L : Subgroup H) [L.Normal] (hL : L.index = 2)
    (hproper : ¬ (S : Subgroup H) ≤ L) :
    let Y := (S : Subgroup H).map j ⊓ L.map j
    Nat.card Y * 2 = Nat.card ((S : Subgroup H).map j) ∧
      ∃ T : Sylow 2 L, (T : Subgroup L).map (j.comp L.subtype) = Y := by
  intro Y
  have hidx : L.relIndex (S : Subgroup H) = 2 := by
    have hd := relIndex_dvd_index_of_normal (H := L) (K := (S : Subgroup H))
    rw [hL] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hone | htwo
    · exact (hproper (relIndex_eq_one.mp hone)).elim
    · exact htwo
  have hmap : (L.subgroupOf (S : Subgroup H)).map
      (j.comp (S : Subgroup H).subtype) = Y := by
    rw [← map_map, subgroupOf_map_subtype, map_inf _ _ _ hj, inf_comm]
  have hcard : Nat.card Y * 2 = Nat.card ((S : Subgroup H).map j) := by
    have hc := (L.subgroupOf (S : Subgroup H)).index_mul_card
    change L.relIndex (S : Subgroup H) * _ = _ at hc
    rw [hidx] at hc
    rw [← hmap, card_map_of_injective (f := j.comp (S : Subgroup H).subtype)
      (hj.comp (S : Subgroup H).subtype_injective), card_map_of_injective hj]
    omega
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal L
  refine ⟨hcard, T, ?_⟩
  rw [hT, ← map_map, subgroupOf_map_subtype, map_inf _ _ _ hj]

end Sylow
