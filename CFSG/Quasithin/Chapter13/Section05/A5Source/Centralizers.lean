module
public import Theory.Representation.BinaryPermutation.FiveInvariantHyperplane
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.SylowCalculation.Geometry
/-!
# Centralizers of the original Sylow-invariant A₅ hyperplane

The actual normalizer action contains A₅, and the image of T is Sylow in
that action. A Sylow subgroup cannot fix a nonsingular vector, whose orbit
has even length ten. The native invariant-hyperplane dichotomy therefore
forces every pointwise fixer of the actual order-eight W to act trivially
on V. Its action kernel is proved to be the genuine centralizer C_G(V).

This proves N_G(V) ∩ C_G(W) = C_G(V) without a prescribed coordinate
marking of W. Relative F.9.1 normalizer control also gives C_H(W)=C_H(V).

Source: Aschbacher–Smith 13.2.3(1) and 13.5.10, pp.878 and 918.
-/
@[expose] public section
open Subgroup BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.CentralizerReduction A5Module
open A5Module.FlagCoordinates A5Module.FlagCoordinates.SylowCalculation
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- The actual invariant third subgroup has no nontrivial permutation fixer. -/
theorem fixer_third (d : FlagSource T L V V₁ V₂)
    (W : Subgroup G) (hWV : W ≤ V) (hc : Nat.card W = 8)
    (hTW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (g : Equiv.Perm (Fin 5))
    (hg : ∀ x : Multiplicative Space, d.module.map x ∈ W →
      coreRepresentation (Fin 5) g x.toAdd = x.toAdd) : g = 1 := by
  let P : Set (Equiv.Perm (Fin 5)) :=
    ↑((d.imageSylow : Subgroup d.image).map d.image.subtype)
  have hpre : Nat.card (d.preimage W) = 8 :=
    (d.preimage_card W hWV).trans hc
  have hinv : ∀ p ∈ P, ∀ x ∈ d.preimage W,
      Multiplicative.ofAdd (coreRepresentation (Fin 5) p x.toAdd) ∈ d.preimage W := by
    rintro p ⟨q,hq,rfl⟩ x hx
    exact d.preimage_invariant W hTW q hq x hx
  rcases FiveInvariantHyperplane.fixed_hyperplane_dichotomy P (d.preimage W)
      hpre hinv g hg with h | ⟨x,hx,hfix⟩
  · exact h
  · exact (hx (sylow_fixed_singular d.image d.alternating_le_image d.imageSylow x
      (fun p hp => hfix p.val ⟨p,hp,rfl⟩))).elim

omit [Finite G] in
/-- The original normalizer actor has trivial kernel precisely on C_G(V). -/
theorem actor_eq_one_iff (d : FlagSource T L V V₁ V₂)
    (n : normalizer (V : Set G)) :
    d.normalizerAction n = 1 ↔ n.val ∈ centralizer (V : Set G) := by
  constructor
  · intro hn
    apply mem_centralizer_iff.mpr
    intro v hv
    obtain ⟨x,rfl⟩ := d.module.range_eq.ge hv
    have he := d.normalizer_equivariant n x.toAdd
    rw [hn] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hn
    apply FiveGeometry.eq_one_of_fixes_hyperplane
    intro x _
    apply Multiplicative.ofAdd.injective
    apply d.module.injective
    rw [← d.normalizer_equivariant]
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_iff.mp hn _ (map_mem d.module _)).symm

/-- Source 13.2.3(1)'s module calculation on the full normalizer.
Only the genuine source order and Sylow invariance of W are used. -/
theorem centralizer_third (d : FlagSource T L V V₁ V₂)
    (W : Subgroup G) (hWV : W ≤ V) (hc : Nat.card W = 8)
    (hTW : (T : Subgroup G) ≤ normalizer (W : Set G)) :
    normalizer (V : Set G) ⊓ centralizer (W : Set G) = centralizer (V : Set G) := by
  apply le_antisymm
  · intro n hn
    apply (actor_eq_one_iff d ⟨n,hn.1⟩).mp
    apply fixer_third d W hWV hc hTW
    intro x hx
    apply Multiplicative.ofAdd.injective
    apply d.module.injective
    rw [← d.normalizer_equivariant]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hn.2 _ hx).symm
  · exact le_inf (Subgroup.centralizer_le_normalizer _) (centralizer_le hWV)

/-- Relative centralizers agree wherever the actual W-normalizer already
normalizes V, as in original F.9.1(c). -/
theorem relative_centralizer_third (d : FlagSource T L V V₁ V₂)
    (W H : Subgroup G) (hWV : W ≤ V) (hc : Nat.card W = 8)
    (hTW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hN : H ⊓ normalizer (W : Set G) ≤ normalizer (V : Set G)) :
    H ⊓ centralizer (W : Set G) = H ⊓ centralizer (V : Set G) := by
  apply le_antisymm
  · intro x hx
    exact ⟨hx.1, (centralizer_third d W hWV hc hTW).le
      ⟨hN ⟨hx.1,Subgroup.centralizer_le_normalizer _ hx.2⟩,hx.2⟩⟩
  · exact inf_le_inf_left H (centralizer_le hWV)
end CFSG.Quasithin.Chapter13.Section05.A5Source
