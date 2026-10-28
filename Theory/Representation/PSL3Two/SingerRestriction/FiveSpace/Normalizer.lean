module

public import Theory.Representation.PSL3Two.SingerRestriction.FiveSpace.Canonical

/-!
# Transport of Singer normalizer preservation

Conjugacy carries the actual Singer action, fixed spaces and nonzero orbits
to the canonical matrix model. The canonical normalizer calculation then
shows that every normalizer element preserves the given moving three-space.

Source: Aschbacher–Smith, J.2.3, printed pp.433–434 (PDF pp.444–445).
-/

public section

open Matrix Representation Representation.BinaryOffender Representation.RegularCyclicNormalClosure
open Subgroup
namespace BinaryLinearThree.SingerRestriction.FiveSpace
open Matrix.PSL3Two.OuterInvolutionSinger Certificate

private theorem transport_normalizer {X V : Type*} [_root_.Group X]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) X V) (K H : Subgroup X) (t : X)
    (he : K.map (MulAut.conj t).toMonoidHom = H)
    (hcanonical : ∀ (N : Submodule (ZMod 2) V),
      (∀ h ∈ K, ∀ u ∈ N, ρ h u ∈ N) →
      fixedSpace ρ K ⊓ N = ⊥ →
      (∀ u ∈ N, u ≠ 0 → ∀ w ∈ N, w ≠ 0 → ∃ h ∈ K, ρ h u = w) →
      ∀ k ∈ normalizer K, ∀ u ∈ N, ρ k u ∈ N)
    (M : Submodule (ZMod 2) V)
    (hM : ∀ h ∈ H, ∀ u ∈ M, ρ h u ∈ M)
    (hd : fixedSpace ρ H ⊓ M = ⊥)
    (ht : ∀ u ∈ M, u ≠ 0 → ∀ w ∈ M, w ≠ 0 → ∃ h ∈ H, ρ h u = w)
    (g : X) (hg : g ∈ normalizer H) (v : V) (hv : v ∈ M) : ρ g v ∈ M := by
  have hconj (t h : X) (v : V) :
      ρ ((MulAut.conj t) h) (ρ t v) = ρ t (ρ h v) := by
    change ρ (t*h*t⁻¹) (ρ t v) = _
    simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]
  let e := MulAut.conj t
  let N := M.comap (ρ t)
  have hinv (u : V) : ρ t (ρ t⁻¹ u) = u := Representation.self_inv_apply ρ t u
  have hN : ∀ h ∈ K, ∀ u ∈ N, ρ h u ∈ N := by
    intro h hh u hu
    change ρ t (ρ h u) ∈ M
    rw [← hconj t h u]
    exact hM _ (he ▸ mem_map.mpr ⟨h,hh,rfl⟩) _ hu
  have hdN : fixedSpace ρ K ⊓ N = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro u hu
    have hf : ρ t u ∈ fixedSpace ρ H := by
      rw [← he]
      intro k
      obtain ⟨a, ha, heq⟩ := k.property
      change ρ (k : X) (ρ t u) = ρ t u
      rw [← heq]
      exact (hconj t a u).trans (congrArg (ρ t) (hu.1 ⟨a, ha⟩))
    have hz : ρ t u ∈ (⊥ : Submodule (ZMod 2) V) :=
      hd ▸ (show ρ t u ∈ fixedSpace ρ H ⊓ M from ⟨hf,hu.2⟩)
    change ρ t u = 0 at hz
    exact (ρ.apply_bijective t).injective (hz.trans (map_zero _).symm)
  have htN : ∀ u ∈ N, u ≠ 0 → ∀ w ∈ N, w ≠ 0 →
      ∃ h ∈ K, ρ h u = w := by
    intro u hu hu0 w hw hw0
    have htu : ρ t u ≠ 0 := fun hz => hu0 ((ρ.apply_bijective t).injective
      (hz.trans (map_zero _).symm))
    have htw : ρ t w ≠ 0 := fun hz => hw0 ((ρ.apply_bijective t).injective
      (hz.trans (map_zero _).symm))
    obtain ⟨h, hh, hhuw⟩ := ht _ hu htu _ hw htw
    rw [← he] at hh
    obtain ⟨k, hk, rfl⟩ := hh
    refine ⟨k,hk, (ρ.apply_bijective t).injective ?_⟩
    rw [← hconj t k u]
    exact hhuw
  have hg' : e.symm g ∈ normalizer K := by
    have hn := congrArg (fun J : Subgroup X => normalizer (J : Set X)) he
    rw [← map_equiv_normalizer_eq K (MulAut.conj t)] at hn
    rw [← hn] at hg
    exact mem_map_equiv.mp hg
  have hvN : ρ t⁻¹ v ∈ N := by change ρ t (ρ t⁻¹ v) ∈ M; rwa [hinv]
  have hm := hcanonical N hN hdN htN (e.symm g) hg' (ρ t⁻¹ v) hvN
  change ρ t (ρ (e.symm g) (ρ t⁻¹ v)) ∈ M at hm
  have hc := hconj t (e.symm g) (ρ t⁻¹ v)
  have heq := congrArg₂ (fun (a : X) (u : V) => ρ a u)
    (e.apply_symm_apply g) (hinv v)
  exact (congrArg (fun u : V => u ∈ M) (hc.symm.trans heq)).mp hm

/-- Every normalizer element preserves a fixed-point-free transitive Singer
subspace of the actual Steinberg representation. -/
theorem normalizer_mem (H : Subgroup Group) (hH : Nat.card H = 7)
    (M : Submodule (ZMod 2) Steinberg)
    (hM : ∀ h ∈ H, ∀ v ∈ M, S h v ∈ M)
    (hd : fixedSpace S H ⊓ M = ⊥)
    (ht : ∀ v ∈ M, v ≠ 0 → ∀ w ∈ M, w ≠ 0 → ∃ h ∈ H, S h v = w)
    (g : Group) (hg : g ∈ normalizer H) (v : Steinberg) (hv : v ∈ M) : S g v ∈ M := by
  obtain ⟨t, he⟩ := exists_conjugate_singer H hH
  exact transport_normalizer S (zpowers singer) H t he canonical_mem M hM hd ht g hg v hv
end BinaryLinearThree.SingerRestriction.FiveSpace
