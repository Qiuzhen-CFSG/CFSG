module

public import Theory.Representation.BinaryOffender.Basic

/-!
# Quadraticity from two conjugate-generation statements

Quadraticity of B makes its action trivial on the displacements of C ≤ B.
Conjugate generation under a subgroup normalizing C extends this to R.
Then conjugating C by a subgroup normalizing R and generating R proves
that every displacement of R is fixed by R. The proof uses actual operator
identities; it does not assume that R is abelian or that the module splits.

Source: the propagation step in Aschbacher–Smith, B.4.9, final paragraph
on printed p.95, combined manuscript of 1 March 2004.
-/

public section
open Representation
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private def fixesDisplacements (C : Subgroup G) : Subgroup G where
  carrier := {g | ∀ c ∈ C, ∀ v, ρ g (ρ c v - v) = ρ c v - v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh c hc v
    simp only [map_mul, Module.End.mul_apply, hh c hc v, hg c hc v]
  inv_mem' := by
    intro g hg c hc v
    have h := congrArg (ρ g⁻¹) (hg c hc v)
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using h.symm

private def displacementIn (W : Submodule (ZMod 2) V) : Subgroup G where
  carrier := {g | ∀ v, ρ g v - v ∈ W}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh v
    simpa only [map_mul, Module.End.mul_apply, sub_add_sub_cancel] using
      W.add_mem (hg (ρ h v)) (hh v)
  inv_mem' := by
    intro g hg v
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply, neg_sub] using W.neg_mem (hg (ρ g⁻¹ v))

private theorem mixed_conjugate {A C : Subgroup G}
    (hmix : ∀ a ∈ A, ∀ c ∈ C, ∀ v, ρ a (ρ c v - v) = ρ c v - v) (g : G) :
    ∀ a ∈ A.map (MulAut.conj g).toMonoidHom,
      ∀ c ∈ C.map (MulAut.conj g).toMonoidHom,
        ∀ v, ρ a (ρ c v - v) = ρ c v - v := by
  have hinv (v : V) : ρ g⁻¹ (ρ g v) = v := by
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  have hginv (v : V) : ρ g (ρ g⁻¹ v) = v := by
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩ v
  change ρ (g * a * g⁻¹) (ρ (g * c * g⁻¹) v - v) = ρ (g * c * g⁻¹) v - v
  simpa only [map_mul, Module.End.mul_apply, map_sub, hinv, hginv] using
    congrArg (ρ g) (hmix a ha c hc (ρ g⁻¹ v))

/-- If B acts quadratically, C lies in B, the X-conjugates of B generate R,
and the N-conjugates of C generate R, then R acts quadratically. Here X
normalizes C and N normalizes R. No commutativity or finiteness is needed. -/
theorem quadratic_of_conjugate_generation {B C R X N : Subgroup G}
    (hB : IsQuadratic ρ B) (hCB : C ≤ B)
    (hXC : X ≤ Subgroup.normalizer C) (hNR : N ≤ Subgroup.normalizer R)
    (hBX : R ≤ ⨆ x : X, B.map (MulAut.conj (x : G)).toMonoidHom)
    (hCN : R ≤ ⨆ n : N, C.map (MulAut.conj (n : G)).toMonoidHom) :
    IsQuadratic ρ R := by
  have hRC : R ≤ fixesDisplacements ρ C := by
    apply hBX.trans
    apply iSup_le
    intro x
    have hc : C.map (MulAut.conj (x : G)).toMonoidHom = C :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXC x.property)
    have hm := mixed_conjugate ρ (fun b hb c hc v => hB b hb c (hCB hc) v) (x : G)
    rw [hc] at hm
    exact hm
  have hRK : R ≤ displacementIn ρ (fixedSpace ρ R) := by
    apply hCN.trans
    apply iSup_le
    intro n c hc v
    have hr : R.map (MulAut.conj (n : G)).toMonoidHom = R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNR n.property)
    have hm := mixed_conjugate ρ (fun r hr => hRC hr) (n : G)
    rw [hr] at hm
    intro r
    exact hm r r.property c hc v
  intro a ha b hb v
  exact (hRK hb v) ⟨a, ha⟩


end Representation.BinaryOffender
