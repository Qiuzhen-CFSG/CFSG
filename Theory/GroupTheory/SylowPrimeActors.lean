module

public import Theory.GroupTheory.OddSubgroupLift
public import Theory.GroupTheory.SylowNormalizerCentralQuotient
public import Mathlib.GroupTheory.Commutator.Basic
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Odd actors on specified Sylow subgroups through central covers

A finite central extension with two-group kernel lifts odd subgroups with their
exact orders. Aligning the image Sylow by inner conjugation and comparing its
normalizer retains the original Sylow subgroup. Noncentral action on its derived
subgroup lifts, and a fixed-point-free quotient action has precisely the central
kernel as its fixed subgroup. Faithful embeddings retain both relative
centralizers and the noncentral derived action.

The proof combines Sylow conjugacy, Schur–Zassenhaus, and literal subgroup maps.
These elementary interfaces are used in the split-torus step of
Aschbacher–Smith, The Classification of Quasithin Groups, 2.5.7, printed p.556.
-/

public section
open Subgroup
namespace Subgroup
variable {E Q : Type*} [Group E] [Group Q]

theorem map_noncentral_commutator_of_injective (f : E →* Q)
    (hf : Function.Injective f) (S X : Subgroup E)
    (hm : ¬X ≤ centralizer ((⁅S,S⁆ : Subgroup E) : Set E)) :
    ¬ X.map f ≤ centralizer ((⁅S.map f,S.map f⁆ : Subgroup Q) : Set Q) := by
  intro h
  apply hm
  intro x hx d hd
  apply hf
  have hh := h (mem_map_of_mem f hx) (f d) (by
    rw [←map_commutator]
    exact mem_map_of_mem f hd)
  simpa only [map_mul] using hh

variable [Finite E] [Finite Q]

theorem exists_sylow_aligned_map (f : E →* Q) (hf : Function.Surjective f)
    (S : Sylow 2 E) (P : Sylow 2 Q) :
    ∃ β : E →* Q, Function.Surjective β ∧ β.ker = f.ker ∧
      (S : Subgroup E).map β = (P : Subgroup Q) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Q (S.mapSurjective hf) P
  let β := (MulAut.conj g).toMonoidHom.comp f
  refine ⟨β,(MulAut.conj g).surjective.comp hf,?_,?_⟩
  · ext x
    change (MulAut.conj g) (f x)=1 ↔ f x=1
    constructor
    · intro h
      apply (MulAut.conj g).injective
      simpa only [map_one] using h
    · intro h
      rw [h,map_one]
  · have h := congrArg Sylow.toSubgroup hg
    change ((S : Subgroup E).map f).map (MulAut.conj g).toMonoidHom = (P : Subgroup Q) at h
    simpa only [Subgroup.map_map] using h

theorem lift_odd_sylow_actor (f : E →* Q) (hf : Function.Surjective f)
    (h2 : IsPGroup 2 f.ker) (hc : f.ker ≤ center E)
    (S : Sylow 2 E) (A : Subgroup Q) (ho : Odd (Nat.card A))
    (hN : A ≤ normalizer ((S : Subgroup E).map f : Set Q))
    (hm : ¬ A ≤ centralizer (↑(⁅(S : Subgroup E).map f, (S : Subgroup E).map f⁆) : Set Q)) :
    ∃ X : Subgroup E, X.map f = A ∧ Nat.card X = Nat.card A ∧
      X ≤ normalizer (S : Set E) ∧
      ¬ X ≤ centralizer (↑(⁅(S : Subgroup E), (S : Subgroup E)⁆) : Set E) := by
  obtain ⟨X,hX,_,hcard,hpre⟩ := f.exists_odd_subgroup_lift hf h2 A ho
  refine ⟨X,hX,hcard,?_,?_⟩
  · rw [←S.normalizer_comap_of_central_kernel f hf hc]
    intro x hx
    exact hN (hX ▸ mem_map_of_mem f hx)
  · intro h
    apply hm
    rw [←hX, ←map_commutator]
    exact (map_mono h).trans (map_centralizer_le_centralizer_image _ _)

omit [Finite E] [Finite Q] in
theorem sylow_centralizer_eq_kernel_of_image (f : E →* Q)
    (h2 : IsPGroup 2 f.ker) (hc : f.ker ≤ center E)
    (S : Sylow 2 E) (X : Subgroup E)
    (hfix : (S : Subgroup E).map f ⊓ centralizer (X.map f : Set Q) = ⊥) :
    (S : Subgroup E) ⊓ centralizer (X : Set E) = f.ker := by
  apply le_antisymm
  · intro s hs
    have hfs : f s ∈ (S : Subgroup E).map f ⊓ centralizer (X.map f : Set Q) := by
      refine ⟨mem_map_of_mem f hs.1,?_⟩
      exact map_centralizer_le_centralizer_image _ _ (mem_map_of_mem f hs.2)
    rw [hfix] at hfs
    exact hfs
  · intro s hs
    exact ⟨h2.le_sylow_of_normal S hs, center_le_centralizer _ (hc hs)⟩
end Subgroup
