module
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Trivial conjugate intersections from perfect point-centralizer residuals

A nonidentity common element puts a conjugate perfect subgroup in the local
point centralizer. If that element is fixed by the whole residual actor,
conjugate-overgroup rigidity finishes the argument. Otherwise the point
centralizer's solvable residual identifies the perfect subgroup, and its
normalizer forces the conjugator into the original overgroup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 10.2.10, printed p.753. The source-specific residual and normalizer
inputs are supplied by the Chapter 10 consumer.
-/

public section
open Subgroup Theory.GroupTheory

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem inf_conjugate_eq_bot_of_perfect_centralizer_residual
    (L R M U : Subgroup G) [Group.IsPerfect L]
    (hUL : U ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ U, u ≠ 1 → centralizer ({u} : Set G) ≤ M)
    (hconj : ∀ g : G, L.map (MulAut.conj g).toMonoidHom ≤ M →
      L.map (MulAut.conj g).toMonoidHom ≤ R)
    (hrigid : ∀ g : G, R ≤ M.map (MulAut.conj g).toMonoidHom → g ∈ M)
    (hres : ∀ u ∈ U, u ∉ centralizer (R : Set G) →
      (solvableResidual (R ⊓ centralizer ({u} : Set G) : Subgroup G)).map
        (R ⊓ centralizer ({u} : Set G)).subtype = L)
    (hNL : normalizer (L : Set G) ≤ M)
    {g : G} (hg : g ∉ M) : U ⊓ U.map (MulAut.conj g).toMonoidHom = ⊥ := by
  apply eq_bot_iff.mpr
  rintro v ⟨hv,u,hu,rfl⟩
  by_cases hu1 : u = 1
  · simp [hu1]
  have hv1 : (MulAut.conj g) u ≠ 1 :=
    fun he => hu1 ((MulAut.conj g).map_eq_one_iff.mp he)
  let C := centralizer ({(MulAut.conj g) u} : Set G)
  have hCM : C ≤ M := hcent _ hv hv1
  have hCMg : C ≤ M.map (MulAut.conj g).toMonoidHom := by
    rw [show C = (centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom from
      (CentralizerSmallKernelTransport.map_centralizer (MulAut.conj g) u).symm]
    exact map_mono (hcent u hu hu1)
  by_cases hvR : (MulAut.conj g) u ∈ centralizer (R : Set G)
  · exact (hg (hrigid g (le_trans (by
      intro r hr
      exact mem_centralizer_singleton_iff.mpr (hvR r hr)) hCMg))).elim
  let A := L.map (MulAut.conj g).toMonoidHom
  have hAC : A ≤ C := by
    rintro x ⟨l,hl,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg (MulAut.conj g) (hUL hu l hl)
  have hAR : A ≤ R := hconj g (hAC.trans hCM)
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := ((MulAut.conj g).subgroupMap L).toMonoidHom)
    ((MulAut.conj g).subgroupMap L).surjective
  have hAL : A ≤ L := (le_map_solvableResidual_of_isPerfect A (R ⊓ C)
    (le_inf hAR hAC)).trans_eq (hres _ hv hvR)
  have he : A = L := eq_of_le_of_card_ge hAL
    (Nat.card_congr ((MulAut.conj g).subgroupMap L).toEquiv).le
  exact (hg (hNL (mem_normalizer_iff_map_conj_eq.mpr he))).elim

end Subgroup
