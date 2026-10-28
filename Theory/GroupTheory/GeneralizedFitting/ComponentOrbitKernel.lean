module

public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Orbit

/-!
# Kernels induced over component orbits

Let K and Y lie in an ordinary component J, with Y normal in K and invariant
under the component stabilizer in A. Then K normalizes every A-conjugate of Y:
in the original component this is invariance, and in any other component it
follows from commutation. Thus the actual A-orbit join of Y is normal in KA.

This retains the local kernel, rather than replacing it by the full core of
an overgroup. The source application is the kernel H₀ in Aschbacher--Smith,
*The Classification of Quasithin Groups*, combined manuscript of 1 March 2004,
E.1.11, printed pp.213--214.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem IsComponent.normalizes_local_kernel_orbit {J K Y A : Subgroup G}
    (hJ : IsComponent G J) (hKJ : K ≤ J) (hYJ : Y ≤ J)
    (hKY : K ≤ normalizer (Y : Set G))
    (hinv : A ⊓ normalizer (J : Set G) ≤ normalizer (Y : Set G)) :
    K ≤ normalizer (componentOrbit Y A : Set G) := by
  apply (le_iInf fun a : A => ?_).trans (iInf_normalizer_le_normalizer_iSup _)
  by_cases he : J.map (MulAut.conj (a : G)).toMonoidHom = J
  · have heY : Y.map (MulAut.conj (a : G)).toMonoidHom = Y :=
      mem_normalizer_iff_map_conj_eq.mp
      (hinv ⟨a.property, mem_normalizer_iff_map_conj_eq.mpr he⟩)
    rw [heY]
    exact hKY
  · apply le_trans _ (centralizer_le_normalizer _)
    apply le_centralizer_iff.mp
    exact (map_mono hYJ).trans ((commutator_eq_bot_iff_le_centralizer.mp
      ((hJ.map_conj (a : G)).commutator_eq_bot_of_ne hJ he)).trans
      (centralizer_le hKJ))

theorem IsComponent.normal_local_kernel_orbit {J K Y A : Subgroup G}
    (hJ : IsComponent G J) (hKJ : K ≤ J) (hYK : Y ≤ K)
    (hKY : K ≤ normalizer (Y : Set G))
    (hinv : A ⊓ normalizer (J : Set G) ≤ normalizer (Y : Set G)) :
    ((componentOrbit Y A).subgroupOf (K ⊔ A)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer
    ((componentOrbit_le_sup Y A).trans (sup_le_sup hYK le_rfl))).mpr
  exact sup_le (hJ.normalizes_local_kernel_orbit hKJ (hYK.trans hKJ) hKY hinv)
    (le_normalizer_componentOrbit Y A)

end Theory.GroupTheory
