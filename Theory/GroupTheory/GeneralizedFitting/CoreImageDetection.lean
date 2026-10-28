module
public import Theory.GroupTheory.PCoreCentralKernelTransfer
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.CComponent.RadicalKernel

/-!
# Detecting the generalized Fitting preimage beyond an image two-core

Let a finite perfect group map onto another finite group, with kernel
central modulo the source two-core. If the source two-core quotient is
nontrivial, the preimage of its generalized Fitting subgroup cannot map
into the target two-core. The induced core-quotient map has central kernel.
Otherwise F* of the source core quotient is central; self-centralization
would make that nontrivial perfect quotient abelian.

Source application: Aschbacher--Smith, 11.5.8, printed p.784, the selection
of a chief factor detecting the generalized-Fitting lift.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {K H : Type*} [Group K] [Finite K] [Group H] [Finite H]

/-- A central-mod-core kernel cannot erase the whole generalized-Fitting lift. -/
theorem fitting_preimage_not_le_core_comap
    [Group.IsPerfect K] [Nontrivial (K ⧸ pCore 2 K)]
    (f : K →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ (center (K ⧸ pCore 2 K)).comap (QuotientGroup.mk' (pCore 2 K))) :
    ¬ (generalizedFitting (K ⧸ pCore 2 K)).comap (QuotientGroup.mk' (pCore 2 K)) ≤
      (pCore 2 H).comap f := by
  have hc : pCore 2 K ≤ (pCore 2 H).comap f := map_le_iff_le_comap.mp
    (le_sSup ⟨Normal.map inferInstance f hf, pCore_isPGroup.map f⟩)
  have hz := f.coreMap_ker_le_center_of_map_ker hf hc (map_le_iff_le_comap.mpr hk)
  intro hbad
  have hF : generalizedFitting (K ⧸ pCore 2 K) ≤ center (K ⧸ pCore 2 K) := by
    intro z hzf
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) z
    apply hz
    exact (QuotientGroup.eq_one_iff (f k)).mpr (hbad hzf)
  have htop : (⊤ : Subgroup (K ⧸ pCore 2 K)) ≤ center (K ⧸ pCore 2 K) := by
    apply le_trans _ ((centralizer_generalizedFitting_le (K ⧸ pCore 2 K)).trans hF)
    intro x _ y hy
    exact (mem_center_iff.mp (hF hy) x).symm
  have hab : IsMulCommutative (K ⧸ pCore 2 K) := isMulCommutative_iff.mpr fun a b =>
    (mem_center_iff.mp (htop (mem_top b)) a)
  exact Group.IsPerfect.not_isMulCommutative _ hab
end Theory.GroupTheory
