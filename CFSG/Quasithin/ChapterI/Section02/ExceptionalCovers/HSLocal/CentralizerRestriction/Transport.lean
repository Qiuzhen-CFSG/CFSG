module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CorePreimage
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# The cover core maps into the model centralizer's two-core

The preimage of a model centralizer normalizes the original centralizer:
conjugating its marked element changes it only by a central element.
Relative normality makes embedded two-cores monotone, and the literal map
with two-group kernel transports the preimage core. This proves the required
containment without assuming that the entire centralizer map is surjective.

Source application: the core-purity assertion in Aschbacher–Smith I.2.2(5),
printed p.412 / PDF p.423. All subgroups remain embedded in the given K.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
variable {K : Type*} [Group K]

def preimage (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) (u : K) :
    Subgroup K := (centralizer ({modelMap e u} : Set _)).comap (modelMap e)

theorem centralizer_le_preimage
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) (u : K) :
    centralizer ({u} : Set K) ≤ preimage e u := by
  intro x hx
  apply mem_centralizer_singleton_iff.mpr
  simpa only [map_mul] using congrArg (modelMap e) (mem_centralizer_singleton_iff.mp hx)

theorem preimage_normalizes_centralizer
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) (u : K) :
    preimage e u ≤ normalizer (centralizer ({u} : Set K) : Set K) := by
  have step (g : K) (hg : g ∈ preimage e u) (x : K)
      (hx : x ∈ centralizer ({u} : Set K)) :
      g * x * g⁻¹ ∈ centralizer ({u} : Set K) := by
    have hgu : Commute (modelMap e g) (modelMap e u) :=
      mem_centralizer_singleton_iff.mp hg
    let z := g⁻¹ * u * g * u⁻¹
    have hz : z ∈ center K := by
      rw [← modelMap_ker e]
      change modelMap e z = 1
      simp only [z, map_mul, map_inv]
      rw [hgu.inv_left.eq]
      group
    have hc : Commute x (g⁻¹ * u * g) := by
      have hxc : Commute x z := mem_center_iff.mp hz x
      have hxu : Commute x u := mem_centralizer_singleton_iff.mp hx
      have hh := hxc.mul_right hxu
      simpa only [z, inv_mul_cancel_right] using hh
    have hh := hc.map (MulAut.conj g).toMonoidHom
    apply mem_centralizer_singleton_iff.mpr
    simpa [MulAut.conj_apply, mul_assoc] using hh.eq
  intro g hg
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact step g hg x
  · intro hx
    have h := step g⁻¹ ((preimage e u).inv_mem hg) _ hx
    simpa [mul_assoc] using h

theorem centralizerCore_le_preimage_core
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) (u : K) :
    centralizerCore u ≤ (preimage e u).pCoreIn 2 := by
  exact (pCoreIn_mono_of_normalizes (centralizerTwoResidual_le u)
    (le_normalizer_embedded_pResidual 2 (centralizer ({u} : Set K)))).trans
      (pCoreIn_mono_of_normalizes (centralizer_le_preimage e u)
        (preimage_normalizes_centralizer e u))

theorem preimage_map
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) (u : K) :
    (preimage e u).map (modelMap e) = centralizer ({modelMap e u} : Set _) := by
  apply map_comap_eq_self
  rw [MonoidHom.range_eq_top_of_surjective _
    (e.surjective.comp (QuotientGroup.mk'_surjective (center K)))]
  exact le_top

theorem core_image_le_model_centralizer_core [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K) :
    (centralizerCore u).map (modelMap e) ≤
      (centralizer ({modelMap e u} : Set _)).pCoreIn 2 := by
  have hk : IsPGroup 2 (modelMap e).ker := IsPGroup.of_card (n := 1)
    (by rw [modelMap_ker, hZ, pow_one])
  have h := map_mono (f := modelMap e) (centralizerCore_le_preimage_core e u)
  rwa [map_pCoreIn_of_ker_isPGroup _ hk, preimage_map] at h

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
