module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.CoverCoordinates.Transport
public import Theory.GroupTheory.QuaternionBinaryCentralExtension

/-!
# Lifting the marked M₁₂ involution and its full centralizer

Pull back the concrete left quaternion factor along the actual central quotient.
The quaternion central-extension theorem makes every lift of z square one.
The full first parabolic normalizes that factor, and its lifted normalizer fixes
the central kernel pointwise. It therefore fixes every lift of z, proving full
centralizer lifting before using any core or square-orbit conclusion.

Source: Aschbacher–Smith, I.2.2(5), common symplectic-core paragraph,
printed p.411 / PDF p.422. The factor normalizer is the concrete FirstCore input.
-/

@[expose] public section
noncomputable section
open Subgroup
open Theory.GroupTheory
open CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers
open CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
open CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.CoverCoordinates
open Sporadic.Mathieu.M12SmallPair

namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.CoverCoordinates.SymplecticCore
variable {K : Type*} [Group K]

theorem quaternion_lifting (e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12)
    (hZ : Nat.card (center K) = 2) (u : K) (hu : projection e u = z) :
    u ^ 2 = 1 ∧ (centralizer ({u} : Set K)).map (projection e) = firstParabolic := by
  let F := leftFactor.comap (projection e)
  let eqv := MonoidHom.ofInjective leftEmbedding_injective
  let q : F →* QuaternionGroup 2 :=
    eqv.symm.toMonoidHom.comp ((projection e).subgroupComap leftFactor)
  have hq (x : F) : leftEmbedding (q x) = projection e x :=
    congrArg Subtype.val (eqv.apply_symm_apply ((projection e).subgroupComap leftFactor x))
  have hqker (x : F) : x ∈ q.ker ↔ (x : K) ∈ center K := by
    rw [← projection_eq_one e, ← hq, ← leftEmbedding.map_one, leftEmbedding_injective.eq_iff]
    rfl
  have hk : q.ker ≤ center F := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp ((hqker x).mp hx) y)
  have hk2 : ∀ x ∈ q.ker, x ^ 2 = 1 := by
    intro x hx
    exact Subtype.ext (CoreLiftData.ambient_center_square hZ x ((hqker x).mp hx))
  have hsurj : Function.Surjective q :=
    eqv.symm.surjective.comp
      ((projection e).subgroupComap_surjective_of_surjective leftFactor (projection_surjective e))
  have hzm : leftEmbedding (QuaternionGroup.a 2) = z := by decide +kernel
  have huF : u ∈ F := by
    change projection e u ∈ leftFactor
    rw [hu]
    exact ⟨QuaternionGroup.a 2, hzm⟩
  have huq : q ⟨u, huF⟩ = QuaternionGroup.a 2 := by
    apply leftEmbedding_injective
    rw [hq, hu, hzm]
  obtain ⟨hsquare, hfixed⟩ := q.quaternion_lift_square_and_fixed hsurj hk hk2 ⟨u, huF⟩ huq
  constructor
  · exact congrArg Subtype.val hsquare
  · apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      change projection e x ∈ centralizer ({z} : Set Sporadic.Mathieu.M12)
      apply mem_centralizer_singleton_iff.mpr
      rw [← hu]
      exact Commute.map (show Commute x u from mem_centralizer_singleton_iff.mp hx) (projection e)
    · intro y hy
      obtain ⟨x, hx⟩ := projection_surjective e y
      have hxN : x ∈ normalizer (F : Set K) := by
        apply mem_normalizer_iff.mpr
        intro r
        change projection e r ∈ leftFactor ↔ projection e (x * r * x⁻¹) ∈ leftFactor
        rw [map_mul, map_mul, map_inv, hx]
        exact mem_normalizer_iff.mp (firstParabolic_normalizes_left hy) (projection e r)
      let α := F.normalizerMonoidHom ⟨x, hxN⟩
      have hα : ∀ k ∈ q.ker, α k = k := by
        intro k hk'
        apply Subtype.ext
        change x * (k : K) * x⁻¹ = k
        rw [mem_center_iff.mp ((hqker k).mp hk') x, mul_inv_cancel_right]
      have huα := hfixed α hα
      have he : x * u * x⁻¹ = u := congrArg Subtype.val huα
      exact mem_map.mpr ⟨x, mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp he), hx⟩

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.CoverCoordinates.SymplecticCore
