module
public import Theory.Representation.BinaryConjugationSection.CoordinateEmbedding
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# Commuting perfect actors on an embedded section

Embed the smaller marked quotient in the original ambient quotient using
both coordinate maps. A commuting actor preserving its numerator induces
an operator in the marked representation's invertible commutant. When
that commutant is trivial, its displacement lies in the retained central
kernel. Perfectness kills the second commutator and hence the first.

Source application: cross-centralization in Aschbacher--Smith 14.6.22(2),
printed p.1038. Neither the original quotient kernel nor its displacement
is assumed trivial.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G E V : Type*} [Group G]
  [AddCommGroup E] [Module (ZMod 2) E] [AddCommGroup V] [Module (ZMod 2) V]
  {H K Q U W Z : Subgroup G} [IsElementaryAbelian 2 W]
  {ρ : Representation (ZMod 2) H E} {σ : Representation (ZMod 2) K V}

/-- A perfect actor commuting on the original ambient quotient fixes a
marked invariant section with trivial invertible commutant, including its kernel. -/
theorem centralizes_of_embedded_trivial_commutant
    (c : BinaryConjugationSection H U Z ρ)
    (d : BinaryConjugationSection K W Z σ)
    (hKH : K ≤ H) (hQH : Q ≤ H) (hWU : W ≤ U)
    (hQW : Q ≤ normalizer (W : Set G))
    (hQZ : Q ≤ centralizer (Z : Set G)) [Group.IsPerfect Q]
    (hcomm : ∀ (q : Q) (k : K), Commute (ρ (inclusion hQH q)) (ρ (inclusion hKH k)))
    (htriv : ∀ f : V ≃ₗ[ZMod 2] V, (∀ k v, f (σ k v) = σ k (f v)) →
      f = LinearEquiv.refl _ _) : ⁅W,Q⁆ = ⊥ := by
  obtain ⟨j,hj,hcoord,hinter,_⟩ := c.exists_coordinate_embedding d hKH hWU
  obtain ⟨η,hη⟩ := d.exists_original_quotient_action hQW
    (hQZ.trans (centralizer_le_normalizer _))
  have hjη (q : Q) (v : V) : j (η q v) = ρ (inclusion hQH q) (j v) := by
    obtain ⟨w,hw⟩ := d.onto (Multiplicative.ofAdd v)
    have hv : (d.coordinates w).toAdd = v := congrArg Multiplicative.toAdd hw
    rw [←hv,hη,hcoord,hcoord]
    exact c.equivariant (inclusion hQH q) (inclusion hWU w)
  have hfix (q : Q) (v : V) : η q v = v := by
    let f := LinearMap.GeneralLinearGroup.toLinearEquiv (η.asGroupHom q)
    have hf : f = LinearEquiv.refl _ _ := htriv f (by
      intro k v
      apply hj
      change j (η q (σ k v)) = j (σ k (η q v))
      rw [hjη,←hinter,←hinter,hjη]
      simpa only [Module.End.mul_apply] using
        (LinearMap.congr_fun (hcomm q k).eq (j v)))
    exact congrArg (fun a : V ≃ₗ[ZMod 2] V => a v) hf
  have hWQ : ⁅W,Q⁆ ≤ Z := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro q hq w hw
    let a : W := W.normalizerMonoidHom (inclusion hQW ⟨q,hq⟩) ⟨w,hw⟩
    have he : d.coordinates a = d.coordinates ⟨w,hw⟩ := by
      apply Multiplicative.toAdd.injective
      exact (hη ⟨q,hq⟩ ⟨w,hw⟩).symm.trans (hfix ⟨q,hq⟩ _)
    have hz := (d.coordinates_eq_one_iff (a * (⟨w,hw⟩ : W)⁻¹)).mp (by
      rw [map_mul,map_inv,he,mul_inv_cancel])
    exact hz
  apply commutator_eq_bot_of_iterated_eq_bot W Q
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (hWQ.trans (le_centralizer_iff.mp hQZ))
end Representation.BinaryConjugationSection
