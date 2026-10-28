module
public import Theory.Representation.PSL3Two.NaturalDualNormalizer

/-!
# Coordinates and commutant of the doubled binary three-space

The nonisomorphism of a seed and its original automorphism twist excludes
inner automorphisms of SL₃(2). The checked automorphism action then identifies
the second factor with the contragredient, while keeping the first coordinate
and the actor marking unchanged. The natural–dual commutant calculation
transfers to every action with these coordinates.

`NonFFSourceDoubledBinaryCoordinates` constructs the markings from the actual
chosen seed and applies the commutant theorem to its whole orbit. These are
the model identifications used in H.4 and 7.6–7.7, not the ambient centralizer
geometry or the global bound r > 2.
Source: Aschbacher–Smith, D.3.10 and 7.6–7.7, printed pp.201,701–709.
-/

public noncomputable section
open Representation
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open BinaryLinearThree

/-- A nonisomorphic binary natural twist is the dual for the same actor;
the coordinate axes retain the original seed. -/
theorem doubledBinary_pair_coordinates {J U : Type*} [_root_.Group J]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) J U) (q : J →* Group)
    (e : U ≃ₗ[ZMod 2] Vector) (he : ∀ j v, e (ρ j v) = W (q j) (e v))
    (α : MulAut J) (a : MulAut Group)
    (ha : ∀ j, a (q j) = q (α j))
    (hne : ¬ Nonempty (ρ.Equiv (ρ.comp α.toMonoidHom))) :
    ∃ E : (U × U) ≃ₗ[ZMod 2] NaturalDual.Space,
      (∀ j v, E ((ρ.prod (ρ.comp α.toMonoidHom)) j v) =
        NaturalDual.action (q j) (E v)) ∧
      (∀ v, (E v).1 = e v.1) ∧
      (∀ v, (E v).2 = 0 ↔ v.2 = 0) := by
  have hout : a ∉ MulAut.innerSubgroup Group := by
    intro hi
    obtain ⟨b⟩ := (AutomorphismAction.natural_stabilizer a).mpr hi
    let c := (e.trans b.symm.toLinearEquiv).trans e.symm
    apply hne
    refine ⟨Representation.Equiv.mk c ?_⟩
    intro j
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (c (ρ j v)) = e (ρ (α j) (c v))
    rw [he]
    change e (e.symm (b.symm (e (ρ j v)))) =
      W (q (α j)) (e (e.symm (b.symm (e v))))
    rw [e.apply_symm_apply, e.apply_symm_apply, he, ← ha]
    exact LinearMap.congr_fun (b.symm.isIntertwining' (q j)) (e v)
  let b := AutomorphismAction.naturalOuterEquiv a hout
  refine ⟨e.prodCongr (e.trans b.toLinearEquiv), ?_, fun _ => rfl, ?_⟩
  · intro j v
    apply Prod.ext
    · exact he j v.1
    · change b (e (ρ (α j) v.2)) = W.dual (q j) (b (e v.2))
      rw [he, ← ha]
      exact LinearMap.congr_fun (b.isIntertwining' (q j)) (e v.2)
  · intro v
    exact (e.trans b.toLinearEquiv).map_eq_zero_iff

/-- The whole marked natural–dual module has trivial invertible commutant. -/
theorem doubledBinary_centralizer {J U : Type*} [_root_.Group J]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) J U) (q : J →* Group)
    (hq : Function.Surjective q) (e : U ≃ₗ[ZMod 2] NaturalDual.Space)
    (he : ∀ j v, e (ρ j v) = NaturalDual.action (q j) (e v))
    (f : U ≃ₗ[ZMod 2] U) (hf : ∀ j v, f (ρ j v) = ρ j (f v)) :
    f = LinearEquiv.refl _ _ := by
  let c := (e.symm.trans f).trans e
  have hc : ∀ g v, c (NaturalDual.action g v) = NaturalDual.action g (c v) := by
    intro g v
    obtain ⟨j,rfl⟩ := hq g
    change e (f (e.symm (NaturalDual.action (q j) v))) =
      NaturalDual.action (q j) (e (f (e.symm v)))
    have h := he j (e.symm v)
    rw [e.apply_symm_apply] at h
    rw [← h, e.symm_apply_apply, hf, he]
  have hid := NaturalDual.centralizer_eq_one c hc
  apply LinearEquiv.ext
  intro v
  apply e.injective
  have h := LinearEquiv.congr_fun hid (e v)
  simpa only [c, LinearEquiv.trans_apply, e.symm_apply_apply,
    LinearEquiv.refl_apply] using h

end CFSG.Quasithin.Chapter7.NormalizedSource
