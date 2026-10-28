module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Internal
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.GoldschmidtONan.Basic


/-!
# The factor centralizer fixes the moved module

Restriction to each actual natural plane is a scalar by the centralizer
calculation for SL₂. Over the binary field an invertible scalar is one.
Thus the centralizer of the offender subgroup fixes its full moved space.

Source: Aschbacher–Smith, proof of 14.1.7, printed p.977, using the
concrete B.1.8 factor witness (printed p.70).
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

theorem centralizer_fixes_support (i : Fin d.count) (c : G)
    (hc : c ∈ centralizer (d.factor i : Set G))
    {v : V} (hv : v ∈ subspaceCommutator ρ ⊤ (d.factor i)) : ρ c v = v := by
  let W := subspaceCommutator ρ ⊤ (d.factor i)
  have hstab : centralizer (d.factor i : Set G) ≤ subspaceStabilizer ρ W :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (fun _ _ _ _ => Submodule.mem_top))
      (centralizer_le_normalizer _)
  let a : W →ₗ[ZMod 2] W :=
    ((ρ c).comp W.subtype).codRestrict W (fun w => (hstab hc w).2 w.property)
  let e := d.naturalEquiv i
  let f : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    e.toLinearMap.comp (a.comp e.symm.toLinearMap)
  have hact (g : d.factor i) (w : Fin 2 → ZMod 2) :
      (e.symm (Representation.specialLinearNatural 2 (d.factorModel i g) w) : V) =
        ρ (g : G) (e.symm w : V) := by
    simpa only [e, LinearEquiv.apply_symm_apply] using
      (d.naturalEquiv_action i g (e.symm w)).symm
  have hf (w : Fin 2 → ZMod 2) : (e.symm (f w) : V) = ρ c (e.symm w : V) := by
    change (e.symm (e (a (e.symm w))) : V) = _
    rw [e.symm_apply_apply]
    rfl
  obtain ⟨k, hk⟩ := Representation.SL2NaturalOffenders.centralizer_scalar f.toAddMonoidHom (by
    intro g w
    obtain ⟨g, rfl⟩ := (d.factorModel i).surjective g
    apply e.symm.injective
    apply Subtype.val_injective
    change (e.symm (f (Representation.specialLinearNatural 2 (d.factorModel i g) w)) : V) =
      (e.symm (Representation.specialLinearNatural 2 (d.factorModel i g) (f w)) : V)
    rw [hf, hact, hact, hf]
    simpa only [← Module.End.mul_apply, ← map_mul] using
      congrArg (fun x => ρ x (e.symm w : V)) (hc g g.property).symm)
  change ∀ w, f w = k • w at hk
  have hinj : Function.Injective f := by
    intro x y hxy
    apply e.symm.injective
    apply Subtype.ext
    apply Representation.GoldschmidtONan.action_injective c
    rw [← hf, ← hf, hxy]
  have hkne : k ≠ 0 := by
    intro hk0
    have heq : f (fun _ => 1) = f 0 := by simp [hk, hk0]
    have h01 := congrFun (hinj heq) 0
    exact one_ne_zero h01
  have hk1 : k = 1 := (by decide +kernel : ∀ x : ZMod 2, x ≠ 0 → x = 1) k hkne
  have hfix : f (e ⟨v, hv⟩) = e ⟨v, hv⟩ := by simp [hk, hk1]
  have hh := congrArg (fun w => (e.symm w : V)) hfix
  rw [hf, e.symm_apply_apply] at hh
  exact hh


include d in
theorem centralizer_fixes_moved (c : G)
    (hc : c ∈ centralizer (offenderSubgroup ρ : Set G))
    {v : V} (hv : v ∈ subspaceCommutator ρ ⊤ (offenderSubgroup ρ)) : ρ c v = v := by
  have hi : ∀ i, subspaceCommutator ρ ⊤ (d.factor i) ≤ (ρ c - 1).ker := by
    intro i w hw
    change ρ c w - w = 0
    exact sub_eq_zero.mpr (d.centralizer_fixes_support i c
      (centralizer_le (d.factor_le_offenderSubgroup i) hc) hw)
  have h := (iSup_le hi) ((d.iSup_support.symm ▸ hv))
  exact sub_eq_zero.mp h

end CFSG.Quasithin.ChapterB.SolvableFFFactors
