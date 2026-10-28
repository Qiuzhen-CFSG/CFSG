module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.SixSpace.Inputs
public import Theory.Representation.BinaryPermutationNaturalDuality
public import Theory.Representation.SubrepresentationLattice

/-!
# Recognizing the A₇ six-space from a point-stabilizer fixed vector

Extend the vector along the transitive seven-letter action, then extend linearly
from the permutation basis. Independence of the chosen transports uses the
literal point stabilizer. Irreducibility makes the map onto. Its kernel has
dimension one, so the six-dimensional augmentation core maps nontrivially and
hence bijectively. The odd-degree core/deleted comparison gives the required
natural model. The invariant coordinate pairing handles a fixed covector.

The actual source consumer is `sevenSixSpace_of_pointSimpleDegrees`.
Source: Aschbacher–Smith K.1.2, printed p.452 (PDF p.463); the permutation
models and their invariant pairing are the modules of §B.3.
-/

public section
open Representation
namespace CFSG.Quasithin.ChapterK.Alternating.SevenSixSpace

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Seven translates of a point-stabilizer fixed vector give a surjection
from the permutation module. Its restriction to the core is a bijection and
intertwines the original actor with the canonical natural action. -/
theorem of_point_fixed (ρ : Representation (ZMod 2) Actor V)
    [ρ.IsIrreducible] (hd : Module.finrank (ZMod 2) V = 6)
    (hfixed : Representation.invariants (ρ.comp PointStabilizer.subtype) ≠ ⊥) :
    Nonempty (ρ.Equiv (BinaryPermutation.alternatingNaturalRepresentation (Fin 7))) := by
  classical
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfixed
  let : MulAction.IsPretransitive Actor (Fin 7) :=
    alternatingGroup.isPretransitive_of_three_le_card _ (by simp)
  have htrans (i : Fin 7) : ∃ g : Actor, g • (0 : Fin 7) = i :=
    MulAction.exists_smul_eq Actor 0 i
  let lift (i : Fin 7) : Actor := Classical.choose (htrans i)
  have hlift (i : Fin 7) : lift i • (0 : Fin 7) = i := Classical.choose_spec (htrans i)
  let value (i : Fin 7) : V := ρ (lift i) v
  have hvalue (g : Actor) (i : Fin 7) (hg : g • (0 : Fin 7) = i) : value i = ρ g v := by
    have hm : (lift i)⁻¹ * g ∈ PointStabilizer := by
      change ((lift i)⁻¹ * g) • (0 : Fin 7) = 0
      rw [mul_smul, hg]
      exact (congrArg (fun j => (lift i)⁻¹ • j) (hlift i).symm).trans (inv_smul_smul _ _)
    have hh := hv ⟨(lift i)⁻¹ * g, hm⟩
    change ρ ((lift i)⁻¹ * g) v = v at hh
    have he := congrArg (ρ (lift i)) hh
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at he
    exact he.symm
  have hvalue_o : value 0 = v := by simpa using hvalue 1 0 (one_smul _ _)
  have hvalue_act (g : Actor) (i : Fin 7) : value (g • i) = ρ g (value i) := by
    rw [hvalue (g * lift i) _ (by rw [mul_smul, hlift]), map_mul]
    rfl
  let f : (BinaryPermutation.alternatingRepresentation (Fin 7)).IntertwiningMap ρ := {
    toLinearMap := {
      toFun a := ∑ i : Fin 7, a i • value i
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro a
      change (∑ i : Fin 7, a (g.val.symm i) • value i) =
        ρ g (∑ i : Fin 7, a i • value i)
      rw [map_sum]
      simp only [map_smul, ← hvalue_act]
      exact (Equiv.sum_comp g.val
        (fun i => a (g.val.symm i) • value i)).symm.trans (by
          simp only [_root_.Equiv.symm_apply_apply, MulAction.subgroup_smul_def, Equiv.Perm.smul_def]) }
  have hf : f ≠ 0 := by
    intro hz
    have hfv : f (Pi.single 0 1) = v := by
      change (∑ i : Fin 7, (Pi.single 0 (1 : ZMod 2) : Fin 7 → ZMod 2) i • value i) = v
      simp [hvalue_o]
    exact hv0 (hfv.symm.trans (congrArg (fun t => t (Pi.single 0 1)) hz))
  have hfs := (IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  let j : (BinaryPermutation.alternatingCoreRepresentation (Fin 7)).IntertwiningMap
      (BinaryPermutation.alternatingRepresentation (Fin 7)) :=
    ⟨(BinaryPermutation.core (Fin 7)).subtype, fun _ => rfl⟩
  have hfj : f.comp j ≠ 0 := by
    intro hz
    have hr := f.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hfs, finrank_top, hd,
      BinaryPermutation.finrank_full, Fintype.card_fin] at hr
    have hle : BinaryPermutation.core (Fin 7) ≤ LinearMap.ker f.toLinearMap := by
      intro x hx
      exact congrArg (fun t => t ⟨x, hx⟩) hz
    have hk := Submodule.finrank_mono hle
    rw [BinaryPermutation.finrank_core, Fintype.card_fin] at hk
    omega
  have hsur := (IsIrreducible.surjective_or_eq_zero (f.comp j)).resolve_right hfj
  have hinj : Function.Injective (f.comp j) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [BinaryPermutation.finrank_core, Fintype.card_fin, hd])).mpr hsur
  let e := ((f.comp j).ofBijective ⟨hinj, hsur⟩).symm
  let c : (BinaryPermutation.alternatingCoreRepresentation (Fin 7)).Equiv
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 7)) :=
    Representation.Equiv.mk (BinaryPermutation.coreEquivNatural (Fin 7) (by decide)) (by
      intro g
      apply LinearMap.ext
      intro x
      exact BinaryPermutation.coreEquivNatural_equivariant (Fin 7) (by decide) g.val x)
  exact ⟨e.trans c⟩

private def dualEquiv {G X Y : Type*} [Group G]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) G X} {σ : Representation (ZMod 2) G Y}
    (e : ρ.Equiv σ) : ρ.dual.Equiv σ.dual :=
  Representation.Equiv.mk e.symm.toLinearEquiv.dualMap (by
    intro g
    ext f v
    exact congrArg f (LinearMap.congr_fun (e.symm.toIntertwiningMap.isIntertwining' g⁻¹) v).symm)

private noncomputable def evalEquiv (ρ : Representation (ZMod 2) Actor V) : ρ.Equiv ρ.dual.dual :=
  Representation.Equiv.mk (Module.evalEquiv (ZMod 2) V) (by
    intro g
    ext v f
    change f (ρ g v) = f (ρ (g⁻¹)⁻¹ v)
    rw [inv_inv])

private theorem irreducible_dual (ρ : Representation (ZMod 2) Actor V)
    [IsIrreducible ρ] : IsIrreducible ρ.dual := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  refine ⟨fun W => ?_⟩
  let U : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule.dualCoannihilator
      apply_mem_toSubmodule g v hv := by
        rw [Submodule.mem_dualCoannihilator] at hv ⊢
        intro f hf
        have h := hv (ρ.dual g⁻¹ f) (W.apply_mem_toSubmodule g⁻¹ hf)
        simpa only [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, inv_inv] using h }
  have hd : U.toSubmodule.dualAnnihilator = W.toSubmodule :=
    Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases eq_bot_or_eq_top U with h | h
  · right
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_bot
  · left
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_top

private noncomputable def naturalSelfDual :
    (BinaryPermutation.alternatingNaturalRepresentation (Fin 7)).Equiv
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 7)).dual :=
  Representation.Equiv.mk (BinaryPermutation.naturalDualEquiv (Fin 7)) (by
    intro g
    apply LinearMap.ext
    intro x
    exact BinaryPermutation.naturalDualEquiv_equivariant (Fin 7) g.val x)

/-- A fixed covector also recognizes the module, using the nondegenerate
coordinate pairing on the canonical natural module. The actor marking is
preserved in both cases. -/
theorem of_point_fixed_or_dual (ρ : Representation (ZMod 2) Actor V)
    [ρ.IsIrreducible] (hd : Module.finrank (ZMod 2) V = 6)
    (hfixed : Representation.invariants (ρ.comp PointStabilizer.subtype) ≠ ⊥ ∨
      Representation.invariants (ρ.dual.comp PointStabilizer.subtype) ≠ ⊥) :
    Nonempty (ρ.Equiv (BinaryPermutation.alternatingNaturalRepresentation (Fin 7))) := by
  rcases hfixed with hfixed | hfixed
  · exact of_point_fixed ρ hd hfixed
  · let : IsIrreducible ρ.dual := irreducible_dual ρ
    obtain ⟨e⟩ := of_point_fixed ρ.dual (by simpa using hd) hfixed
    exact ⟨(evalEquiv ρ).trans ((dualEquiv e).trans naturalSelfDual.symm)⟩


end CFSG.Quasithin.ChapterK.Alternating.SevenSixSpace
