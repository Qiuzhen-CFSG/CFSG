module
public import Theory.Representation.SymplecticFourOrthogonalCover.ParabolicFixed
public import Theory.SpecificGroups.SymplecticFour.CoreFixedCubic

/-!
# Cubic fixed vectors in the original local fixed spaces of a symplectic cover

The point residual fixes its entire core-fixed space in every central natural
cover. For the plane residual, a cubic element of its actual two-core quotient
has no fixed vector in a core-fixed, fully moved subspace. The proof keeps the
given natural projection and the literal residual two-core under conjugation.

Source: the natural local calculation and central-cover splitting used in
Aschbacher--Smith 9.4.1 and 4.3.8, printed pp.735 and616.
-/

public noncomputable section
open Matrix Subgroup Representation.OneCohomology
open Representation.BinaryOffender Theory.SpecificGroups.SymplecticFour
namespace Representation.SymplecticFourOrthogonalCover.ParabolicCubicFixed
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (L (K := F)) W}

omit [Finite F] [CharP F 2] [FiniteDimensional (ZMod 2) W] in
private theorem conjugate_projection_core_fixed
    (p : σ.IntertwiningMap (binaryNatural (K := F)))
    (B : Subgroup (L (K := F))) (g : Sp F) (w : W)
    (hw : w ∈ fixedSpace σ (B.pCoreIn 2)) :
    ∀ q ∈ ((B.map (commutator (Sp F)).subtype).map
      (MulAut.conj g).toMonoidHom).pCoreIn 2, q • (g • p w) = g • p w := by
  let f := (MulAut.conj g).toMonoidHom.comp (commutator (Sp F)).subtype
  have hf : Function.Injective f :=
    (MulAut.conj g).injective.comp (commutator (Sp F)).subtype_injective
  rw [Subgroup.map_map,←map_pCoreIn_of_injective 2 _ _ hf]
  rintro q ⟨r,hr,rfl⟩
  have he : r.val • p w = p w := by
    change binaryNatural r (p w) = p w
    rw [← p.isIntertwining]
    exact congrArg p (hw ⟨r,hr⟩)
  change ((MulAut.conj g) r.val) • (g • p w) = g • p w
  simpa only [MulAut.conj_apply,mul_smul,inv_smul_smul] using congrArg (g • ·) he

/-- The original point-local core fixed space is point-local fixed, even
in a nonsplit central natural cover and for a conjugate local residual. -/
theorem point_fixed_of_core_fixed (hF : Nat.card F = 4)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (B : Subgroup (L (K := F))) (g : Sp F)
    (hB : (B.map (commutator (Sp F)).subtype).map
      (MulAut.conj g).toMonoidHom = pointLocal) :
    fixedSpace σ (B.pCoreIn 2) ≤ fixedSpace σ B := by
  intro w hw b
  apply cover_fixed_of_projection_fixed p hp b.val w
  have hcore := conjugate_projection_core_fixed p B g w hw
  rw [hB] at hcore
  have hmem : (MulAut.conj g) b.val.val ∈ pointLocal := hB ▸
    mem_map_of_mem _ (mem_map_of_mem _ b.property)
  have he := CoreFixedCubic.point_fixed_of_core_fixed hF (g • p w) hcore
    ⟨(MulAut.conj g) b.val.val,hmem⟩
  have he' : g • (b.val.val • p w) = g • p w := by
    simpa only [MulAut.conj_apply,mul_smul,inv_smul_smul] using he
  exact (MulAction.injective g) he'

/-- A cubic element in the literal plane-local quotient fixes only zero
on every core-fixed fully moved subspace of the original cover. -/
theorem plane_cubic_fixed_eq_zero (hF : Nat.card F = 4)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (B : Subgroup (L (K := F))) (g : Sp F)
    (hB : (B.map (commutator (Sp F)).subtype).map
      (MulAut.conj g).toMonoidHom = planeLocal)
    (A : Submodule (ZMod 2) W) (hA : A ≤ fixedSpace σ (B.pCoreIn 2))
    (hm : subspaceCommutator σ A B = A)
    (b : B) (hb : orderOf (QuotientGroup.mk' (pCore 2 B) b) = 3)
    (w : W) (hw : w ∈ A) (hfix : σ b.val w = w) : w = 0 := by
  let f := (MulAut.conj g).toMonoidHom.comp (commutator (Sp F)).subtype
  have hf : Function.Injective f :=
    (MulAut.conj g).injective.comp (commutator (Sp F)).subtype_injective
  have he : B.map f = planeLocal := by simpa only [Subgroup.map_map] using hB
  let a : B ≃* planeLocal (F := F) :=
    (B.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr he)
  let eP : (planeLocal (F := F) ⧸ pCore 2 planeLocal) ≃*
      SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq
      ((planeLocal_core_eq (n := 2) hF (by decide)).trans Plane.quotientMap_ker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective Plane.quotientMap Plane.quotientMap_surjective)
  let eQ := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eP
  have ho : orderOf (Plane.quotientMap (a b)) = 3 :=
    (orderOf_injective eQ.toMonoidHom eQ.injective
      (QuotientGroup.mk' (pCore 2 B) b)).trans hb
  have hcore := conjugate_projection_core_fixed p B g w (hA hw)
  rw [hB] at hcore
  have hbfix : (a b).val • (g • p w) = g • p w := by
    have hh : b.val.val • p w = p w := by
      change binaryNatural b.val (p w) = p w
      rw [←p.isIntertwining,hfix]
    change ((MulAut.conj g) b.val.val) • (g • p w) = g • p w
    simpa only [MulAut.conj_apply,mul_smul,inv_smul_smul] using congrArg (g • ·) hh
  have hz := CoreFixedCubic.plane_cubic_fixed_eq_zero hF (a b) ho (g • p w) hcore hbfix
  have hpw : p w = 0 := (MulAction.injective g) (hz.trans (smul_zero g).symm)
  have hwfix : w ∈ fixed σ := by
    rw [cover_fixed_kernel p hp]
    exact hpw
  exact ParabolicFixed.cover_fixed_eq_zero_of_moved_subspace hF p hp B g (Or.inr hB)
    A hA hm w hw hwfix

end Representation.SymplecticFourOrthogonalCover.ParabolicCubicFixed
