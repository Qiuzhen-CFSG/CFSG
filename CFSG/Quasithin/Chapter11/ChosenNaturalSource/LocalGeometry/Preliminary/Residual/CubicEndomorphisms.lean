module
public import Theory.Representation.SL3OddNaturalNormalizer
public import Theory.Representation.SL3DoubledNaturalOffenders.Centralizer
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity

/-!
# The endomorphism field of the full natural SL₃ module

Commuting with the elementary matrices makes every binary-linear
endomorphism a field scalar. This remains true for a surjective acting
group with arbitrary kernel. The cardinal identity is used in CubicDouble
to select an invariant constituent of the actual doubled natural action.
Source: the constituent count in Aschbacher--Smith A.3.19, pp.54--55.
-/

public noncomputable section
open Representation Matrix
open scoped MatrixGroups MonoidAlgebra
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.CubicNatural
variable {F H : Type*} [Field F] [Algebra (ZMod 2) F] [Group H]
variable (η : H →* SL(3,F)) (hη : Function.Surjective η)

private def scalarIntertwiner (c : F) :
    Representation.IntertwiningMap
      ((Representation.SL3OddNaturalNormalizer.binaryNatural F).comp η)
      ((Representation.SL3OddNaturalNormalizer.binaryNatural F).comp η) where
  toFun v := c • v
  map_add' v w := smul_add c v w
  map_smul' a v := by simp only [RingHom.id_apply, smul_comm a c]
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change c • (η g).val.mulVec v = (η g).val.mulVec (c • v)
    exact (Matrix.mulVec_smul _ _ _).symm

include hη in
private theorem scalarIntertwiner_bijective : Function.Bijective (scalarIntertwiner η) := by
  constructor
  · intro c d h
    have hh := congrArg (fun f => f (Pi.single 0 1) 0) h
    change c * (Pi.single 0 (1 : F) : Fin 3 → F) 0 =
      d * (Pi.single 0 (1 : F) : Fin 3 → F) 0 at hh
    simpa only [Pi.single_eq_same, mul_one] using hh
  · intro f
    obtain ⟨c,hc⟩ := Representation.SL3DoubledNaturalOffenders.natural_centralizer_scalar
      f.toLinearMap.toAddMonoidHom (by
        intro g v
        obtain ⟨h,rfl⟩ := hη g
        exact LinearMap.congr_fun (f.isIntertwining' h) v)
    refine ⟨c,?_⟩
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    exact (hc v).symm

include hη in
/-- The endomorphism field of the literal natural representation is F,
even when the acting group has a nontrivial kernel. -/
theorem natural_end_card :
    Nat.card (Module.End (ZMod 2)[H]
      (Representation.asModule ((Representation.SL3OddNaturalNormalizer.binaryNatural F).comp η))) = Nat.card F := by
  let μ := (Representation.SL3OddNaturalNormalizer.binaryNatural F).comp η
  exact (Nat.card_congr (IntertwiningMap.equivLinearMapAsModule μ μ).toEquiv).symm.trans
    (Nat.card_congr (Equiv.ofBijective (scalarIntertwiner η) (scalarIntertwiner_bijective η hη))).symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.CubicNatural
