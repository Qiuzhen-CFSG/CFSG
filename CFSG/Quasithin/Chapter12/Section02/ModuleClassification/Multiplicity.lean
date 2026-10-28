module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity

/-!
# Multiplicity of an irreducible repeated natural module

Evaluation at one coordinate is a nonzero intertwiner. Its kernel is nonzero
if another coordinate is present, so irreducibility forces exactly one copy.
The coordinate equivalence for that one copy retains the original actor.
Used below to compare B.5.1(1ii,iv) with the chosen Irr+ space in 12.2.2.
Source: Aschbacher--Smith B.5.1, printed pp.99--103.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ModuleClassification
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.ExtensionConsequences
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) H W)

theorem repeated_length_eq_one [Nontrivial W] {r : ℕ} (hr : 0 < r)
    (hi : IsIrreducible (repeated σ r)) : r = 1 := by
  classical
  let := hi
  let i : Fin r := ⟨0,hr⟩
  let f : (repeated σ r).IntertwiningMap σ :=
    (LinearMap.proj i).intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)
  obtain ⟨w,hw⟩ := exists_ne (0 : W)
  have hf : f ≠ 0 := by
    intro he
    have h := DFunLike.congr_fun he (fun _ => w)
    exact hw h
  have hinj := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  by_contra h
  have hr2 : 1 < r := by omega
  let j : Fin r := ⟨1,hr2⟩
  have he : f (Pi.single j w) = f 0 := by
    change (Pi.single j w : Fin r → W) i = (0 : Fin r → W) i
    simp [i,j]
  have hz := congrFun (hinj he) j
  simp only [Pi.single_eq_same,Pi.zero_apply] at hz
  exact hw hz

noncomputable def repeatedOneEquiv : ActionEquiv (repeated σ 1) σ where
  groupEquiv := MulEquiv.refl H
  linearEquiv :=
    { toFun := fun v => v 0
      invFun := fun v _ => v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun v => by ext i; exact congrArg v (Subsingleton.elim _ _)
      right_inv := fun _ => rfl }
  intertwines _ _ := rfl

end CFSG.Quasithin.Chapter12.Section02.ModuleClassification
