module

public import Theory.SpecificGroups.SL2.SubgroupTwoCore
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular

/-!
# Solvability of SL₂ subgroups with nontrivial two-core

For a finite field of characteristic two, a subgroup with nontrivial
intrinsic two-core is solvable. Conjugate that core into the standard
upper-unipotent Sylow subgroup. Its normalizer preserves the unique fixed
line of a nonidentity root element, so the conjugated subgroup lies in the
solvable triangular Borel. Normality is used only in the original subgroup.

This extends the fixed-line calculation in `SL2.SubgroupTwoCore` and supplies
the linear factor for the full Ree parabolic projection. Source: the elementary
rank-one local argument used in Aschbacher--Smith E.1.14(1), printed p.214,
citing Aschbacher (1982), Lemma 4.7; GLS3 §§2.3--2.6.
-/

public section

open Matrix Subgroup
open scoped MatrixGroups Pointwise
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A nontrivial two-core puts a characteristic-two SL₂ subgroup in a solvable Borel. -/
theorem isSolvable_of_twoCore_ne_bot (R : Subgroup (SL(2, F)))
    (hne : pCore 2 R ≠ ⊥) : Group.IsSolvable R := by
  let N := (pCore 2 R).map R.subtype
  obtain ⟨P, hNP⟩ := (pCore_isPGroup (p := 2) (G := R)).map R.subtype |>.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL(2, F)) P (upperUnipotentSylow F 2)
  let f : R →* SL(2, F) := (MulAut.conj g).toMonoidHom.comp R.subtype
  have hf : Function.Injective f := (MulAut.conj g).injective.comp Subtype.coe_injective
  let W := (pCore 2 R).map f
  have hWU : W ≤ upperUnipotent F := by
    calc
      W = N.map (MulAut.conj g).toMonoidHom := (Subgroup.map_map _ _ _).symm
      _ ≤ (P : Subgroup (SL(2, F))).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hNP
      _ = upperUnipotent F := by
        change (g • P : Sylow 2 (SL(2, F))).toSubgroup = _
        rw [hg]
        rfl
  have hW : W ≠ ⊥ := fun h => hne (((pCore 2 R).map_eq_bot_iff_of_injective hf).mp h)
  have hfn : f.range ≤ Subgroup.normalizer (W : Set (SL(2, F))) := by
    have h := Subgroup.le_normalizer_map (H := pCore 2 R) f
    simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map] using h
  have hfb : f.range ≤ rankOneBorel F :=
    hfn.trans (normalizer_le_rankOneBorel_of_le_upperUnipotent W hWU hW)
  let : Group.IsSolvable (rankOneBorel F) :=
    Theory.SpecificGroups.LinearSylowNormalizers.isSolvable_sylow_normalizer
      2 F (by decide) (upperUnipotentSylow F 2)
  exact Group.isSolvable_of_isSolvable_injective
    (f := f.codRestrict (rankOneBorel F) (fun x => hfb ⟨x, rfl⟩))
    (fun x y h => hf (congrArg Subtype.val h))

/-- A nonsolvable subgroup of characteristic-two SL₂ has trivial intrinsic two-core. -/
theorem twoCore_eq_bot_of_not_isSolvable (R : Subgroup (SL(2, F)))
    (hR : ¬ Group.IsSolvable R) : pCore 2 R = ⊥ := by
  by_contra h
  exact hR (isSolvable_of_twoCore_ne_bot R h)
end Matrix.SpecialLinearGroup
