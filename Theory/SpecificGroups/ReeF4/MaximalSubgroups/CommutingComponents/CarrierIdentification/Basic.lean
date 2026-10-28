module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.Levi

/-!+# The canonical Levi in the commuting-component problem

The middle nodes `{1,2}` of the F₄ diagram generate the full signed B₂
subsystem. Intersecting this split Levi with the exceptional fixed subgroup
defines an actual subgroup of `Model m`. No carrier identification is part
of this definition.

The remaining geometric obligation places a supplied component onto this
subgroup by conjugation in the Ree group. It is stated separately from the
Suzuki matrix comparison so the two arguments can be developed independently.
`ComponentLeviConjugacy` is an obligation, not a proved classification.

Sources: GLS3, 2.3.4–8 and Table 2.4 type V,
`refs/KGroup/GLS3/chapter2.tex`; the Suzuki-wreath entry in Malle,
J. Algebra 139 (1991), 52–69, DOI 10.1016/0021-8693(91)90283-E,
reproduced in the proof of Theorem 5 of arXiv:0910.4758, pp.2–3.
-/

@[expose] public section

namespace ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification

open Subgroup LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration

/-- The fixed intersection of the full signed middle-node B₂ Levi. -/
noncomputable def standardSuzukiLevi (m : ℕ) : Subgroup (Model m) :=
  (splitLevi m .suzuki).subgroupOf (fixedSubgroup m)

/-- Every local exceptional construction gives the same fixed Levi, through
the comparison that preserves the underlying split matrices. -/
noncomputable def localLeviEquiv {m : ℕ} (d : LocalBlockInput m) :
    fixedLevi d .suzuki ≃* standardSuzukiLevi m where
  toFun x := ⟨d.modelEquiv x.val, by
    change (d.modelEquiv x.val).val ∈ splitLevi m .suzuki
    rw [LocalBlockInput.modelEquiv_coe]
    exact x.property⟩
  invFun x := ⟨d.modelEquiv.symm x.val, by
    change (d.modelEquiv.symm x.val).val ∈ splitLevi m .suzuki
    have he := d.modelEquiv_coe (d.modelEquiv.symm x.val)
    rw [d.modelEquiv.apply_symm_apply] at he
    rw [← he]
    exact x.property⟩
  left_inv x := Subtype.ext (d.modelEquiv.symm_apply_apply x.val)
  right_inv x := Subtype.ext (d.modelEquiv.apply_symm_apply x.val)
  map_mul' x y := Subtype.ext (d.modelEquiv.map_mul x.val y.val)

@[simp] theorem localLeviEquiv_coe {m : ℕ} (d : LocalBlockInput m)
    (x : fixedLevi d .suzuki) :
    ((localLeviEquiv d x).val : SplitGroup m) = x.val.val := by
  exact d.modelEquiv_coe x.val

/-- Geometric placement of an arbitrary component in the multiple-component
maximal-subgroup case. All component and radical hypotheses are relative to M. -/
def ComponentLeviConjugacy : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ L K : Subgroup M,
      L.IsCComponent → K.IsCComponent → L ≠ K → ⁅L, K⁆ = ⊥ →
        ∃ g : Model m,
          (L.map M.subtype).map (MulAut.conj g).toMonoidHom = standardSuzukiLevi m

end ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification
