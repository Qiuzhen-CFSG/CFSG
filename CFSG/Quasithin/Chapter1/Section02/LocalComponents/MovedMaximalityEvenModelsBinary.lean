module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityEvenModelsSmall
public import Theory.SpecificGroups.BinaryLinear.SylowComponentUnique
public import Theory.SpecificGroups.PSL4Two.SchurMultiplier

/-!
# Binary higher linear models and the exceptional alternating model

The actual field map to F₂ and projective-to-linear equivalence transport
the dimension-at-most-five Levi restriction to PSL₄(2) and PSL₅(2).
The checked exceptional isomorphism PSL₄(2) ≃ A₈ then supplies A₈.
Source: Aschbacher--Smith A.3.12(4--5), pp.47--48; 1.2.8(1), p.506.
The exceptional-isomorphism port retains its attribution in LICENSES/ATLAS.txt.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
variable {G : Type*} [Group G] [Finite G]
theorem binary_higher_linear_sylow_overgroup_component_unique {n : ℕ} (hn : n=4 ∨ n=5)
    (hm : ClassicalGroup.IsPSL G n 2) : SylowOvergroupComponentUnique G := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let a : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  exact SylowOvergroupComponentUnique.of_equiv
    (e.trans ((Atlas.fieldEquivPSL n a).trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega))))
    (BinaryLinear.sylow_overgroup_component_unique_le_five n (by omega))

theorem alternating_eight_sylow_overgroup_component_unique
    (hm : LocalModels.IsAlternating G 8) : SylowOvergroupComponentUnique G := by
  obtain ⟨e⟩ := hm
  apply SylowOvergroupComponentUnique.of_equiv
    (e.trans (Matrix.PSL4Two.binaryEquivAlternatingEight (ZMod 2) (by simp)).symm)
  exact binary_higher_linear_sylow_overgroup_component_unique (Or.inl rfl)
    ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨MulEquiv.refl _⟩⟩
end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
