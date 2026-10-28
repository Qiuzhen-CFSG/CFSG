module
public import Theory.Representation.BinaryRadicalFlag.Normalizer
public import Theory.Representation.SpecialLinearNatural
public import Theory.SpecificGroups.HigherLinear.ParabolicGeometry
/-!
# Radical subgroups determine actual type-A parabolics

A nontrivial two-radical subgroup of the determinant-one group over a finite
binary field has normalizer equal to the full stabilizer of a proper nonempty
partial flag. The flag comes from the canonical fixed filtration of the
natural representation, and radicality identifies the entire normalizer.

The dimension-three specialization permits both a maximal parabolic and a
Borel; the binary dimensions four and five are literal source applications.
Source: Aschbacher (1981), A pushing up theorem for finite groups, 8.2(7),
pp.73–74; Aschbacher–Smith C.2.7(3), printed pp.145–146.
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Subgroup
open scoped MatrixGroups
namespace Matrix.HigherLinear
variable {n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem radical_normalizer_eq_partialFlag (hn : 2 ≤ n)
    (U : Subgroup SL(n,F)) (hU : U.IsPRadical 2) :
    ∃ (k : ℕ) (W : Fin k → Submodule F (Fin n → F)),
      0 < k ∧ k < n ∧ StrictMono W ∧
      (∀ i, W i ≠ ⊥ ∧ W i ≠ ⊤) ∧
      normalizer (U : Set SL(n,F)) = ⨅ i, parabolicSL (W i) := by
  have : NeZero n := ⟨by omega⟩
  have hρ : Function.Injective (Representation.specialLinearNatural (k := F) n) := by
    intro g h hgh
    apply SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    exact LinearMap.congr_fun hgh
  obtain ⟨k,W,hpos,hlt,hs,hproper,heq⟩ :=
    Representation.BinaryRadical.exists_partialFlag_normalizer
      (Representation.specialLinearNatural n) hρ U hU
  refine ⟨k,W,hpos,?_,hs,hproper,heq⟩
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using hlt

theorem radical_normalizer_eq_partialFlag_three
    (U : Subgroup SL(3,F)) (hU : U.IsPRadical 2) :
    ∃ (k : ℕ) (W : Fin k → Submodule F (Fin 3 → F)),
      (k=1 ∨ k=2) ∧ StrictMono W ∧
      (∀ i, W i ≠ ⊥ ∧ W i ≠ ⊤) ∧
      normalizer (U : Set SL(3,F)) = ⨅ i, parabolicSL (W i) := by
  obtain ⟨k,W,hpos,hlt,hs,hproper,heq⟩ := radical_normalizer_eq_partialFlag (by decide : 2≤3) U hU
  exact ⟨k,W,by omega,hs,hproper,heq⟩

/-- The two-radical hypothesis can be supplied by the literal normalizer-core
identity arising from the C.2.7 component intersection. -/
theorem normalizer_eq_partialFlag_of_core (hn : 2 ≤ n)
    (U : Subgroup SL(n,F)) (hne : U ≠ ⊥)
    (hcore : (pCore 2 (normalizer (U : Set SL(n,F)))).map
      (normalizer (U : Set SL(n,F))).subtype = U) :
    ∃ (k : ℕ) (W : Fin k → Submodule F (Fin n → F)),
      0 < k ∧ k < n ∧ StrictMono W ∧
      (∀ i, W i ≠ ⊥ ∧ W i ≠ ⊤) ∧
      normalizer (U : Set SL(n,F)) = ⨅ i, parabolicSL (W i) :=
  radical_normalizer_eq_partialFlag hn U ⟨hne,hcore⟩

/-- The literal `SL₄(2)` source row. -/
theorem binary_four_radical_normalizer
    (U : Subgroup SL(4,ZMod 2)) (hU : U.IsPRadical 2) :
    ∃ (k : ℕ) (W : Fin k → Submodule (ZMod 2) (Fin 4 → ZMod 2)),
      0 < k ∧ k < 4 ∧ StrictMono W ∧
      (∀ i, W i ≠ ⊥ ∧ W i ≠ ⊤) ∧
      normalizer (U : Set SL(4,ZMod 2)) = ⨅ i, parabolicSL (W i) :=
  radical_normalizer_eq_partialFlag (by decide) U hU

/-- The literal `SL₅(2)` source row. -/
theorem binary_five_radical_normalizer
    (U : Subgroup SL(5,ZMod 2)) (hU : U.IsPRadical 2) :
    ∃ (k : ℕ) (W : Fin k → Submodule (ZMod 2) (Fin 5 → ZMod 2)),
      0 < k ∧ k < 5 ∧ StrictMono W ∧
      (∀ i, W i ≠ ⊥ ∧ W i ≠ ⊤) ∧
      normalizer (U : Set SL(5,ZMod 2)) = ⨅ i, parabolicSL (W i) :=
  radical_normalizer_eq_partialFlag (by decide) U hU

end Matrix.HigherLinear
