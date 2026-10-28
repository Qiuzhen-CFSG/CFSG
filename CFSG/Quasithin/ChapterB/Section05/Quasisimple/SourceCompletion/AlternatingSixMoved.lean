module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFSocle
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Theory.Representation.BinaryOffender.AmbientSectionTransport
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOffender.NoncentralMoved
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.NormalElementaryEmbedding
/-!
# The moved layer of an FF module with alternating-six socle

The faithful self-centralizing simple component has order 360. The complete
B.5.1 classification forces its moved space into Irr⁺: the three reducible
alternatives have actors SL₃(F), SL₄(2), or SL₅(2), whose orders differ from
360. Every faithful invariant submodule therefore contains the full moved
space. For literal normal elementary subgroups, the original quotient action
and subgroup inclusion identify the ambient commutator with any contained
fully moved faithful subgroup.

Source: Aschbacher–Smith B.5.1; Meierfrankenfeld–Stellmacher (1993), (1.8)
and the symplectic case of (3.2), printed pp.863–864.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
private theorem linear_three_card_ne_360 (F : BinaryField) :
    Nat.card SL(3,F.Carrier) ≠ 360 := by
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
  have hq : 2 ≤ Nat.card F.Carrier := Finite.one_lt_card
  by_cases he : Nat.card F.Carrier = 2
  · simp [he]
  · have hq3 : 3 ≤ Nat.card F.Carrier := by omega
    have hb : 5616 ≤ Nat.card F.Carrier ^ 3 * (Nat.card F.Carrier ^ 3 - 1) *
        (Nat.card F.Carrier ^ 2 - 1) := by
      calc
        5616 = 3^3 * (3^3-1) * (3^2-1) := by norm_num
        _ ≤ _ := by gcongr
    omega
private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp
private theorem binary_higher_card_ne_360 {d : ℕ} (hd : d = 4 ∨ d = 5) :
    Nat.card SL(d,ZMod 2) ≠ 360 := by
  rcases hd with rfl | rfl <;> rw [binary_card] <;> norm_num [Fin.prod_univ_succ]

variable {G : Type*} [Group G] [Finite G]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
/-- The complete FF classification has only the Irr⁺ branch at order 360. -/
theorem ff_card360_moved_irrPlus
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    [L.Normal] [IsSimpleGroup L] [IsQuasisimple L]
    (hcard : Nat.card L = 360) (hC : centralizer (L : Set G) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple L)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ) :
    IsIrrPlus ρ L (subspaceCommutator ρ ⊤ L) := by
  obtain ⟨hLJ,⟨c⟩⟩ := ff_socle_source_conclusion ρ L hC hsq hf hff
  have hc : Nat.card (L.subgroupOf (offenderSubgroup ρ)) = 360 :=
    (Nat.card_congr (subgroupOfEquivOfLe hLJ).toEquiv).trans hcard
  cases c.clause_one with
  | irreducible hi _ _ _ _ =>
    rw [c.sectionData.space_eq] at hi
    change IsIrrPlus _ _ (subspaceCommutator (ρ.comp (offenderSubgroup ρ).subtype) ⊤ (L.subgroupOf (offenderSubgroup ρ))) at hi
    rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hLJ] at hi
    exact (IsIrrPlus.subgroupOf_iff ρ L (offenderSubgroup ρ) hLJ _).mp hi
  | doubleThree F _ e _ _ =>
    exact (linear_three_card_ne_360 F ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | naturalDual d hd _ hn =>
    obtain ⟨e⟩ := hn
    exact (binary_higher_card_ne_360 hd ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨e⟩ := hn
    exact (binary_higher_card_ne_360 hd ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion

open CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {M H : Type*} [Group M] [Finite M] [Group H] [Finite H]
variable (W X : Subgroup M) [W.Normal] [X.Normal]
  [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 X]

/-- A native fully moved faithful subgroup is the entire moved subgroup. -/
theorem normalElementary_card360_commutator_eq
    (hWX : W ≤ X) (q : M →* H) (hq : Function.Surjective q)
    (hW : q.ker = centralizer (W : Set M))
    (hX : q.ker = centralizer (X : Set M))
    (L : Subgroup M) (C : Subgroup H) [C.Normal] [IsSimpleGroup C] [IsQuasisimple C]
    (hLC : L.map q = C) (hcard : Nat.card C = 360)
    (hC : centralizer (C : Set H) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C)
    (hff : IsFFModule (NormalElementaryQuotient.representation X q hq hX))
    (hmove : ⁅W,L⁆ = W) : ⁅X,L⁆ = W := by
  let ρ := NormalElementaryQuotient.representation X q hq hX
  let σ := NormalElementaryQuotient.representation W q hq hW
  let e := NormalElementaryQuotient.inclusionLinear W X hWX
  have he : Function.Injective e := NormalElementaryQuotient.inclusionLinear_injective W X hWX
  have hact : ∀ g w, e (σ g w) = ρ g (e w) :=
    NormalElementaryQuotient.inclusionLinear_intertwines W X hWX q hq hW hX
  have hne : C ≠ ⊥ := by
    intro hz
    rw [hz,Subgroup.card_bot] at hcard
    omega
  have hn : ¬ LinearMap.range e ≤ fixedSpace ρ C :=
    range_not_fixed_of_faithful_embedding ρ σ e he hact
      (NormalElementaryQuotient.representation_injective W q hq hW) C hne
  have hs : C ≤ subspaceStabilizer ρ (LinearMap.range e) := by
    apply le_subspaceStabilizer
    rintro c hc _ ⟨w,rfl⟩
    exact ⟨σ c w,hact c w⟩
  have hi := ff_card360_moved_irrPlus ρ C hcard hC hsq
    (NormalElementaryQuotient.representation_injective X q hq hX) hff
  have heq := moved_eq_of_noncentral_invariant ρ C hi (LinearMap.range e) hs hn
  have hmW : subspaceCommutator σ ⊤ C = ⊤ := by
    rw [← hLC, ← NormalElementaryQuotient.commutatorSpace_eq W q hq hW]
    ext v
    change (v.toMul : M) ∈ ⁅W,L⁆ ↔ True
    rw [hmove]
    exact iff_true_intro v.toMul.property
  have hmX : subspaceCommutator ρ ⊤ C = LinearMap.range e := by
    rw [← heq]
    have hh := subspaceCommutator_map_embedding ρ σ (MonoidHom.id H) e
      (fun g w => (hact g w).symm) C ⊤
    simpa only [Submodule.map_top,Subgroup.map_id,hmW] using hh
  apply le_antisymm
  · intro x hx
    let v : Additive X := Additive.ofMul ⟨x,(commutator_le_left X L) hx⟩
    have hv : v ∈ subspaceCommutator ρ ⊤ C := by
      rw [← hLC, ← NormalElementaryQuotient.commutatorSpace_eq X q hq hX]
      exact hx
    rw [hmX] at hv
    obtain ⟨w,hw⟩ := hv
    have he' : (w.toMul : M) = x := congrArg (fun z : Additive X => (z.toMul : M)) hw
    exact he' ▸ w.toMul.property
  · rw [← hmove]
    exact commutator_mono hWX le_rfl
end CFSG.Quasithin.ChapterB.QuasisimpleSource
