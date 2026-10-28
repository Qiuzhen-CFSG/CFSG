module
public import Theory.Representation.SL2.OffenderFieldDegree
public import Theory.Representation.NormalElementaryQuotient.FixedIndex

/-!
# Original-degree lower bounds for binary rank-one actors

Every nontrivial two-subgroup of SL2(2^n) contains a nonidentity involution.
The irreducible-section displacement bound therefore makes it move at least
n binary dimensions of every nontrivial representation. The normal
elementary subgroup version uses the literal quotient action and retains
its whole fixed kernel.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 4.3 and its
SL2-module lower bound, pp.43--44. The faithful core-omega consumer is
Glauberman.PushingUpSL2Degree.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace Representation.SL2
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

theorem two_subgroup_fixedCodim_lower
    (ρ : Representation (ZMod 2) SL(2,F) V) (hnt : ∃ g, ρ g ≠ 1)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (A : Subgroup SL(2,F)) (hA : IsPGroup 2 A) (hne : A ≠ ⊥) :
    n ≤ fixedCodim ρ A := by
  obtain ⟨a,ha,hane⟩ := A.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨P,hP⟩ := hA.exists_le_sylow
  let e := (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 P).symm
  have hp : (⟨a,hP ha⟩ : P) ^ 2 = 1 := by
    apply e.injective
    rw [map_pow,map_one,pow_two]
    change (e ⟨a,hP ha⟩).toAdd + (e ⟨a,hP ha⟩).toAdd = 0
    exact CharTwo.add_self_eq_zero _
  have ha2 : a^2 = 1 := congrArg Subtype.val hp
  exact (involution_fixedCodim_lower ρ hnt hn hF a hane ha2).trans
    (NaturalTensor.fixedCodim_mono ρ (zpowers_le.mpr ha))

variable {G : Type*} [Group G]
theorem normal_two_subgroup_fixed_index_lower
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] [Finite U]
    (q : G →* SL(2,F)) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hne : ¬ A ≤ q.ker) :
    Nat.card F ≤ (centralizer (A : Set G)).relIndex U := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hf := NormalElementaryQuotient.representation_injective U q hq hker
  have himage : A.map q ≠ ⊥ := fun he => hne ((map_eq_bot_iff A).mp he)
  obtain ⟨g,hg,hgne⟩ := (A.map q).bot_or_exists_ne_one.resolve_left himage
  have hnt : ∃ g, ρ g ≠ 1 := ⟨g,fun hh => hgne (hf (hh.trans ρ.map_one.symm))⟩
  have hl := two_subgroup_fixedCodim_lower ρ hnt hn hF (A.map q) (hA.map q) himage
  rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim U q hq hker,hF]
  exact Nat.pow_le_pow_right (by decide) hl
end Representation.SL2
