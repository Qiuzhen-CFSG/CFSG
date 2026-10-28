module
public import Theory.Mathieu.M22.QuasithinOddCores
public import Theory.Mathieu.M22.CoverDegreeEleven

/-!
# Small odd prime cores in groups containing full M₂₂ covers

The original supercritical Frattini action has odd kernel and degree at most
four. The characteristic-eleven degree bound now excludes the last large
odd-core alternative. Thus every odd prime core has rank at most two, the
precise hypothesis consumed by the original cubic-component comparison.

Source: Aschbacher--Smith A.1.28, printed p.26, and 4.2.13, printed p.612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Sporadic.Mathieu.M22CentralCover
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The eleven-core cannot have rank greater than two. -/
theorem eleven_core_rank_le_two
    {G : Type*} [Group G] [Finite G]
    (hqt : IsQuasithin G) (B : Subgroup G) [IsQuasisimple B]
    (e : (B ⧸ center B) ≃* M22) :
    primeRank 11 (pCore 11 G) ≤ 2 := by
  have hp : Odd 11 := by decide
  by_contra! hlarge
  have hp2 : 11 ≠ 2 := by decide
  let Q := pCore 11 G
  have hQ : IsPGroup 11 Q := pCore_isPGroup
  obtain ⟨X,hX⟩ := hQ.exists_supercriticalPSubgroup hp2
  let : X.Characteristic := hX.characteristic
  let : Fact (IsPGroup 11 X) := ⟨hQ.to_subgroup X⟩
  let : IsElementaryAbelian 11 (X ⧸ frattini X) := isElementaryAbelian_quotient_frattini
  have hlocal (a : G) (ha : orderOf a = 2) :
      primeRank 11 (centralizer ({a} : Set G)) ≤ 2 :=
    ((isTwoLocal_involution_centralizer ha).primeRank_le 11).trans
      ((isQuasithin_iff_twoLocalPrimeRank.mp hqt) 11 Fact.out hp)
  let f : PerfectCentralCovering.Cover B M22 := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := by rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk'] }
  have hthree : 3 ≤ primeRank 2 G := (three_le_twoRank f).trans
    (Theory.GroupTheory.primeRank_le_of_injective 2 B.subtype B.subtype_injective)
  have hdim := Theory.Quasithin.supercritical_frattini_finrank_le_four
    hp hlocal Q hQ hlarge hthree X hX
  let a : G →* MulAut (X ⧸ frattini X) :=
    ((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp MulAut.conjNormal
  have hodd : Odd (Nat.card a.ker) :=
    Theory.Quasithin.odd_card_supercritical_frattini_kernel hp hlocal Q hQ hlarge X hX
  let aB := a.comp B.subtype
  let : MulDistribMulAction B (X ⧸ frattini X) :=
    MulDistribMulAction.compHom (X ⧸ frattini X) aB
  let ρ : Representation (ZMod 11) B (Additive (X ⧸ frattini X)) :=
    Representation.ofElementaryAbelianAction
  have hker : ρ.asGroupHom.ker = aB.ker := by
    ext b
    rw [MonoidHom.mem_ker,MonoidHom.mem_ker]
    constructor
    · intro hb
      have hv := congrArg Units.val hb
      ext v
      exact congrArg (fun r : Module.End (ZMod 11) (Additive (X ⧸ frattini X)) =>
        r (Additive.ofMul v)) hv
    · intro hb
      apply Units.ext
      ext v
      exact congrArg (fun z : MulAut (X ⧸ frattini X) => z (Additive.toMul v)) hb
  have hρodd : Odd (Nat.card ρ.asGroupHom.ker) := by
    rw [hker]
    exact hodd.of_dvd_nat (card_comap_dvd_of_injective a.ker B.subtype B.subtype_injective)
  have hd := degree_ge_five_eleven_of_odd_kernel e ρ hρodd
  omega

/-- All odd prime cores have small rank, with the full M₂₂ cover retained. -/
theorem odd_core_rank_le_two
    {G : Type*} [Group G] [Finite G]
    (hqt : IsQuasithin G) (B : Subgroup G) [IsQuasisimple B]
    (e : (B ⧸ center B) ≃* M22)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) :
    primeRank p (pCore p G) ≤ 2 := by
  by_cases hp11 : p = 11
  · subst p
    exact eleven_core_rank_le_two hqt B e
  · exact odd_core_rank_le_two_of_ne_eleven hqt B e hp hp11

end Sporadic.Mathieu.M22CentralCover
