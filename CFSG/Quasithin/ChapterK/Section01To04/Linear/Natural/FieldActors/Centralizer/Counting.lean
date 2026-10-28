module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.FieldActors.Coefficients
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.FieldActors.FixedSpaces
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Passing from the linear centralizer to the ambient centralizer

On an elementary subgroup of the literal centralizer, the coefficient image
has order at most two. Each element of the linear kernel has square one;
faithfulness and its determinant put it inside the marked SL₃ layer. Thus a
cardinality bound on elementary subgroups of C_L(a) gives a two-rank bound,
increased by one, on C_G(a). Elementary actors containing a inherit this bound.

The component cardinality estimate remains an explicit premise here. These
counting reductions do not assert that the fixed-field matrix estimate has
already been proved.

Source: Aschbacher–Smith, K.3.2.1, printed p.455, manuscript of 1 March 2004.
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterK.Linear.Natural.FieldActors.Centralizer

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) (F : BinaryField)
  (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3))

omit [Finite G] in
/-- The elementary coefficient image has order at most two; its kernel belongs to the marked SL₃ layer. -/
theorem elementary_card_le_of_component_bound
    (hf : Function.Injective ρ) (hs : IsSemilinearExtension ρ L F 3 e) (a : G) (r : ℕ)
    (hlin : ∀ B : Subgroup G, IsElementaryAbelian 2 B → B ≤ L →
      B ≤ Subgroup.centralizer ({a} : Set G) → Nat.card B ≤ 2 ^ r)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAC : A ≤ Subgroup.centralizer ({a} : Set G)) : Nat.card A ≤ 2 ^ (r + 1) := by
  let : IsElementaryAbelian 2 A := hA
  let φ := (coefficientAction ρ L F e hs).comp A.subtype
  let : IsElementaryAbelian 2 φ.ker := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      exact Subtype.ext ((Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p) x.val) }
  let B := φ.ker.map A.subtype
  have hBA : B ≤ A := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hBL : B ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact linear_square_one_mem_component ρ L F e hf x (elementary_square_one hA x)
      ((coefficientAction_eq_one_iff ρ L F e hs x).mp hx)
  have hB := hlin B IsElementaryAbelian.map_subtype hBL (hBA.trans hAC)
  have hker : Nat.card φ.ker ≤ 2 ^ r := by
    simpa only [B, Subgroup.card_map_of_injective A.subtype_injective] using hB
  calc
    Nat.card A ≤ 2 * Nat.card φ.ker :=
      SL2NaturalOffenders.card_le_two_mul_fieldAction_ker A hA φ
    _ ≤ 2 * 2 ^ r := Nat.mul_le_mul_left _ hker
    _ = 2 ^ (r + 1) := by rw [pow_succ, Nat.mul_comm]

/-- A bound on elementary subgroups of C_L(a) gives the corresponding bound plus one for the literal C_G(a). -/
theorem primeRank_le_of_component_bound
    (hf : Function.Injective ρ) (hs : IsSemilinearExtension ρ L F 3 e) (a : G) (r : ℕ)
    (hlin : ∀ B : Subgroup G, IsElementaryAbelian 2 B → B ≤ L →
      B ≤ Subgroup.centralizer ({a} : Set G) → Nat.card B ≤ 2 ^ r) :
    primeRank 2 (Subgroup.centralizer ({a} : Set G)) ≤ r + 1 := by
  let C := Subgroup.centralizer ({a} : Set G)
  apply (primeRank_le_iff_elementary_card_le C).mpr
  intro A hA
  let : IsElementaryAbelian 2 A := hA
  have hAC : A.map C.subtype ≤ C := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hbound := elementary_card_le_of_component_bound ρ L F e hf hs a r hlin
    (A.map C.subtype) IsElementaryAbelian.map_subtype hAC
  simpa only [Subgroup.card_map_of_injective C.subtype_injective] using hbound

omit [AddCommGroup V] [Module (ZMod 2) V] in
/-- An elementary subgroup containing the actual actor lies in its centralizer, with the stated binary-rank bound. -/
theorem elementary_rank_le_centralizer (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (a : G) (haA : a ∈ A) : rank A ≤ primeRank 2 (Subgroup.centralizer ({a} : Set G)) := by
  let : IsElementaryAbelian 2 A := hA
  let C := Subgroup.centralizer ({a} : Set G)
  have hAC : A ≤ C := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨x, hx⟩ : A) ⟨a, haA⟩))
  have hbound := (primeRank_le_iff_elementary_card_le (p := 2) (n := primeRank 2 C) C).mp le_rfl
    (A.subgroupOf C) (IsElementaryAbelian.subgroupOf hAC)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv] at hbound
  exact (Nat.log_mono_right hbound).trans_eq (Nat.log_pow (by decide : 1 < 2) _)

/-- The preceding centralizer estimate applies to every elementary actor containing a. -/
theorem elementary_rank_le_of_component_bound
    (hf : Function.Injective ρ) (hs : IsSemilinearExtension ρ L F 3 e) (a : G) (r : ℕ)
    (hlin : ∀ B : Subgroup G, IsElementaryAbelian 2 B → B ≤ L →
      B ≤ Subgroup.centralizer ({a} : Set G) → Nat.card B ≤ 2 ^ r)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (haA : a ∈ A) : rank A ≤ r + 1 :=
  (elementary_rank_le_centralizer A hA a haA).trans
    (primeRank_le_of_component_bound ρ L F e hf hs a r hlin)

end CFSG.Quasithin.ChapterK.Linear.Natural.FieldActors.Centralizer
