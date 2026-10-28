module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ModuleData
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.PSL3Two.SmallModuleProperties
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168

/-!
# The sharp multiplicity bound for a natural FF-quotient

An elementary offender in the actual SL₃(2) has rank at most two, using
the checked PSL₂(7) comparison and its dihedral Sylow groups. Each copy of
the faithful natural module has positive fixed codimension under this
nontrivial actor. Fixed codimensions add across the copies and cannot increase
under the given surjection, so there are at most two copies. Faithfulness
excludes zero copies, giving precisely multiplicity one or two.

This proof assumes explicit homogeneous natural quotient coordinates. It does
not classify irreducible factors, split extensions, or supply those coordinates.
It applies to arbitrary finite-dimensional FF-modules, including nonsplit ones.

Source: the binary multiplicity inequality in Aschbacher–Smith B.5.1(1),
printed pp.99–101, as used in C.1.34(1),(2),(5), pp.136–137 of the combined
manuscript of 1 March 2004.
-/

public section

open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition

private def copies {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) G W) (m : ℕ) :
    Representation (ZMod 2) G (Fin m → W) where
  toFun g := {
    toFun w i := σ g (w i)
    map_add' x y := by funext i; exact map_add (σ g) (x i) (y i)
    map_smul' a x := by funext i; exact map_smul (σ g) a (x i)
  }
  map_one' := by
    apply LinearMap.ext
    intro w
    funext i
    change σ 1 (w i) = w i
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro w
    funext i
    change σ (g*h) (w i) = σ g (σ h (w i))
    rw [map_mul]
    rfl

private def fixedCopiesEquiv {G W : Type*} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] (σ : Representation (ZMod 2) G W) (m : ℕ) (A : Subgroup G) :
    fixedSpace (copies σ m) A ≃ₗ[ZMod 2] (Fin m → fixedSpace σ A) where
  toFun w i := ⟨w.val i, fun a => congrFun (w.property a) i⟩
  invFun w := ⟨fun i => (w i).val, fun a => funext fun i => (w i).property a⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem fixedCodim_copies {G W : Type*} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) G W) (m : ℕ) (A : Subgroup G) :
    fixedCodim (copies σ m) A = m * fixedCodim σ A := by
  have he := (fixedCopiesEquiv σ m A).finrank_eq
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at he
  have hh := fixedCodim_add_finrank (copies σ m) A
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, he] at hh
  have hσ := fixedCodim_add_finrank σ A
  nlinarith

private theorem elementary_rank_le_two (A : Subgroup SL) (hA : IsElementaryAbelian 2 A) :
    rank A ≤ 2 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) ≃* SL :=
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.trans Matrix.PSL3Two.equiv.symm
  have hr : primeRank 2 SL ≤ 2 := by
    rw [← Theory.GroupTheory.primeRank_equiv 2 e, Theory.PSL2.primeField_two_rank (by decide : 3 < 7)]
  have hc := (primeRank_le_iff_elementary_card_le SL).mp hr A hA
  have hl := Nat.log_monotone (b := 2) hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hl

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) SL V} {m : ℕ}

/-- A homogeneous natural quotient of an FF-module has at most two summands. -/
theorem ModuleQuotient.multiplicity_le_two (q : ModuleQuotient ρ m) (hFF : IsFFModule ρ) :
    m ≤ 2 := by
  obtain ⟨A, hA⟩ := hFF
  let σ : Representation (ZMod 2) SL (Fin 3 → ZMod 2) :=
    (Representation.specialLinearNatural 3).comp q.marking.toMonoidHom
  have hσ : Function.Injective σ := by
    intro g k h
    apply q.marking.injective
    apply Matrix.SpecialLinearGroup.toLin'_injective
    exact LinearEquiv.toLinearMap_injective h
  have hpos := fixedCodim_pos_of_faithful σ hσ hA.1.1
  have hle := fixedCodim_le_of_equivariant_surjection ρ (copies σ m)
    q.projection q.surjective (fun g v => funext (q.equivariant g v)) A
  rw [fixedCodim_copies] at hle
  have hrank := elementary_rank_le_two A hA.1.2
  have hbound := hle.trans hA.2
  nlinarith

omit [FiniteDimensional (ZMod 2) V] in
/-- A faithful action cannot have only fixed vectors. -/
theorem ModuleQuotient.multiplicity_pos (q : ModuleQuotient ρ m)
    (hρ : Function.Injective ρ) : 0 < m := by
  by_contra! hz
  have hm : m = 0 := Nat.eq_zero_of_le_zero hz
  subst m
  have hfix (v : V) : v ∈ fixedSpace ρ ⊤ := by
    rw [← q.kernel]
    change q.projection v = 0
    exact Subsingleton.elim _ _
  have hall (g : SL) : ρ g = ρ 1 := by
    apply LinearMap.ext
    intro v
    exact (hfix v ⟨g, mem_top _⟩).trans (by simp)
  have hcard : Nat.card SL = 1 := by
    let : Subsingleton SL := ⟨fun g k => hρ ((hall g).trans (hall k).symm)⟩
    exact Nat.card_unique
  have hc := Matrix.PSL3Two.card_SL
  change Nat.card SL = 168 at hc
  omega

/-- Faithfulness and offending give the sharp one-or-two multiplicity range. -/
theorem ModuleQuotient.multiplicity_cases (q : ModuleQuotient ρ m)
    (hρ : Function.Injective ρ) (hFF : IsFFModule ρ) : m = 1 ∨ m = 2 := by
  have := q.multiplicity_pos hρ
  have := q.multiplicity_le_two hFF
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition
