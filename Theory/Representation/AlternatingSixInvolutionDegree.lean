module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.Representation.BinaryAlternatingSixSmallDegrees
public import Theory.Representation.BinaryOffender.ConjugateDisplacement
public import Theory.Representation.NormalInvariants
public import Mathlib.Tactic.FinCases

/-!
# Involution displacement in binary A₆ modules

Three double transpositions generate the actual alternating group on six
letters: four short words give its standard Suzuki generators. Since all
A₆ involutions are conjugate, any involution has three conjugates generating
A₆. Their displacement maps embed a faithful irreducible module into three
copies of its involution displacement space. Rank two therefore bounds the
module dimension by six, and the binary small-degree theorem leaves only
one or four, excluding the dimension range used by the Chapter 15 source.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.58, printed p.1149; the displacement estimate is the standard
conjugate-generator bound recorded in `BinaryOffender.ConjugateDisplacement`.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open GLS3.Chapter5.SchurPresentation
namespace AlternatingSix.InvolutionDisplacement
open AlternatingSix.ShadowLocal (A6)

private def generators : Fin 3 → A6 := ![
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
  ⟨Equiv.swap 0 1 * Equiv.swap 2 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
  ⟨Equiv.swap 0 2 * Equiv.swap 1 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩]

private def words : Fin 4 → List (Fin 3) := ![
  [0, 1, 2, 1, 0, 2, 1], [0], [0, 1, 0], [0, 1, 2, 0, 1, 0, 2, 1]]

private theorem word_eq (i : Fin 4) :
    alternatingSuzukiGenerator 1 i = ((words i).map generators).prod := by
  apply Subtype.ext
  rw [alternatingSuzukiGenerator_val]
  fin_cases i <;> decide

private theorem generators_generate : closure (Set.range generators) = ⊤ := by
  apply top_unique
  rw [← alternatingSuzukiGenerator_closure_eq_top 1]
  apply (closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  rw [word_eq]
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
  exact subset_closure (Set.mem_range_self j)

/-- Three conjugates of any involution generate the actual six-point alternating group. -/
theorem exists_three_conjugate_generators (t : A6) (ht : orderOf t = 2) :
    ∃ c : Fin 3 → A6, closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤ := by
  have ho (i : Fin 3) : orderOf (generators i) = 2 := by
    apply orderOf_eq_prime
    · revert i; decide
    · revert i; decide
  choose c hc using fun i => isConj_iff.mp
    (AlternatingSix.ShadowLocal.involutions_isConj t (generators i) ht (ho i))
  exact ⟨c, by simpa only [hc] using generators_generate⟩

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- Rank-two involution movement bounds the degree of a faithful simple binary A₆-module. -/
theorem finrank_le_six (σ : Representation (ZMod 2) A6 W) [σ.IsIrreducible]
    (hf : Function.Injective σ) (t : A6) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (σ t - LinearMap.id)) = 2) :
    Module.finrank (ZMod 2) W ≤ 6 := by
  have hfix : fixedSpace σ (⊤ : Subgroup A6) = ⊥ := by
    by_contra hn
    have hn' : Representation.invariants (σ.comp (⊤ : Subgroup A6).subtype) ≠ ⊥ := hn
    have hk := σ.le_ker_of_normal_invariants_ne_bot ⊤ hn'
    have he : t = 1 := hf ((MonoidHom.mem_ker.mp (hk (mem_top t))).trans (map_one σ).symm)
    simp [he] at ht
  obtain ⟨c, hc⟩ := exists_three_conjugate_generators t ht
  have hb := finrank_le_mul_fixedCodim_of_conjugate_generation σ ⊤ hfix t c hc.ge
  rw [fixedCodim_zpowers_eq_displacement_rank, hr] at hb
  exact hb

/-- A faithful simple binary A₆-module with rank-two movement cannot have degree at least six. -/
theorem not_six_le_finrank (σ : Representation (ZMod 2) A6 W) [σ.IsIrreducible]
    (hf : Function.Injective σ) (t : A6) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (σ t - LinearMap.id)) = 2) :
    ¬ 6 ≤ Module.finrank (ZMod 2) W := by
  have hd := finrank_le_six σ hf t ht hr
  have ha := AlternatingSix.BinarySmallDegrees.finrank_eq_one_or_four σ hd
  omega


end AlternatingSix.InvolutionDisplacement
