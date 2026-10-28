module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryResidual
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryImage

/-!
# The actual natural action on a quadratic conjugate displacement

If [A,B] centralizes B, each map b ↦ [a,b] is a homomorphism from B to
[A,B]. Relative normality of the field residual makes these maps equivariant.
A noncentralizing A supplies a nonzero map. Since B is two natural copies,
a displacement of one-copy order is natural, even when it lies outside B.
This gives the representation step needed for the conjugate line in 6.1.14(5).

The Sylow and local-component arguments still have to supply relative
normality and the quadratic line geometry. Their final assembly owner is
qt-d-1222-rankone-recognition-natural-contained.
Source: Aschbacher–Smith, printed pp.671–672.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G]

/-- Quadratic displacement is a homomorphism into the literal commutator. -/
def quadraticDisplacement (A B : Subgroup G)
    (hc : ⁅A, B⁆ ≤ centralizer (B : Set G)) (a : A) : B →* (⁅A, B⁆ : Subgroup G) where
  toFun b := ⟨⁅(a : G), (b : G)⁆, commutator_mem_commutator a.property b.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' b c := by
    apply Subtype.ext
    change ⁅(a : G), (b : G) * (c : G)⁆ = ⁅(a : G), (b : G)⁆ * ⁅(a : G), (c : G)⁆
    have hh := (mem_centralizer_iff.mp (hc (commutator_mem_commutator a.property c.property))
      b b.property)
    rw [commutatorElement_mul_right_eq_mul_conj]
    calc
      _ = ⁅(a : G), (b : G)⁆ * ((b : G) * ⁅(a : G), (c : G)⁆) * (b : G)⁻¹ := by group
      _ = _ := by rw [hh]; group

/-- An actor commuting with A modulo C_G(B) intertwines each displacement. -/
theorem quadraticDisplacement_equivariant (K A B : Subgroup G)
    (hAK : ⁅A, K⁆ ≤ centralizer (B : Set G))
    (hc : ⁅A, B⁆ ≤ centralizer (B : Set G)) (a : A)
    (k : K) (b b' : B) (hb : (b' : G) = (k : G) * (b : G) * (k : G)⁻¹) :
    (quadraticDisplacement A B hc a b' : G) =
      (k : G) * (quadraticDisplacement A B hc a b : G) * (k : G)⁻¹ := by
  have hcb : ⁅⁅(a : G)⁻¹, (k : G)⁆, (b' : G)⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (mem_centralizer_iff.mp
      (hAK (commutator_mem_commutator (A.inv_mem a.property) k.property)) b' b'.property).symm
  change ⁅(a : G), (b' : G)⁆ = (k : G) * ⁅(a : G), (b : G)⁆ * (k : G)⁻¹
  rw [conjugate_commutatorElement, ← hb]
  have hk : (k : G) * (a : G) * (k : G)⁻¹ = (a : G) * ⁅(a : G)⁻¹, (k : G)⁆ := by
    simp [commutatorElement_def, mul_assoc]
  rw [hk, commutatorElement_mul_left_eq_conj_mul, hcb]
  simp

/-- A noncentralizing conjugate supplies a nonzero individual displacement. -/
theorem quadraticDisplacement_nonzero (A B : Subgroup G)
    (hc : ⁅A, B⁆ ≤ centralizer (B : Set G))
    (hnon : ¬ A ≤ centralizer (B : Set G)) :
    ∃ a : A, ∃ b : B, quadraticDisplacement A B hc a b ≠ 1 := by
  by_contra! hz
  apply hnon
  intro a ha
  apply mem_centralizer_iff.mpr
  intro b hb
  have hh := congrArg (fun x : (⁅A, B⁆ : Subgroup G) => (x : G)) (hz ⟨a,ha⟩ ⟨b,hb⟩)
  exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G] {L M B U A : Subgroup G} {n : ℕ}

/-- A quadratic conjugate displacement of the source order is natural,
without requiring that it be contained in the original layer. -/
theorem field_fixedSpace_displacement_natural
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) (hn : 2 < n)
    (hN : ((fieldLocalResidual L U).subgroupOf (normalizer (U : Set G))).Normal)
    (hA : A ≤ centralizer (U : Set G))
    (hquad : ⁅A, B⁆ ≤ centralizer (B : Set G))
    (hcard : Nat.card (⁅A, B⁆ : Subgroup G) = 2 ^ n)
    (hnon : ¬ A ≤ centralizer (B : Set G)) :
    ∃ m, n = 2 * m ∧ IsNaturalModule (fieldLocalResidual L U) ⁅A, B⁆ m := by
  obtain ⟨m, hnm, _, hRU⟩ := field_fixedSpace_natural hn hnatural hfield hUne
  obtain ⟨e, he⟩ := field_fixedSpace_double_equiv hnatural hfield hUne
  have hUcard : Nat.card U = 2 ^ n := by
    rw [hRU.card, Nat.mul_comm m 2, ← hnm]
  have hKL : fieldLocalResidual L U ≤ L := (map_subtype_le _).trans inf_le_left
  have hKB : fieldLocalResidual L U ≤ normalizer (B : Set G) := by
    obtain ⟨_, _, _, _, _, hmodel⟩ := hnatural
    exact hKL.trans hmodel.normalizes
  have hKAB := field_fixedSpace_residual_normalizes_displacement hnatural hfield hUne hn hN hA
  have hAK : ⁅A, fieldLocalResidual L U⁆ ≤ centralizer (B : Set G) :=
    ((commutator_mono hA le_rfl).trans
      (field_fixedSpace_centralizer_commutator hnatural hfield hUne hn hN)).trans
        (field_fixedSpace_core_centralizes hnatural hfield hUne hn).2
  obtain ⟨a, ha⟩ := quadraticDisplacement_nonzero A B hquad hnon
  refine ⟨m, hnm, natural_of_nonzero_double_image hRU hKAB
    (hcard.trans hUcard.symm) e (fun k b b' hb => he (inclusion (map_subtype_le _) k) b b' hb)
    hKB (quadraticDisplacement A B hquad a) ha ?_⟩
  exact quadraticDisplacement_equivariant _ _ _ hAK hquad a
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
