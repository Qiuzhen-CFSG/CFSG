module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank.PureIntersections
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Normalization
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.Offenders

/-!
# Fixed spaces in the first-stage conjugate configuration

The actual offender image is unchanged by restricting to its normalizing
part. For a pure invariant summand, displacements of vectors in the reverse
normalizer lie in the pure intersection with the conjugate and hence vanish.
E.3.32 therefore restricts the generated core on each summand. At image rank
n-1 every nonidentity cyclic fixed space belongs to that core.
Source: Aschbacher--Smith, 12.1.8, printed pp.792--793 (PDF809--810).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
variable {G : Type*} [Group G] {W : Subgroup G} [IsElementaryAbelian 2 W]

omit [IsElementaryAbelian 2 W] in
/-- Restricting to the actual normalizing part does not change the action image. -/
theorem induced_offender_eq (g : G) :
    inducedAutomizer W (offenderNormalizer W g) =
      inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom) := by
  unfold inducedAutomizer offenderNormalizer
  congr 1
  ext x
  exact ⟨fun h => h.1, fun h => ⟨h,x.property⟩⟩

/-- Pure-intersection vanishing applies to any summand invariant under the
chosen subactor, including the dual summand. -/
theorem pure_normalizer_le_fixed (P : Submodule (ZMod 2) (Additive W))
    (g : G) (J : Subgroup (Automizer W))
    (hJ : J ≤ inducedAutomizer W (offenderNormalizer W g))
    (hinv : ∀ a : J, ∀ u ∈ P, automizerRepresentation W a u ∈ P)
    (hz : P ⊓ subgroupSpace W (W.map (MulAut.conj g).toMonoidHom) = ⊥) :
    P ⊓ subgroupSpace W (normalizer (W.map (MulAut.conj g).toMonoidHom : Set G)) ≤
      fixedSpace (automizerRepresentation W) J := by
  intro u hu a
  have hd : automizerRepresentation W a u - u ∈
      P ⊓ subgroupSpace W (W.map (MulAut.conj g).toMonoidHom) := by
    refine ⟨P.sub_mem (hinv a u hu.1) hu.1, ?_⟩
    obtain ⟨b,hb,he⟩ := hJ a.property
    apply (mem_subgroupSpace W _ _).mpr
    rw [← he, toMul_sub, div_eq_mul_inv]
    change (b : G) * (u.toMul : G) * (b : G)⁻¹ * (u.toMul : G)⁻¹ ∈ _
    have hnorm := (mem_subgroupSpace W _ u).mp hu.2
    have hconj := (mem_normalizer_iff.mp hnorm) (b : G)⁻¹
    have hinv := (W.map (MulAut.conj g).toMonoidHom).inv_mem hb.1
    have hh := (W.map (MulAut.conj g).toMonoidHom).mul_mem hb.1 (hconj.mp hinv)
    simpa only [Subgroup.subtype_apply, mul_assoc] using hh
  rw [hz] at hd
  exact sub_eq_zero.mp hd

variable [Finite G]

/-- The corank n−2 core contains each nonidentity cyclic fixed space when
the offender image has rank n−1. -/
theorem cyclic_fixed_le_core {K X : Type*} [Group K] [Finite K]
    [IsElementaryAbelian 2 K] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) K X) (a : K) (ha : a ≠ 1) :
    fixedSpace ρ (zpowers a) ≤
      BinaryNaturalDual.generatedCore ρ (Nat.log 2 (Nat.card K) - 1) := by
  have ho : orderOf a = 2 := orderOf_eq_prime
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 K) a) ha
  have he := (zpowers a).index_mul_card
  rw [Nat.card_zpowers, ho] at he
  have hl := congrArg (Nat.log 2) he
  rw [Nat.log_mul_base (by decide) (zpowers a).index_ne_zero_of_finite] at hl
  apply BinaryNaturalDual.fixedSpace_le_generatedCore
  omega

omit [Finite G] in
/-- In the first-stage conjugate configuration the E.3.32 core satisfies
the fixed-space restriction on every pure invariant summand. -/
theorem pure_core_le_fixed {n : ℕ} {g : G}
    (C : ConjugateConfiguration W g 1 n)
    (hn : 2 ≤ n) (P : Submodule (ZMod 2) (Additive W))
    (J : Subgroup (Automizer W))
    (hJ : J ≤ inducedAutomizer W (offenderNormalizer W g))
    (hinv : ∀ a : J, ∀ u ∈ P, automizerRepresentation W a u ∈ P)
    (hz : P ⊓ subgroupSpace W (W.map (MulAut.conj g).toMonoidHom) = ⊥) :
    P ⊓ BinaryNaturalDual.generatedCore
      ((automizerRepresentation W).comp
        (inducedAutomizer W (offenderNormalizer W g)).subtype) (n-2) ≤
      fixedSpace (automizerRepresentation W) J := by
  apply le_trans _ (pure_normalizer_le_fixed P g J hJ hinv hz)
  apply inf_le_inf_left
  intro u hu
  exact (mem_subgroupSpace W _ u).mpr
    (C.core_le (n-2) (by omega) ((ZeroClosure.mem_core_iff _ _ u).mpr hu)).2

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.LowRank
