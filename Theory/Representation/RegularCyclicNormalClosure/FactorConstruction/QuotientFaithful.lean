module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.MaximalIntersection
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Faithfulness of the pointwise-fixer quotient

The kernel of the action on W/F consists of shears fixing F pointwise.
A shear preserves the original fixed space, hence normalizes its cyclic
actor and preserves its moved space. Since its displacement is in F, it
fixes the moved space. The remaining rank is at most dim(U/F), and the
ambient involution bound excludes a nonidentity shear.

This proves faithfulness for the maximal-intersection quotient used in the
local approach to Aschbacher–Smith E.6.24, printed p.255. It does not assume
that the ambient involution rank bound descends to the quotient.
-/

public section

open Module Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure
namespace FactorConstruction
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) A W)

/-- The quotient action of the actual pointwise fixer. -/
@[expose] def quotientOnFixer (F : Submodule (ZMod 2) W) :
    Representation (ZMod 2) (pointwiseFixer ρ F) (W ⧸ F) :=
  Representation.quotient (ρ.comp (pointwiseFixer ρ F).subtype) F (by
    intro g v hv
    change ρ (g : A) v ∈ F
    rw [(mem_pointwiseFixer ρ F g).mp g.property v hv]
    exact hv)

@[simp] theorem quotientOnFixer_mkQ (F : Submodule (ZMod 2) W)
    (g : pointwiseFixer ρ F) (v : W) :
    quotientOnFixer ρ F g (F.mkQ v) = F.mkQ (ρ (g : A) v) := rfl

end FactorConstruction
open FactorConstruction
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- A shear fixing F, with F in the actor's fixed space, fixes the moved
space. Normalization follows from its preservation of the fixed space. -/
theorem Input.shear_fixes_moved (h : Input ρ C) (F : Submodule (ZMod 2) W)
    (hFU : F ≤ fixedSpace ρ C) (q : A)
    (hQ : ∀ v : W, ρ q v - v ∈ F) :
    ∀ v ∈ displacementSpan ρ C ⊤, ρ q v = v := by
  have hU : (fixedSpace ρ C).map (ρ q) ≤ fixedSpace ρ C := by
    rintro _ ⟨v, hv, rfl⟩
    have he := (fixedSpace ρ C).add_mem (hFU (hQ v)) hv
    simpa only [sub_add_cancel] using he
  have hUeq : (fixedSpace ρ C).map (ρ q) = fixedSpace ρ C :=
    Submodule.eq_of_le_of_finrank_eq hU
      (Submodule.equivMapOfInjective (ρ q) (ρ.apply_bijective q).injective
        (fixedSpace ρ C)).finrank_eq.symm
  have hnorm := h.normal_in_stabilizer q hUeq
  have hS := displacementSpan_map_of_normalized ρ C q hnorm
  intro v hv
  have hv' : ρ q v ∈ displacementSpan ρ C ⊤ := by
    rw [← hS]
    exact Submodule.mem_map_of_mem hv
  exact sub_eq_zero.mp (Submodule.disjoint_def.mp h.split.disjoint _
    (hFU (hQ v)) ((displacementSpan ρ C ⊤).sub_mem hv' hv))

/-- The pointwise-fixer quotient is faithful when the remaining dimension
of the original fixed space does not exceed the moved dimension. No bound
on involutions of the quotient is assumed. -/
theorem Input.quotientOnFixer_faithful (h : Input ρ C)
    (F : Submodule (ZMod 2) W) (hFU : F ≤ fixedSpace ρ C)
    (hsmall : finrank (ZMod 2) (fixedSpace ρ C) ≤ finrank (ZMod 2) F +
      finrank (ZMod 2) (displacementSpan ρ C ⊤)) :
    Function.Injective (quotientOnFixer ρ F) := by
  apply (injective_iff_map_eq_one _).mpr
  intro q hq
  have hfix : ∀ v ∈ F, ρ (q : A) v = v := (mem_pointwiseFixer ρ F q).mp q.property
  have hQ (v : W) : ρ (q : A) v - v ∈ F := by
    have he := congrArg (fun f : Module.End (ZMod 2) (W ⧸ F) => f (F.mkQ v)) hq
    change F.mkQ (ρ (q : A) v) = F.mkQ v at he
    exact (Submodule.Quotient.eq F).mp he
  have hS := h.shear_fixes_moved F hFU q hQ
  have hchar (v : W) : v + v = 0 := by
    have he : (1 + 1 : ZMod 2) = 0 := by decide
    simpa only [add_smul, one_smul, zero_smul] using congrArg (fun r => r • v) he
  have hsq : (q : A) ^ 2 = 1 := by
    apply h.faithful
    ext v
    have he := hfix (ρ (q : A) v - v) (hQ v)
    change ρ (q : A) (ρ (q : A) v - v) = ρ (q : A) v - v at he
    rw [map_sub, sub_eq_iff_eq_add] at he
    simp only [pow_two, map_mul, Module.End.mul_apply, map_one, Module.End.one_apply]
    calc
      _ = (ρ (q : A) v - v) + ρ (q : A) v := he
      _ = (ρ (q : A) v + ρ (q : A) v) - v := by abel
      _ = v := by
        rw [hchar, zero_sub]
        exact neg_eq_iff_add_eq_zero.mpr (hchar v)
  by_contra hne
  have hneA : (q : A) ≠ 1 := fun he => hne (Subtype.ext he)
  have hord : orderOf (q : A) = 2 := orderOf_eq_prime hsq hneA
  have hFS : F ⊔ displacementSpan ρ C ⊤ ≤ fixedSpace ρ (zpowers (q : A)) := by
    apply sup_le
    · intro v hv
      exact (mem_fixedSpace_zpowers_iff ρ q v).mpr (hfix v hv)
    · intro v hv
      exact (mem_fixedSpace_zpowers_iff ρ q v).mpr (hS v hv)
  have hdis : Disjoint F (displacementSpan ρ C ⊤) := h.split.disjoint.mono_left hFU
  have hdim := F.finrank_sup_add_finrank_inf_eq (displacementSpan ρ C ⊤)
  rw [hdis.eq_bot, finrank_bot, add_zero] at hdim
  have hle := Submodule.finrank_mono hFS
  have hsplit := Submodule.finrank_add_eq_of_isCompl h.split
  have hr := fixedCodim_add_finrank ρ (zpowers (q : A))
  have hbound := h.no_small_involutions (q : A) hord
  omega

end Representation.RegularCyclicNormalClosure
