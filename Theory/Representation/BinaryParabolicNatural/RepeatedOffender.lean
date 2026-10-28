module

public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.Representation.BinaryParabolicNatural.Basic
public import Theory.SpecificGroups.BinaryLinear.LineRadical
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Sylow


/-!
# Repeated natural modules and point-radical offenders

The root forms of a subgroup of a binary line radical identify its common
fixed space with their coannihilator. Thus its fixed codimension equals its
binary rank. A repeated natural module multiplies this cost by the number
of copies, while keeping one actor, so a nontrivial offender permits only
one copy. A Sylow fixes one line, whose point stabilizer has precisely that
radical as its intrinsic two-core. The last theorem combines these facts.

Source: the repeated-natural argument in Aschbacher--Smith 15.1.28,
printed pp.1102--1103, and its B.4.2 natural-module calculation.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open BinaryLinear BinaryTransvectionGroups
namespace Representation.BinaryParabolicNatural
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Each copy pays the same fixed codimension for the same actor. -/
theorem fixedCodim_copies [FiniteDimensional (ZMod 2) V]
    {H : Type*} [Group H] (ι : Type*) [Fintype ι]
    (ρ : Representation (ZMod 2) H V) (A : Subgroup H) :
    fixedCodim (copies ι ρ) A = Fintype.card ι * fixedCodim ρ A := by
  have hd := fixedCodim_add_finrank (copies ι ρ) A
  have hs := fixedCodim_add_finrank ρ A
  rw [fixed_copies, (copySpaceEquiv ι _).finrank_eq,
    Module.finrank_pi_fintype, Module.finrank_pi_fintype] at hd
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hd
  nlinarith

/-- The linear forms of a common-center subgroup detect exactly its fixed vectors. -/
theorem fixedSpace_line_radical (x : V) (hx : x ≠ 0)
    (A : Subgroup (BinaryLinear.GL V)) (hA : A ≤ radical (Submodule.span (ZMod 2) {x})) :
    BinaryOffender.fixedSpace (natural V) A = (rootForms A x).dualCoannihilator := by
  ext v
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro hv f hf
    have hh := hv ⟨transvection x f hf.1, hf.2⟩
    change v + f v • x = v at hh
    exact (smul_eq_zero.mp (add_eq_left.mp hh)).resolve_right hx
  · intro hv a
    obtain ⟨_,f,hf,he⟩ := (mem_rootGroup_iff hx).mp ⟨a.property,hA a.property⟩
    have hfA : f ∈ rootForms A x := (mem_rootForms hf).mpr (he ▸ a.property)
    change (a : BinaryLinear.GL V) v = v
    rw [he]
    change v + f v • x = v
    rw [hv f hfA,zero_smul,add_zero]

/-- A common-center subgroup has fixed codimension equal to its binary rank. -/
theorem fixedCodim_line_radical [FiniteDimensional (ZMod 2) V]
    (x : V) (hx : x ≠ 0) (A : Subgroup (BinaryLinear.GL V))
    (hA : A ≤ radical (Submodule.span (ZMod 2) {x})) :
    fixedCodim (natural V) A = rank A := by
  have he : rootGroup A x = A := inf_eq_left.mpr hA
  have hcard := rootForms_card_eq A hx
  rw [he, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hcard
  have hr : rank A = Module.finrank (ZMod 2) (rootForms A x) := by
    rw [rank, ← hcard, Nat.log_pow (by decide : 1 < 2)]
  have hd := fixedCodim_add_finrank (natural V) A
  rw [fixedSpace_line_radical x hx A hA] at hd
  have hs := Subspace.finrank_add_finrank_dualCoannihilator_eq (rootForms A x)
  omega

/-- An offender in a common-center radical permits just one natural copy. -/
theorem copies_eq_one_of_line_offender [FiniteDimensional (ZMod 2) V]
    (r : ℕ) (hr : 0 < r) (x : V) (hx : x ≠ 0)
    (A : Subgroup (BinaryLinear.GL V)) (hA : A ≤ radical (Submodule.span (ZMod 2) {x}))
    (ho : IsOffender (copies (Fin r) (natural V)) A) : r = 1 := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hp := ho.1.rank_pos
  have hb := ho.2
  rw [fixedCodim_copies, Fintype.card_fin, fixedCodim_line_radical x hx A hA] at hb
  nlinarith

/-- Positive repetition leaves the pointwise stabilizer of a fixed space unchanged. -/
theorem copies_fixedCentralizer (r : ℕ) (hr : 0 < r)
    {H : Type*} [Group H] (ρ : Representation (ZMod 2) H V) (A : Subgroup H) :
    subspaceKernel (copies (Fin r) ρ) (BinaryOffender.fixedSpace (copies (Fin r) ρ) A) ⊤ =
      subspaceKernel ρ (BinaryOffender.fixedSpace ρ A) ⊤ := by
  ext g
  constructor
  · rintro ⟨hg,hfix⟩
    refine ⟨hg,fun v hv => ?_⟩
    have hconst : (fun _ : Fin r => v) ∈ BinaryOffender.fixedSpace (copies (Fin r) ρ) A :=
      fun a => funext (fun _ => hv a)
    exact congrFun (hfix _ hconst) ⟨0,hr⟩
  · rintro ⟨hg,hfix⟩
    refine ⟨hg,fun v hv => ?_⟩
    funext i
    exact hfix (v i) (fun a => congrFun (hv a) i)

/-- The natural Sylow-fixed centralizer is the stabilizer of its unique fixed point. -/
theorem sylow_fixedCentralizer [Finite V] [FiniteDimensional (ZMod 2) V]
    (hd : 0 < Module.finrank (ZMod 2) V) (R : Sylow 2 (BinaryLinear.GL V)) :
    ∃ x : V, x ≠ 0 ∧
      subspaceKernel (natural V) (BinaryOffender.fixedSpace (natural V) R) ⊤ =
        parabolic (Submodule.span (ZMod 2) {x}) := by
  obtain ⟨x,hx,hfix⟩ := BinaryNaturalDual.VectorStabilizers.Pure.linear_sylow_fixed_line hd R
  have he : BinaryOffender.fixedSpace (natural V) R = BinaryLinear.fixedSpace R := by
    ext v
    exact ⟨fun h g hg => h ⟨g,hg⟩,fun h g => h g g.property⟩
  refine ⟨x,hx,?_⟩
  rw [he,hfix,BinaryNaturalDual.VectorStabilizers.Pure.parabolic_line_eq hx]
  ext g
  constructor
  · intro hg
    exact hg.2 x (Submodule.mem_span_singleton_self x)
  · intro hg
    refine ⟨mem_top _,?_⟩
    intro v hv
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
    change g (a • x) = a • x
    rw [map_smul,show g x = x from hg]

/-- The original intrinsic two-core becomes the line radical, on all copies. -/
theorem copies_sylow_core [Finite V] [FiniteDimensional (ZMod 2) V]
    (hd : 0 < Module.finrank (ZMod 2) V) (R : Sylow 2 (BinaryLinear.GL V))
    (r : ℕ) (hr : 0 < r) :
    ∃ x : V, x ≠ 0 ∧
      (subspaceKernel (copies (Fin r) (natural V))
        (BinaryOffender.fixedSpace (copies (Fin r) (natural V)) R) ⊤).pCoreIn 2 =
          radical (Submodule.span (ZMod 2) {x}) := by
  obtain ⟨x,hx,he⟩ := sylow_fixedCentralizer hd R
  refine ⟨x,hx,?_⟩
  rw [copies_fixedCentralizer r hr,he]
  exact BinaryLinear.SmallParabolicLevi.map_twoCore_eq_radical _

/-- A Sylow-fixed-centralizer core cannot offend on multiple natural copies. -/
theorem copies_eq_one_of_sylow_core_offender [Finite V] [FiniteDimensional (ZMod 2) V]
    (hd : 0 < Module.finrank (ZMod 2) V) (R : Sylow 2 (BinaryLinear.GL V))
    (r : ℕ) (hr : 0 < r) (A : Subgroup (BinaryLinear.GL V))
    (ho : IsOffender (copies (Fin r) (natural V)) A)
    (hA : A ≤ (subspaceKernel (copies (Fin r) (natural V))
      (BinaryOffender.fixedSpace (copies (Fin r) (natural V)) R) ⊤).pCoreIn 2) : r = 1 := by
  obtain ⟨x,hx,he⟩ := copies_sylow_core hd R r hr
  rw [he] at hA
  exact copies_eq_one_of_line_offender r hr x hx A hA ho
end Representation.BinaryParabolicNatural
