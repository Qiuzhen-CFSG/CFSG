module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SuzukiCentralizer
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorModels
public import Theory.Representation.BinaryOffender.PerfectIrreducibleCentralizer

/-!
# The two-factor FF case in a Suzuki centralizer

Assume the actual offender action has zero fixed space. Its literal quotient
map is then injective, so the source markings on the two-factor quotient
transport to the original prescribed subspaces. Natural linear factors are
excluded by the commuting perfect action and Schur's lemma. Two natural
three-spaces are excluded by the Suzuki multiplicity calculation. The
symmetric-five and exceptional four-dimensional factors contradict the
lower bound for the original moved space.

No constituent replaces the quotient and no fixed summand is dropped.
Chapter 10's SuzukiExclusion proves the zero fixed-space premise from
normality and the original full-action irreducibility.
Source: Aschbacher–Smith B.5.6(3a–c), p.105, and 10.1.1, p.741.
-/

public noncomputable section
open scoped MonoidAlgebra
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource ExtensionConsequences BenderSuzuki.MatrixGroups

variable {Q D V : Type*} [Group Q] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private def fixedImageEquiv (σ : Representation (ZMod 2) D V)
    (hz : σ.invariants = ⊥) (A : Subgroup D) (U : Subrepresentation σ) :
    ActionEquiv (U.toRepresentation.comp A.subtype)
      (((fixed σ).quotientImage U).toRepresentation.comp A.subtype) where
  groupEquiv := MulEquiv.refl A
  linearEquiv := Submodule.equivMapOfInjective σ.invariants.mkQ
    (by apply LinearMap.ker_eq_bot.mp; rw [Submodule.ker_mkQ,hz]) U.toSubmodule
  intertwines _ _ := rfl

private def fixedImageMarking (σ : Representation (ZMod 2) D V)
    (hz : σ.invariants = ⊥) (A : Subgroup D) (U : Subrepresentation σ)
    {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    {τ : Representation (ZMod 2) H W}
    (e : ActionEquiv (((fixed σ).quotientImage U).toRepresentation.comp A.subtype) τ) :
    ActionEquiv (U.toRepresentation.comp A.subtype) τ where
  groupEquiv := e.groupEquiv
  linearEquiv := (fixedImageEquiv σ hz A U).linearEquiv.trans e.linearEquiv
  intertwines a v :=
    (congrArg e.linearEquiv ((fixedImageEquiv σ hz A U).intertwines a v)).trans
      (e.intertwines a _)

private theorem no_irreducible_moved
    (ρ : Representation (ZMod 2) Q V) (S : Subgroup Q) [Group.IsPerfect S]
    (hfix : fixedSpace ρ S = ⊥)
    (f : D →* Q) (hc : f.range ≤ centralizer (S : Set Q))
    (A : Subgroup D) (U : Subrepresentation (ρ.comp f))
    (hu : U.toSubmodule = moved (ρ.comp f) A)
    (hi : IsIrreducible (U.toRepresentation.comp A.subtype)) : False := by
  let W := U.toSubmodule
  have hs : S ≤ subspaceStabilizer ρ W := by
    dsimp only [W]
    rw [hu]
    change S ≤ subspaceStabilizer ρ (subspaceCommutator (ρ.comp f) ⊤ A)
    rw [subspaceCommutator_comp_map]
    exact subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      ((le_centralizer_iff.mp ((map_le_range f A).trans hc)).trans (Subgroup.centralizer_le_normalizer _))
  let τ := (stabilizerRepresentation ρ W).comp (inclusion hs)
  let α := U.toRepresentation.comp A.subtype
  let := hi
  have ht := perfect_commuting_irreducible α τ (by
    intro a s
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ρ s (ρ (f a) v) = ρ (f a) (ρ s v)
    rw [← Module.End.mul_apply,←map_mul,← Module.End.mul_apply,←map_mul]
    exact LinearMap.congr_fun (congrArg ρ (hc (MonoidHom.mem_range.mpr ⟨a,rfl⟩) s s.property)) v)
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial α
  obtain ⟨v,hv⟩ := exists_ne (0:W)
  apply hv
  apply Subtype.ext
  apply hfix.le
  intro s
  exact congrArg Subtype.val (ht s v)

omit [FiniteDimensional (ZMod 2) V] in
private theorem no_doubled_moved
    (ρ : Representation (ZMod 2) Q V) (S : Subgroup Q)
    {m : ℕ} (hm : 0<m) (eS : S ≃* SuzukiMatrixGroup m)
    (hfix : fixedSpace ρ S = ⊥)
    (f : D →* Q) (hc : f.range ≤ centralizer (S : Set Q))
    (A : Subgroup D) (U : Subrepresentation (ρ.comp f))
    (hu : U.toSubmodule = moved (ρ.comp f) A)
    (F : BinaryField)
    (e : ActionEquiv (U.toRepresentation.comp A.subtype) (repeated (linearNatural F 3) 2)) : False := by
  let W := U.toSubmodule
  have hs : S ≤ subspaceStabilizer ρ W := by
    dsimp only [W]
    rw [hu]
    change S ≤ subspaceStabilizer ρ (subspaceCommutator (ρ.comp f) ⊤ A)
    rw [subspaceCommutator_comp_map]
    exact subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      ((le_centralizer_iff.mp ((map_le_range f A).trans hc)).trans (Subgroup.centralizer_le_normalizer _))
  let τ := ((stabilizerRepresentation ρ W).comp (inclusion hs)).comp eS.symm.toMonoidHom
  let α := (U.toRepresentation.comp A.subtype).comp e.groupEquiv.symm.toMonoidHom
  have hcomm (a : SuzukiMatrixGroup m) (b : Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
      (v : W) : τ a (α b v) = α b (τ a v) := by
    apply Subtype.ext
    change ρ (eS.symm a) (ρ (f (e.groupEquiv.symm b)) v) =
      ρ (f (e.groupEquiv.symm b)) (ρ (eS.symm a) v)
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    exact LinearMap.congr_fun (congrArg ρ
      (hc (MonoidHom.mem_range.mpr ⟨(e.groupEquiv.symm b : D),rfl⟩)
        (eS.symm a) (eS.symm a).property)) v
  have he (b : Matrix.SpecialLinearGroup (Fin 3) F.Carrier) (v : W) :
      e.linearEquiv (α b v) = SL3DoubledNaturalOffenders.representation F.Carrier b (e.linearEquiv v) := by
    have hh := e.intertwines (e.groupEquiv.symm b) v
    rw [e.groupEquiv.apply_symm_apply] at hh
    exact hh
  have ht := Suzuki.doubled_natural_commuting_trivial_of_coordinates hm τ α hcomm e.linearEquiv he
  have hzero (v : W) : v = 0 := by
    apply Subtype.ext
    apply hfix.le
    intro s
    have hh := congrArg Subtype.val (ht (eS s) v)
    change ρ (eS.symm (eS s)) v = v at hh
    rw [eS.symm_apply_apply] at hh
    exact hh
  let : Nontrivial W := e.linearEquiv.toEquiv.nontrivial
  obtain ⟨v,hv⟩ := exists_ne (0:W)
  exact hv (hzero v)

/-- The literal B.5 two-factor quotient is impossible for a commuting Suzuki
component when the offender action has no fixed vectors and large moved spaces. -/
theorem not_twoFactors_of_commuting_suzuki
    (ρ : Representation (ZMod 2) Q V) (S : Subgroup Q) [Group.IsPerfect S]
    {m : ℕ} (hm : 0<m) (eS : S ≃* SuzukiMatrixGroup m)
    (hfix : fixedSpace ρ S = ⊥)
    (f : D →* Q) (hc : f.range ≤ centralizer (S : Set Q))
    (hz : Representation.invariants (ρ.comp f) = ⊥)
    (hdegree : ∀ A : Subgroup D, A ≠ ⊥ →
      24 ≤ Module.finrank (ZMod 2) (moved (ρ.comp f) A))
    (c : SourceTwoFactorCase (ρ.comp f)) : False := by
  let σ := ρ.comp f
  let A := c.first
  let U := c.firstSpace
  let E := (fixed σ).quotientImage U
  let eU := fixedImageEquiv σ hz A U
  have hdU := eU.linearEquiv.finrank_eq
  let : Nontrivial A := c.firstCase.nontrivial
  have hA : A ≠ ⊥ := (nontrivial_iff_ne_bot A).mp inferInstance
  have hd := hdegree A hA
  have hle : moved σ A ≤ U.toSubmodule := by
    cases c.firstCase with
    | natural he _ => exact he.ge
    | doubleNatural _ _ he _ => exact he.ge
    | exceptional he _ => exact he
  have hdim : 24 ≤ Module.finrank (ZMod 2) U.toSubmodule :=
    hd.trans (Submodule.finrank_mono hle)
  have hdimE : 24 ≤ Module.finrank (ZMod 2) E.toSubmodule := by
    rwa [← hdU]
  cases c.firstCase with
  | natural hu hn =>
    cases hn with
    | linearTwo F hn =>
      obtain ⟨e⟩ := hn
      exact no_irreducible_moved ρ S hfix f hc A U hu
        (irreducible_of_equiv (fixedImageMarking σ hz A U e) (linearNatural_irreducible F (by decide : 2 ≤ 2)))
    | linearThree F ho hn =>
      obtain ⟨e⟩ := hn
      exact no_irreducible_moved ρ S hfix f hc A U hu
        (irreducible_of_equiv (fixedImageMarking σ hz A U e) (linearNatural_irreducible F (by decide : 2 ≤ 3)))
    | symmetricFive hn =>
      obtain ⟨e⟩ := hn
      have he := e.linearEquiv.finrank_eq
      change Module.finrank (ZMod 2) E.toSubmodule =
        Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 5)) at he
      rw [BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)] at he
      simp only [Fintype.card_fin] at he
      omega
  | doubleNatural F ho hu hn =>
    obtain ⟨e⟩ := hn
    exact no_doubled_moved ρ S hm eS hfix f hc A U hu F (fixedImageMarking σ hz A U e)
  | exceptional hu d =>
    have he := d.dimension
    change Module.finrank (ZMod 2) E.toSubmodule = 4 at he
    omega

end CFSG.Quasithin.ChapterB.SourceInduction
