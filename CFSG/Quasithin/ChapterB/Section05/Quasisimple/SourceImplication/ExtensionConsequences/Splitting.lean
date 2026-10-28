module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeLargeField

/-!
# Splitting the nonexceptional repeated-natural branches

Coordinate cocycles show that H¹ vanishes on any finite sum when it vanishes
on one summand. The connecting class of the literal moved space then supplies
a fixed supplement. The transvection calculation gives disjointness. This
proves full direct sums for the repeated binary modules of dimension at least
four, doubled SL₃ modules over fields larger than two, and natural-plus-dual
modules. The binary SL₃ endpoint requires a separate offender argument.

All cohomology inputs here are proved, including the defining-field to binary
scalar restriction. Source: Aschbacher–Smith, combined manuscript (1 March
2004), I.1.6(4),(6), printed p.408, and B.5.1(2)–(5), printed pp.102–103.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

theorem fixedSpace_top : fixedSpace ρ ⊤ = ρ.invariants := by
  ext v
  exact ⟨fun h g => h ⟨g, Subgroup.mem_top _⟩, fun h g => h g⟩

theorem H1_repeated_subsingleton (r : ℕ) [Subsingleton (H1 ρ)] :
    Subsingleton (H1 (repeated ρ r)) := by
  classical
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro f _
  let c (i : Fin r) : cocycles ρ :=
    ⟨fun g => f.val g i, fun g h => congrFun (f.property g h) i⟩
  have hc (i : Fin r) : ∃ v, principal ρ v = c i :=
    (classMap_eq_zero_iff ρ (c i)).mp (Subsingleton.elim _ _)
  choose v hv using hc
  refine ⟨v, ?_⟩
  apply Subtype.ext
  funext g i
  exact congrArg (fun t : cocycles ρ => t.val g) (hv i)

theorem moved_disjoint_fixed {L : Subgroup G} (s : MovedSection ρ L)
    (hz : Representation.invariants (s.space.toRepresentation.comp L.subtype) = ⊥) :
    Disjoint s.space.toSubmodule (fixedSpace ρ L) := by
  rw [disjoint_iff]
  apply bot_unique
  intro v hv
  have h : (⟨v, hv.1⟩ : s.space.toSubmodule) ∈
      Representation.invariants (s.space.toRepresentation.comp L.subtype) :=
    fun g => Subtype.ext (hv.2 g)
  rw [hz] at h
  exact congrArg Subtype.val h

theorem repeated_isCompl {L : Subgroup G} (s : MovedSection ρ L)
    (F : BinaryField) {d r : ℕ} (hd : 2 ≤ d) (hL : L = ⊤)
    (e : ActionEquiv (s.space.toRepresentation.comp L.subtype)
      (repeated (linearNatural F d) r))
    [Subsingleton (H1 (linearNatural F d))] :
    IsCompl s.space.toSubmodule ρ.invariants := by
  have hz := invariants_of_equiv e (repeated_invariants r (linearNatural_invariants F hd))
  have hdis := moved_disjoint_fixed s hz
  subst L
  rw [fixedSpace_top] at hdis
  let := H1_repeated_subsingleton (ρ := linearNatural F d) r
  let := e.ofTop.H1_subsingleton
  exact ⟨hdis, codisjoint_iff.mpr (s.fixed_supplement_of_H1_subsingleton ρ)⟩

theorem repeated_binary_isCompl {L : Subgroup G} (s : MovedSection ρ L)
    {d r : ℕ} (hd : 4 ≤ d) (hL : L = ⊤)
    (hn : IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype)
      BinaryField.two d r) : IsCompl s.space.toSubmodule ρ.invariants := by
  obtain ⟨e⟩ := hn
  let := H1_linearNatural_subsingleton hd
  exact repeated_isCompl s BinaryField.two (by omega) hL e

theorem H1_three_large (F : BinaryField) (hF : 1 < F.degree) :
    Subsingleton (H1 (linearNatural F 3)) := by
  have hc : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    have h := Nat.pow_lt_pow_right (by decide : 1 < 2) hF
    simpa using h
  let := SLHigherNatural.H1_subsingleton_sl3_large_field hc
  exact (H1RestrictEquiv (k := ZMod 2) (specialLinearNatural (k := F.Carrier) 3)).injective.subsingleton

theorem doubleThree_large_isCompl {L : Subgroup G} (s : MovedSection ρ L)
    (F : BinaryField) (hF : 1 < F.degree) (hL : L = ⊤)
    (e : ActionEquiv (s.space.toRepresentation.comp L.subtype)
      (repeated (linearNatural F 3) 2)) : IsCompl s.space.toSubmodule ρ.invariants := by
  let := H1_three_large F hF
  exact repeated_isCompl s F (by decide) hL e

theorem naturalDual_invariants {d : ℕ} (hd : 2 ≤ d) :
    (naturalPlusDual d).invariants = ⊥ := by
  have hn := linearNatural_invariants BinaryField.two hd
  have hdual := invariants_of_equiv (dualNaturalEquiv d) hn
  apply bot_unique
  intro v hv
  have h₁ : v.1 ∈ (linearNatural BinaryField.two d).invariants :=
    fun g => congrArg Prod.fst (hv g)
  have h₂ : v.2 ∈ (linearNatural BinaryField.two d).dual.invariants :=
    fun g => congrArg Prod.snd (hv g)
  rw [hn] at h₁
  rw [hdual] at h₂
  exact Prod.ext h₁ h₂

theorem naturalDual_isCompl {L : Subgroup G} (s : MovedSection ρ L)
    {d : ℕ} (hd : 4 ≤ d) (hL : L = ⊤)
    (hn : IsNaturalPlusDual (s.space.toRepresentation.comp L.subtype) d) :
    IsCompl s.space.toSubmodule ρ.invariants := by
  obtain ⟨e⟩ := hn
  have hdis := moved_disjoint_fixed s (invariants_of_equiv e (naturalDual_invariants (by omega)))
  subst L
  rw [fixedSpace_top] at hdis
  exact ⟨hdis, codisjoint_iff.mpr (s.fixed_supplement_of_naturalDual ρ hd rfl ⟨e⟩)⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
