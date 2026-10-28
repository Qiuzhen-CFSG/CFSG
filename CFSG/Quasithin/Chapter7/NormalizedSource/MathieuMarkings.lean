module
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M24

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceIrreducible
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.Source

/-!
# Concrete Mathieu markings on the normalized chosen orbit

The Chapter K hypotheses construct the full M₁₂ heart action, the simple
M₂₂ code/cocode or semilinear triple-cover action, and the M₂₃ code/cocode.
For M₂₄, the source cubic bound gives degree eleven. The thirteen concrete
absolute simple modules exhaust the odd conjugacy-class bound; dimension
selects the native code or cocode. Scalar descent returns an intertwiner of
the original binary representations. The resulting source marking retains
the entire actor and discharges both its central cover and outer extension.

The chosen-module application constructs the Chapter K hypotheses and applies
these markings to the original orbit representation. Its subgroup rank is
therefore ten, eleven or twelve. The escaping-space and ambient recognition
arguments remain in the normalized Mathieu/J₄ assembly.

Source: Aschbacher--Smith, Table 7.1.1, printed p.697, and Chapter K,
pp.451,457--459; James, J. Algebra 27 (1973), 57--111; Guralnick--Malle,
Classification of 2F-modules I, Proposition 5.1 and Table 6.7.
-/

public noncomputable section
open Representation Sporadic.Mathieu
open scoped TensorProduct IsMulCommutative
universe v
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuMarkings
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum
private abbrev CandidateIndex := Option (Bool ⊕ (Fin 2 ⊕ Fin 8))

private theorem closed_eleven_marking
    {F W : Type v} [Field F] [IsAlgClosed F] [CharP F 2]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (σ : Representation F M24 W) [σ.IsIrreducible]
    (hW : Module.finrank F W = 11) :
    Nonempty (σ.Equiv (SmallModels.code F)) ∨
      Nonempty (σ.Equiv (SmallModels.cocode F)) := by
  classical
  obtain ⟨α, hαirr, hα⟩ := SmallModels.fortyFourModelsExist_of_binary
    SmallModels.binaryFortyFourModelsExist F
  obtain ⟨d, π, hπirr, hπ, hd⟩ := LargeModels.largeModelsExist F
  let V : CandidateIndex → Type v := fun i => match i with
    | none => F
    | some (.inl _) => Fin 11 → F
    | some (.inr (.inl _)) => Fin 44 → F
    | some (.inr (.inr j)) => Fin (d j) → F
  let addV : ∀ i, AddCommGroup (V i) := fun i => by
    rcases i with _ | (i | (i | i)) <;> dsimp [V] <;> infer_instance
  let modV : ∀ i, Module F (V i) := fun i => by
    rcases i with _ | (i | (i | i)) <;> dsimp [V] <;> infer_instance
  let rep : ∀ i, Representation F M24 (V i) := fun i => match i with
    | none => Representation.trivial F M24 F
    | some (.inl false) => SmallModels.code F
    | some (.inl true) => SmallModels.cocode F
    | some (.inr (.inl j)) => α j
    | some (.inr (.inr j)) => π j
  let finV : ∀ i, FiniteDimensional F (V i) := by
    intro i
    rcases i with _ | (i | (i | i)) <;> dsimp [V] <;> infer_instance
  let irr : ∀ i, IsIrreducible (rep i) := by
    intro i
    rcases i with _ | (i | (i | i))
    · change IsIrreducible (Representation.trivial F M24 F)
      constructor
      intro S
      rcases IsSimpleOrder.eq_bot_or_eq_top S.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)
    · cases i
      · exact SmallModels.code_irreducible F
      · exact SmallModels.cocode_irreducible F
    · exact hαirr i
    · exact hπirr i
  have hdistinct : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro E
    have hdim := E.toLinearEquiv.finrank_eq
    rcases i with _ | (i | (i | i)) <;> rcases j with _ | (j | (j | j))
    · exact hij rfl
    all_goals simp only [V, addV, modV, Module.finrank_self,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
    all_goals try omega
    · have := hd j; omega
    · cases i <;> cases j
      · exact hij rfl
      · exact (SmallModels.code_cocode_coordinates_inequivalent F).false E
      · exact (SmallModels.code_cocode_coordinates_inequivalent F).false E.symm
      · exact hij rfl
    · have := hd j; omega
    · exact (hα (fun h => hij (congrArg (fun k => (some (Sum.inr (Sum.inl k)) : CandidateIndex)) h))).false E
    · have := hd j; omega
    · have := hd i; omega
    · have := hd i; omega
    · have := hd i; omega
    · exact (hπ (fun h => hij (congrArg (fun k => (some (Sum.inr (Sum.inr k)) : CandidateIndex)) h))).false E
  have hc : Nat.card CandidateIndex = 13 := by
    simp [CandidateIndex, Nat.card_eq_fintype_card]
  obtain ⟨i, ⟨E⟩⟩ := exists_equiv_of_pRegular_class_bound V rep 2 hdistinct
    (hc ▸ oddClassBound) σ
  have hdim := E.toLinearEquiv.finrank_eq
  rw [hW] at hdim
  rcases i with _ | (i | (i | i))
  · simp [V] at hdim
  · cases i
    · exact Or.inl ⟨E⟩
    · exact Or.inr ⟨E⟩
  · simp [V] at hdim
  · simp only [V, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
    have := hd i
    omega

attribute [local instance] ZMod.algebra

/-- Every faithful irreducible native binary M₂₄ module of degree eleven is
marked by the actual code or cocode, with the identity group marking. -/
theorem m24_eleven_marking {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) M24 V)
    [σ.IsIrreducible] (hf : Function.Injective σ)
    (hd : Module.finrank (ZMod 2) V = 11) :
    Nonempty (σ.Equiv MathieuCode.codeRepresentation) ∨
      Nonempty (σ.Equiv MathieuCode.cocodeRepresentation) := by
  have hnon : ¬ IsMulCommutative M24 := by
    intro hc
    let := hc
    have he := mul_comm (⟨m24GeneratorA, m24GeneratorA_mem⟩ : M24)
      ⟨m24GeneratorB, m24GeneratorB_mem⟩
    have hp := congrArg (fun g : M24 => g.val 1) he
    exact (by decide +kernel :
      (m24GeneratorA * m24GeneratorB) (1 : Fin 24) ≠
        (m24GeneratorB * m24GeneratorA) (1 : Fin 24)) hp
  let : σ.IsAbsolutelyIrreducible :=
    isAbsolutelyIrreducible_of_prime_finrank_of_faithful σ hf (hd ▸ by decide) hnon
  let F := AlgebraicClosure (ULift.{v} (ZMod 2))
  let : (extendScalars F σ).IsIrreducible :=
    IsAbsolutelyIrreducible.irreducible_of_extension σ F
  have hdim : Module.finrank F (F ⊗[ZMod 2] V) = 11 := by
    simpa only [Module.finrank_baseChange] using hd
  rcases closed_eleven_marking (extendScalars F σ) hdim with hc | hc
  · obtain ⟨E⟩ := hc
    obtain ⟨e⟩ := repEquiv_of_extendScalars σ MathieuCode.codeRepresentation
      ⟨RepEquiv.ofRepresentationEquiv (E.trans (SmallModels.codeEquiv F).symm)⟩
    exact Or.inl ⟨e.toRepresentationEquiv⟩
  · obtain ⟨E⟩ := hc
    obtain ⟨e⟩ := repEquiv_of_extendScalars σ MathieuCode.cocodeRepresentation
      ⟨RepEquiv.ofRepresentationEquiv (E.trans (SmallModels.cocodeEquiv F).symm)⟩
    exact Or.inr ⟨e.toRepresentationEquiv⟩
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuMarkings

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuMarkings
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterH.Section10To12.M12Calculations
universe u w
variable {A : Type u} [Group A] [Finite A]
  {E : Type w} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]
  (ρ : Representation (ZMod 2) A E) (L : Subgroup A)

/-- A concrete marking of the M₁₂ heart, including every outer actor. -/
structure M12Marking where
  component : L ≃* Sporadic.Mathieu.M12
  embedding : A →* MulAut Sporadic.Mathieu.M12
  injective : Function.Injective embedding
  on_component : ∀ l : L, embedding l = MulAut.conj (component l)
  inner_preimage : (MulAut.innerSubgroup Sporadic.Mathieu.M12).comap embedding = L
  equivalence : ρ.Equiv (Ambient.automorphismRepresentation.comp embedding)
  degree : Module.finrank (ZMod 2) E = 10

/-- The full source hypotheses construct an actual M₁₂ heart marking. -/
theorem m12_marking (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hq : Nonempty ((L ⧸ center L) ≃* Sporadic.Mathieu.M12)) :
    Nonempty (M12Marking ρ L) := by
  rcases h.fitting with rfl
  obtain ⟨e⟩ := hq
  have hs : M12Source.Hypotheses ρ :=
    ⟨h.sqtk, h.quasisimple, h.faithful, h.irreducible, h.smallCubic⟩
  obtain ⟨f, ι, _, hi, hon, hinner, ⟨E⟩⟩ := M12Source.source_native_ambient_equiv ρ hs e
  exact ⟨⟨f, ι, hi, hon, hinner, E, M12Source.source_degree_eq_ten ρ hs e⟩⟩

/-- M₂₂ retains the simple code/cocode and the genuine semilinear triple cover. -/
theorem m22_marking (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hq : Nonempty ((L ⧸ center L) ≃* Sporadic.Mathieu.M22)) :
    M22Source.MarkedModels ρ L :=
  M22Source.source_markedModels ρ L
    ⟨h.sqtk, h.fitting.symm, h.quasisimple, h.faithful, h.irreducible, h.smallCubic, hq⟩

/-- The M₂₃ source action has its actual code or cocode marking. -/
theorem m23_marking (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hq : Nonempty ((L ⧸ center L) ≃* Sporadic.Mathieu.M23)) :
    Module.finrank (ZMod 2) E = 11 ∧
      (MathieuCode.IsM23Code ρ ∨ MathieuCode.IsM23Cocode ρ) := by
  rcases h.fitting with rfl
  obtain ⟨e⟩ := hq
  exact (LargeMathieu.source_m23_of_degree_and_small_recognition
    ChapterK.SporadicCatalogue.SourceFF.m23_degree_eleven LargeMathieu.m23SmallRecognition ρ
    ⟨h.sqtk, h.quasisimple, h.faithful, h.irreducible, h.smallCubic⟩ e).2

/-- Degree eleven and native completeness give the M₂₄ code/cocode marking
on the entire original actor. Central covers and outer actors are discharged. -/
theorem m24_marking (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hq : Nonempty ((L ⧸ center L) ≃* Sporadic.Mathieu.M24)) :
    MathieuSmall.IsM24ToddOrDual ρ := by
  rcases h.fitting with rfl
  obtain ⟨e⟩ := hq
  have hs : LargeMathieu.SourceHypotheses ρ :=
    ⟨h.sqtk, h.quasisimple, h.faithful, h.irreducible, h.smallCubic⟩
  have ht := LargeMathieu.m24_generalizedFitting_eq_top h.quasisimple e
  have hd := ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu.m24_degree_eleven
    ρ hs ⟨e⟩
  obtain ⟨a⟩ := LargeMathieu.ambient_equiv_of_prime_degree hs e ht (hd ▸ by decide)
  have hi : ρ.IsIrreducible :=
    (irreducible_comp_surjective_iff (generalizedFitting A).subtype
      (fun g => ⟨⟨g, ht ▸ mem_top g⟩, rfl⟩) ρ).mp h.irreducible
  let σ : Representation (ZMod 2) Sporadic.Mathieu.M24 E := ρ.comp a.symm.toMonoidHom
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff a.symm.toMonoidHom a.symm.surjective ρ).mpr hi
  refine ⟨a, ?_⟩
  rcases m24_eleven_marking σ (h.faithful.comp a.symm.injective) hd with hc | hc
  · obtain ⟨E⟩ := hc
    right
    refine ⟨Representation.Equiv.mk E.toLinearEquiv (fun g => ?_)⟩
    simpa [σ] using E.isIntertwining' (a g)
  · obtain ⟨E⟩ := hc
    left
    refine ⟨Representation.Equiv.mk E.toLinearEquiv (fun g => ?_)⟩
    simpa [σ] using E.isIntertwining' (a g)

/-- The literal normalized Mathieu rows. Every alternative contains an
actual group marking and a full-action intertwining equivalence. -/
@[expose] def MarkedRows : Prop :=
  Nonempty (M12Marking ρ L) ∨ M22Source.MarkedModels ρ L ∨
    (Module.finrank (ZMod 2) E = 11 ∧
      (MathieuCode.IsM23Code ρ ∨ MathieuCode.IsM23Cocode ρ)) ∨
    MathieuSmall.IsM24ToddOrDual ρ

/-- The representation part of Table 7.1.1 on the original actor. -/
theorem markedRows (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hm : HasMathieuCentralQuotient L) : MarkedRows ρ L := by
  rcases hm with h12 | h22 | h23 | h24
  · exact .inl (m12_marking ρ L h h12)
  · exact .inr (.inl (m22_marking ρ L h h22))
  · exact .inr (.inr (.inl (m23_marking ρ L h h23)))
  · exact .inr (.inr (.inr (m24_marking ρ L h h24)))

omit [Finite A] [FiniteDimensional (ZMod 2) E] in
/-- The marked source rows have precisely the binary dimensions in the table. -/
theorem MarkedRows.finrank_cases (hm : MarkedRows ρ L) :
    Module.finrank (ZMod 2) E = 10 ∨ Module.finrank (ZMod 2) E = 11 ∨
      Module.finrank (ZMod 2) E = 12 := by
  rcases hm with h12 | h22 | h23 | h24
  · obtain ⟨d⟩ := h12
    exact .inl d.degree
  · rcases h22 with hc | hd | ht
    · obtain ⟨d⟩ := hc
      exact .inl d.degree
    · obtain ⟨d⟩ := hd
      exact .inl d.degree
    · obtain ⟨d⟩ := ht
      exact .inr (.inr d.degree)
  · exact .inr (.inl h23.1)
  · exact .inr (.inl h24.finrank)
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuMarkings

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual chosen-orbit consumer of the Mathieu markings, with the
Chapter K hypotheses constructed from the source multiple-overgroup branch. -/
theorem sourceOrbit_mathieu_markings_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    MathieuMarkings.MarkedRows D.orbitRepresentation D.orbitComponent :=
  MathieuMarkings.markedRows D.orbitRepresentation D.orbitComponent
    (D.sourceOrbit_chapterK_of_many h hmany hnon hVW) hm

/-- The original subgroup has rank ten, eleven or twelve, including the
triple cover, with no assumed module or numerical marking. -/
theorem sourceOrbit_mathieu_rank_cases_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    rank D.sourceOrbit = 10 ∨ rank D.sourceOrbit = 11 ∨
      rank D.sourceOrbit = 12 := by
  have hc : Nat.card D.sourceOrbit = 2 ^ Module.finrank (ZMod 2) D.orbitSpace := by
    calc
      Nat.card D.sourceOrbit = Nat.card D.orbitSpace :=
        (Nat.card_congr D.sourceOrbitCoordinates.toEquiv).symm
      _ = _ := by simpa only [Nat.card_zmod] using
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.orbitSpace)
  have hr : rank D.sourceOrbit = Module.finrank (ZMod 2) D.orbitSpace := by
    rw [rank, hc, Nat.log_pow Nat.one_lt_two]
  rw [hr]
  exact MathieuMarkings.MarkedRows.finrank_cases _ _
    (D.sourceOrbit_mathieu_markings_of_many h hmany hVW hm hnon)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
