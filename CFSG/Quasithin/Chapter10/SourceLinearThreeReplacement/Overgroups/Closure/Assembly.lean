module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Orbit
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Seed
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Assembly

/-!
# Conditional source assembly of the seed normal-closure alternatives

The recognized maximal parabolic supplies the local Xi input and the
actual S₃-wreath quotient. Component detection identifies the H-normal
closure with the component orbit. The swapped and Held rows already have
the required models; only the invariant classical rows use the additional
wreath-action sieve. Full Sylow and SQTK hypotheses are discharged for
every actual maximal two-local containing K_zT.

The two remaining source obligations are explicit in the theorem below.
This module does not assert `ClosureAlternativesAt` without them.
Source: Aschbacher--Smith 10.2.4, p.747, and §10.3, pp.756--757.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

private theorem binary_degree_ge_two {Q : Type*} [Group Q] {n : ℕ}
    (hn : Even n) (hm : ClassicalGroup.IsPSL Q 2 (2 ^ n)) : 2 ≤ n := by
  have hn0 : n ≠ 0 := by
    intro he
    obtain ⟨F,_,_,hc,_⟩ := hm
    have hlarge := Finite.one_lt_card (α := F)
    simp only [he, pow_zero] at hc
    omega
  obtain ⟨m,hm⟩ := hn
  omega

/-- The intrinsic normal-closure calculation, conditional only on the
additional invariant wreath-action sieve. The Held row is preserved. -/
theorem normalClosure_models_of_sieve
    (hsieve : InvariantWreathSieveAt T)
    {X P H : Subgroup G} (h : LocalInput 3 (T : Subgroup G) X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hw : Nonempty (((X ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (X ⊔ (T : Subgroup G) : Subgroup G)) ≃* ParabolicWreath)) :
    conjugateSpanBy X H = X ∨ ∃ I : Subgroup G,
      I ∈ cComponentsIn H ∧ IsQuasisimple (XiQuotient I) ∧
      conjugateSpanBy X H = componentOrbit I (T : Subgroup G) ∧ ClosureModel T I := by
  rcases adequate_three_normalClosure h hH
      (sylowIn_overgroup (le_sup_right.trans h.overgroup)) with
    he | ⟨I,hI,hq,hn,hcomm,hP,he,halt⟩
  · exact Or.inl he
  · refine Or.inr ⟨I,hI,hq,he,?_⟩
    rcases halt with ⟨hplane,hswap | hinvariant⟩ | hheld
    · rcases hswap.2 with ⟨n,hn,_,hm⟩ | ⟨p,hp,ho,hm⟩
      · exact Or.inl ⟨n,binary_degree_ge_two hn hm,hn,hm⟩
      · exact Or.inr (Or.inl ⟨p,hp,ho,hm⟩)
    · have hi := hinvariant.1
      have horbit : componentOrbit I (T : Subgroup G) = I :=
        le_antisymm (iSup_conjugates_le_of_le_normalizer I T I le_rfl hi)
          (le_componentOrbit I T)
      have hX : X ≤ I := (le_conjugateSpanBy X H).trans (he.trans horbit).le
      rw [horbit] at hn hcomm hP
      obtain ⟨k,hk,hm,ha⟩ := hsieve X P H I h hH hI hq hn hi hP hX hcomm hw
        ⟨hplane,Or.inr hinvariant⟩
      exact Or.inr (Or.inr (Or.inl ⟨hi,k,hk,hm,ha⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hheld.2.2.1,hheld.2.2.2⟩))

/-- Source assembly for the literal seed and every actual containing
maximal two-local. The two independent source premises remain visible. -/
theorem closureAlternatives_of_seed_and_sieve
    (hseed : ParabolicSeedAt T) (hsieve : InvariantWreathSieveAt T) :
    ClosureAlternativesAt T := by
  intro hmany L D s d _ _ _ _ M hM hJM
  obtain ⟨r⟩ := hseed hmany L D s d
  have hXM : centralizerSeed T L (d.first * d.second) ⊔ (T : Subgroup G) ≤ M :=
    (sup_le_sup_right (le_conjugateSpanBy _ _) _).trans hJM
  obtain ⟨P,hP⟩ := r.localInput hXM
  exact normalClosure_models_of_sieve hsieve hP (D.simpleQTKE.twoLocal_sqtk hM.1)
    r.seed_wreath

/-- Application to the original overgroup span, keeping the independent
model-generation input with its existing assembly owner. -/
theorem overgroupSpan_of_seed_sieve_and_generation
    (hseed : ParabolicSeedAt T) (hsieve : InvariantWreathSieveAt T)
    (hgeneration : ModelGenerationAt T) : OvergroupSpanAt T :=
  overgroupSpan_of_source_inputs (closureAlternatives_of_seed_and_sieve hseed hsieve)
    hgeneration

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure
