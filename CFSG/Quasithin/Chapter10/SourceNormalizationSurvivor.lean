module
public import CFSG.Quasithin.Chapter10.SourceSetup
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosure
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.SpecialLinearNatural

/-!
# The literal linear-three survivor and normalization endgame inputs

The independent non-A5 reduction must produce the original natural
SL₃(2) moved section, not merely its abstract group type. Its full module,
exchanged factors, point centralizers and weak-closure parameters are kept
on one actual fundamental setup. The separate replacement construction
must produce an actual maximal faithful A5 component in the same group.
These propositions specify outstanding source obligations; this module
does not prove the reduction or replacement by projecting record fields.

The proved consumer below supplies the opening solvable-overgroup step of
10.3.3: the natural section has order eight, giving r≥3, whereas w=2;
E.3.35 would give min(w,r)≤1 for an escaping solvable overgroup.
Source: Aschbacher--Smith 10.1.1(3), 10.2.9, 10.2.13 and 10.3,
printed pp.741,750,755--757.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] (T : Sylow 2 G)

/-- The actual remaining source configuration, before the independent
10.3 centralizer and replacement argument. -/
structure SourceLinearThreeSurvivor {L : Subgroup G}
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) where
  exchange : G
  exchange_mem : exchange ∈ T
  exchange_moves : exchange ∉ normalizer (L : Set G)
  full_eq_local : D.fullModule = D.moduleSubgroup
  generated : D.fullModule = ⁅D.fullModule,L⁆ ⊔
    (⁅D.fullModule,L⁆).map (MulAut.conj exchange).toMonoidHom
  crossed : (⁅D.fullModule,L⁆).map (MulAut.conj exchange).toMonoidHom ≤
    centralizer (L : Set G)
  quotient : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  natural : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
    (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
    ((Representation.specialLinearNatural 3).comp
      (quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
  weakClosure : globalW D.fullModule (T : Subgroup G) = 2
  generation : ∀ H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal,
    generationParameter H = 2
  pointCentralizers : ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 →
    centralizer ({v} : Set G) ≤ D.maximalLocal

/-- The non-A5 part of 10.2.13, including its literal natural action and
point-centralizer input. This is a source obligation, not an assumed instance. -/
def SourceNonnormalReductionAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ L : Subgroup G, L ∈ Chapter1.LStar G (T : Subgroup G) →
    ChapterA.Section04.IsFaithfulSignalizerType L → IsQuasisimple (L ⧸ pCore 2 L) →
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      Nonempty (SourceLinearThreeSurvivor T D)

/-- The output of the original replacement construction in 10.3.
The new component is maximal and faithful in the original ambient group. -/
def SourceLinearThreeReplacementAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    SourceLinearThreeSurvivor T D →
    ∃ R : Subgroup G, R ∈ Chapter1.LStar G (T : Subgroup G) ∧
      ChapterA.Section04.IsFaithfulSignalizerType R ∧ IsQuasisimple (R ⧸ pCore 2 R) ∧
      ¬ (T : Subgroup G) ≤ normalizer (R : Set G) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* alternatingGroup (Fin 5))

/-- Exclusion of a nonnormal faithful quasisimple maximal local component
in the earlier unique-overgroup branch. This is a separate source obligation. -/
def SourceSingleOvergroupExclusionAt : Prop :=
  (maximalTwoLocalOvergroups (T : Subgroup G)).ncard ≤ 1 →
    ∀ R : Subgroup G, R ∈ Chapter1.LStar G (T : Subgroup G) →
      ChapterA.Section04.IsFaithfulSignalizerType R →
      IsQuasisimple (R ⧸ pCore 2 R) →
      ¬ (T : Subgroup G) ≤ normalizer (R : Set G) → False

variable {T}

/-- Every solvable overgroup of the original Sylow lies in M, as required
in the first paragraph of the proof of source 10.3.3. -/
theorem SourceLinearThreeSurvivor.solvable_overgroups_le {L : Subgroup G}
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} [Group.IsSolvable H] (hTH : (T : Subgroup G) ≤ H) :
    H ≤ D.maximalLocal := by
  have hcard := s.natural.card_section
  have hn : 0 < Nat.card (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) : Subgroup G) :=
    Nat.card_pos
  have hsize : 8 ≤ Nat.card (⁅D.fullModule,L⁆ : Subgroup G) := by
    simp only [Nat.card_fun, Nat.card_fin, Nat.card_zmod] at hcard
    norm_num at hcard
    change Nat.card (⁅D.fullModule,L⁆ : Subgroup G) =
      8 * Nat.card (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) : Subgroup G) at hcard
    omega
  have hLV : L ≤ normalizer (D.fullModule : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hr := source_fullModule_globalR_lower_of_element_centralizers D
    (le_normalizer_iff_commutator_le_left.mp hLV) s.pointCentralizers
  have hlog : 3 ≤ Nat.log 2 (Nat.card (⁅D.fullModule,L⁆ : Subgroup G)) := by
    have := Nat.log_mono_right (b := 2) hsize
    norm_num at this
    exact this
  have hthree : (3 : ℕ∞) ≤ globalR D.fullModule := le_trans (by exact_mod_cast hlog) hr
  by_contra hout
  have hmin := source_solvable_overgroup_weakClosure_bound D hTH hout
  rw [s.weakClosure] at hmin
  rcases min_le_iff.mp hmin with hw | hr
  · exact (by decide : ¬ (2 : ℕ∞) ≤ 1) hw
  · exact (by decide : ¬ (3 : ℕ∞) ≤ 1) (hthree.trans hr)

end CFSG.Quasithin.Chapter10
