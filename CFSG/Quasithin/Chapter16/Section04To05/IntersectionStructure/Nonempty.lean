module

public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.Local
public import Theory.GroupTheory.TightlyEmbedded.ProductDisconnected
public import BenderSuzuki.SE.Final

/-!
# Nonemptiness of the conjugate-centralizer relation

In a finite simple group, I.8.2 supplies the strongly embedded normalizer
criterion for a nonnormal tightly embedded K with odd conjugate normalizers.
We retain this earlier source consequence as an explicit input. Empty Δ
would satisfy its hypotheses.

The actual Bender–Suzuki recognition theorem, including its Borel conclusion,
makes that normalizer solvable. This contradicts the nontrivial quasisimple
component it contains. Thus the Bender exclusion requires neither the full
model converse nor an assumed even-characteristic theorem for every model.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), construction
preceding Notation 16.4.1, p.1183; I.8.2, pp.429–430. The I.8.2 owner must
still discharge `SimpleTightNormalizerCriterion` from its source theorem.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z : G} {L : Subgroup G}

/-- The simple-ambient normalizer consequence of I.8.2 used on p.1183.
This is an explicit earlier-theorem input, not a proved recognition theorem. -/
def SimpleTightNormalizerCriterion (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ K : Subgroup G, IsTightlyEmbedded K → ¬ K.Normal →
    HasOddConjugateNormalizers K →
      BenderSuzuki.IsStronglyEmbedded (normalizer (K : Set G))

theorem StandardSetup.component_not_solvable (h : StandardSetup T z L) :
    ¬ Group.IsSolvable L := by
  have hL : IsComponentIn L (involutionCentralizer z) := h.component
  let := hL.quasisimple
  let : Nontrivial L := (nontrivial_iff_ne_bot L).mpr hL.ne_bot
  exact Group.IsPerfect.not_isSolvable L

/-- The centralizer cannot be normal in the simple ambient group. -/
theorem StandardSetup.centralizer_not_normal [IsSimpleGroup G]
    (h : StandardSetup T z L) : ¬ (centralizer (L : Set G)).Normal := by
  intro hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (centralizer (L : Set G)) hn with hb | ht
  · have he := h.tight.1
    rw [hb, card_bot] at he
    exact (by decide : ¬ Even (1 : ℕ)) he
  · apply h.component_not_solvable
    apply Group.isSolvable_of_comm
    intro a b
    apply Subtype.ext
    have hb : (b : G) ∈ centralizer (L : Set G) := ht ▸ mem_top _
    exact hb a a.property

/-- Bender–Suzuki recognition supplies a solvable Borel, impossible because
it contains the nontrivial perfect component L. This uses no model converse. -/
theorem StandardSetup.normalizer_not_stronglyEmbedded [IsSimpleGroup G]
    (h : StandardSetup T z L) :
    ¬ BenderSuzuki.IsStronglyEmbedded (normalizer (L : Set G)) := by
  intro hM
  let M := normalizer (L : Set G)
  have htop : BenderSuzuki.involutionCore G = ⊤ :=
    hM.involutionCore_eq_top_of_isSimple inferInstance
  let e : BenderSuzuki.involutionCore G ≃* G :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hrank : BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo (BenderSuzuki.involutionCore G) :=
    BenderSuzuki.twoRankAtLeastTwo_of_mulEquiv e.symm
      (BenderSuzuki.simpleStronglyEmbeddedRankTwo M inferInstance hM)
  have hSE : BenderSuzuki.TheoremSEBenderConclusion M :=
    (BenderSuzuki.theorem_SE M hM).resolve_left (fun hh => hh hrank)
  have hb := (BenderSuzuki.recognition_borel_of_simple_theoremSEBenderConclusion
    M hM inferInstance hSE).2
  let : Group.IsSolvable M := hb.1
  let : Group.IsSolvable (L.subgroupOf M) := inferInstance
  have hs : Group.IsSolvable L :=
    Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe L.le_normalizer).toMonoidHom)
      (subgroupOfEquivOfLe L.le_normalizer).surjective
  exact h.component_not_solvable hs

/-- Δ is nonempty, conditional only on the earlier I.8.2 normalizer
criterion. All Bender incompatibility is discharged by the preceding theorem. -/
theorem StandardSetup.delta_nonempty [IsSimpleGroup G] (h : StandardSetup T z L)
    (hI82 : SimpleTightNormalizerCriterion G) : (delta L).Nonempty := by
  by_contra hempty
  have hodd : HasOddConjugateNormalizers (centralizer (L : Set G)) := by
    intro g hg
    apply Nat.not_even_iff_odd.mp
    intro he
    apply hempty
    refine ⟨(centralizer (L : Set G)).conjBy g, ⟨g, rfl⟩, ?_, ?_⟩
    · exact fun hh => hg (mem_normalizer_iff_map_conj_eq.mpr hh)
    · change Even (Nat.card ↥(normalizer (centralizer (L : Set G) : Set G) ⊓
        (centralizer (L : Set G)).conjBy g)) at he
      simpa only [inf_comm] using he
  have hm := hI82 _ h.tight h.centralizer_not_normal hodd
  rw [h.normalizers_eq] at hm
  exact h.normalizer_not_stronglyEmbedded hm

/-- Notation 16.4.1, including an adapted conjugator for 16.4.2(4).
The source theorem I.8.2 remains the explicit earlier input. -/
theorem StandardSetup.exists_adapted_intersectionSetup [IsSimpleGroup G]
    (h : StandardSetup T z L) (hI82 : SimpleTightNormalizerCriterion G) :
    ∃ g R, IntersectionSetup T z L g R ∧
      (T : Subgroup G) ⊓ normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
        (T : Subgroup G).conjBy g := by
  obtain ⟨g, R, hR⟩ := h.exists_intersectionSetup (h.delta_nonempty hI82)
  obtain ⟨a, ha, _, hle⟩ := hR.exists_adapted_setup
  exact ⟨a, R, ha, hle⟩

end CFSG.Quasithin.Chapter16.Intersections
