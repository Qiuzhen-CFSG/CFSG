module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictCatalogue
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.TripleCover.Identification
public import Theory.Representation.Mathieu.M22James.Classification
public import Theory.Representation.NormalConstituentDisplacement.FixedLine

/-!
# The triple-cover exclusion for the strict-intersection catalogue

In G.11.2(13), the original group is the outer extension of the genuine
triple cover of M₂₂ and the original module has dimension twelve. Clifford
semisimplicity supplies a simple component on which the central three acts
nontrivially. Quasisimplicity makes this component faithful, and its proved
minimum degree twelve makes it the whole module. James's uniqueness theorem
and the full matrix normalizer then identify the action of every ambient
involution, whose displacement rank is four or six, never two.

The original G.10 hypotheses exclude a reducible twelve-space. Thus the
published thirteen-case conclusion reduces to its unchanged symplectic
four-space alternative on the literal strict quotient. This is conditional
progress: the four-space exclusion and the genuine classifier remain with
qt-d-1222-recognition-strict-elimination. The classifier producer is
qt-g112-low-rank-symplectic-classification, and the final recognition owner
qt-d-1222-rankone-recognition-identification supplies LocalAnalysis.

Source: Aschbacher--Smith, G.11.2(13) and 6.2.19, printed pp.364,691
(PDF pp.375,708). The imported Mathieu modules supply the minimum degree,
intertwiner and outer normalizer, retaining their source attribution.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open Representation.RankTwo Sporadic.Mathieu
open scoped MonoidAlgebra IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.StrictCatalogue
variable {H V : Type*} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem triple_restriction_irreducible
    (ρ : Representation (ZMod 2) H V) (hρ : ρ.IsIrreducible)
    (hf : Function.Injective ρ) (hd : finrank (ZMod 2) V = 12)
    (L : Subgroup H) [L.Normal] (e : L ≃* M22TripleCover) :
    Representation.IsIrreducible (ρ.comp L.subtype) := by
  let σ : Representation (ZMod 2) L V := ρ.comp L.subtype
  let : IsSemisimpleModule (ZMod 2)[L] σ.asModule :=
    NormalConstituentDisplacement.restriction_semisimple ρ hρ L
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv e.symm
  have hcenter : Nat.card (center L) = 3 :=
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans M22TripleCover.center_card
  have hn : ¬ center L ≤ σ.ker := by
    intro hn
    have hfaith : Function.Injective σ := hf.comp Subtype.val_injective
    have he : center L = ⊥ := bot_unique (by simpa only [σ.ker_eq_bot_iff.mpr hfaith] using hn)
    rw [he, Subgroup.card_bot] at hcenter
    omega
  obtain ⟨m, hm, hmk⟩ := Representation.exists_simple_submodule_nontrivial_of_not_le_ker σ (center L) hn
  let W := Subrepresentation.ofSubmodule' m
  let τ := W.toRepresentation
  let : IsIrreducible τ := Representation.irreducible_of_ofSubmodule'_simple σ hm
  have hτ : Function.Injective τ := by
    apply τ.ker_eq_bot_iff.mp
    rcases IsQuasisimple.normal_le_center_or_eq_top τ.ker with hk | hk
    · have hc : Nat.card τ.ker ∣ 3 := hcenter ▸ card_dvd_of_le hk
      rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hc with hc | hc
      · exact (Subgroup.eq_bot_iff_card _).mpr hc
      · exact (hmk (eq_of_le_of_card_ge hk (by omega)).symm.le).elim
    · exact (hmk (hk ▸ le_top)).elim
  have hmin := M22TripleCover.faithful_irreducible_finrank_ge_twelve_of_equiv e τ hτ
  have hW : W = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.eq_top_of_finrank_eq
    exact Nat.le_antisymm (Submodule.finrank_le W.toSubmodule) (by simpa only [hd] using hmin)
  have ha : IsAtom W := (Subrepresentation.irreducible_iff_isAtom W).mp inferInstance
  rw [hW] at ha
  exact isSimpleOrder_iff_isAtom_top.mpr ha

omit [Finite H] in
/-- The abstract group clause of case (13) suffices once the original action
is irreducible: Clifford semisimplicity and the genuine minimum degree recover
the triple-cover module, and its ambient matrix normalizer handles outer actors. -/
theorem exclude_thirteen
    (ρ : Representation (ZMod 2) H V) (hρ : ρ.IsIrreducible)
    (hf : Function.Injective ρ) (a : H) (ha2 : a ^ 2 = 1)
    (hr : finrank (ZMod 2) (movedSpace ρ a) = 2)
    (hc : ChapterG.Section11.CaseThirteen ρ) : False := by
  obtain ⟨hd, ⟨e⟩⟩ := hc
  let σ : Representation (ZMod 2) _ V := ρ.comp e.symm.toMonoidHom
  have hσ : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mpr hρ
  let L := Janko4.InvolutionCentralizers.First.QuotientExtension.coverSubgroup
  let eL : L ≃* M22TripleCover := Subgroup.subgroupOfEquivOfLe
    Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.derivedGroup_le_actionGroup
  have hσf : Function.Injective σ := hf.comp e.symm.injective
  let : Representation.IsIrreducible (σ.comp L.subtype) := triple_restriction_irreducible σ hσ hσf hd L eL
  obtain ⟨E⟩ := TripleCover.component_equiv σ L eL hσf hd
  have hn := TripleCover.no_rank_two_of_component_equiv σ L eL E (e a)
    (by rw [← map_pow, ha2, map_one])
  apply hn
  have he (g : H) (w : V) : (LinearEquiv.refl (ZMod 2) V) (ρ g w) =
      σ (e g) ((LinearEquiv.refl (ZMod 2) V) w) := by simp [σ]
  exact (finrank_movedSpace_transport ρ σ e (LinearEquiv.refl _ _) he a).symm.trans hr

/-- With the original G.10 hypothesis, the catalogue reduces to its
four-dimensional alternative. Degree twelve cannot use the reducible branch. -/
theorem caseTwo_of_conclusion
    {ρ : Representation (ZMod 2) H V} {B : LinearMap.BilinForm (ZMod 2) V}
    {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup H}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hd : 4 ≤ finrank (ZMod 2) V)
    (a : H) (ha : a ∈ X) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hr : finrank (ZMod 2) (movedSpace ρ a) = 2)
    (hType : ∀ w, B w (ρ a w) = 0)
    (hnt : ¬ StabilizerTransitive ρ (movedSpace ρ a))
    (hc : ChapterG.Section11.Conclusion ρ B X) : ChapterG.Section11.CaseTwo ρ B := by
  rcases remaining_cases h.faithful h.alternating h.nondegenerate h.preserves
      hd a ha ha1 ha2 hr hType hnt hc with htwo | hthirteen
  · exact htwo
  · have hi : IsIrreducible ρ := by
      by_contra hn
      have hfour := (h.reducible_degree_and_solvable hn).1
      have htwelve := hthirteen.1
      omega
    exact (exclude_thirteen ρ hi h.faithful a ha2 hr hthirteen).elim

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.StrictCatalogue


namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The literal strict action can only satisfy the four-space catalogue row.
The catalogue remains an explicit conditional input; its exhaustive recognition
and the four-space exclusion are still required for the strict contradiction. -/
theorem LocalAnalysis.strict_catalogue_caseTwo
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G))
    (hdS : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd3 : orderOf d = 3)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    [IsElementaryAbelian 2 (strictCrossingImage (T : Subgroup G) L R z d)]
    (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)))
    (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z))
    (h : ChapterG.Section10.Hypothesis (strictRepresentation (T : Subgroup G) L R z) B v
      (strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d))
      (strictCrossingImage (T : Subgroup G) L R z d)
      ((strictCrossingCenterImage (T : Subgroup G) L R z d).subgroupOf
        (strictCrossingImage (T : Subgroup G) L R z d)))
    (hB : ∀ u w : sourceClosure (T : Subgroup G) L R z,
      B (strictHatElement (T : Subgroup G) L R z u)
        (strictHatElement (T : Subgroup G) L R z w) = 0 ↔ Commute u w)
    (hc : ChapterG.Section11.Conclusion (strictRepresentation (T : Subgroup G) L R z) B
      (strictCrossingImage (T : Subgroup G) L R z d)) :
    ChapterG.Section11.CaseTwo (strictRepresentation (T : Subgroup G) L R z) B := by
  obtain ⟨he', hX', B', v', _, _, hB', hd, _, _, _, _,
      a, ha, ha1, ha2, _, hr, _, htype, hnt⟩ :=
    A.strict_g11_inputs h611 hnatural hz horder hTH hstrict hdres hdH hdS hd3
  have hzero (u w : Additive (StrictVectorQuotient (T : Subgroup G) L R z)) :
      B u w = 0 ↔ B' u w = 0 := by
    obtain ⟨u', hu⟩ := QuotientGroup.mk'_surjective
      (center (sourceClosure (T : Subgroup G) L R z)) u.toMul
    obtain ⟨w', hw⟩ := QuotientGroup.mk'_surjective
      (center (sourceClosure (T : Subgroup G) L R z)) w.toMul
    simpa only [strictHatElement, hu, hw, ofMul_toMul] using
      (hB u' w').trans (hB' u' w').symm
  exact StrictCatalogue.caseTwo_of_conclusion h hd a ha ha1 ha2 hr (fun w => (hzero w _).mpr (htype w)) hnt hc

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
