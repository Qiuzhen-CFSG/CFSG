module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.Source
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.TerminalModels.Sporadic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.OddModels.SmallParameters
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable

/-!
# The remaining actual component models in plane uniqueness

The original component extraction and all proved linear, alternating and
sporadic exclusions leave precisely the unclosed characteristic-two models
and J₄. The actual PSL₂(5) and PSL₂(7) comparisons absorb the small aliases
into the characteristic-two rows. Every row retains an actual model equivalence
and the same conjugation action of z. The conclusion is derived from the
original 1.1.5 packet; no terminal-classification premise is assumed.

The final source application starts with failure of plane uniqueness and
uses the completed 15.2.23. Its earlier HStar quotient, Kc orbit, restricted
action and plane-inverter premises retain their plane-geometry and
small-parabolic producers, with discharge by the chosen-action assembly.
The remaining rows are proof obligations, not a proof of 15.2.15.

Source: Aschbacher--Smith, 15.2.24 and proof of 15.2.15,
printed pp.1117--1118, refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
open ChapterD ChapterD.UniqueFactor PlaneUniquenessPreceding

/-- The unclosed rows, each on the actual component and marked automorphism. -/
inductive RemainingModelAction115 (L : Type*) [Group L] (a : MulAut L) : Prop
  | lie (simple : IsSimpleGroup L) (model : LieTypeTwoModel L)
      (inner : a ∈ (MulAut.conj (G := L)).range)
  | two_cover (nontrivial_center : center L ≠ ⊥) (center_eq : center L = pCore 2 L)
      (model : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4 ∨ IsG2At (L ⧸ pCore 2 L) 4)
      (inner : a ∈ (MulAut.conj (G := L)).range)
  | janko_four (model : Nonempty ((L ⧸ pCore 2 L) ≃* Janko4.Model))
      (action : TwoCentralInner a)

open scoped MatrixGroups IsMulCommutative

private theorem small_linear_two_is_lie {L : Type*} [Group L] [IsQuasisimple L]
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hs : p ≤ 7)
    (hm : ClassicalGroup.IsPSL L 2 p) : IsSimpleGroup L ∧ LieTypeTwoModel L := by
  have hp2 : p ≠ 2 := by
    intro he
    rcases hp.2 with ⟨k,hk⟩ | ⟨k,hk⟩
    · have hh : 1 < (2 : ℕ) ^ (2 ^ k) := one_lt_pow₀ (by decide) (by positivity)
      omega
    · have hd : 3 ∣ 2 ^ k := by rw [←hk,he]
      have hh := Nat.prime_three.dvd_of_dvd_pow hd
      norm_num at hh
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hns : ¬ Group.IsSolvable PSL(2,F) := by
    intro h
    let := h
    exact Group.IsPerfect.not_isSolvable L
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  have hlarge : 3 < p := by
    rw [←hF]
    exact Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
      (hF ▸ hp.1.odd_of_ne_two hp2) hns
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  refine ⟨e.isSimpleGroup,?_⟩
  have hcases : p = 5 ∨ p = 7 := by
    have hprime := hp.1
    interval_cases p <;> norm_num at *
  rcases hcases with rfl | rfl
  · apply Or.inl
    apply ClassificationModels.IsBenderModel.linear 2 (by decide)
    exact ⟨GaloisField 2 2,inferInstance,inferInstance,GaloisField.card 2 2 (by decide),
      RankOne.OddModels.linear_two_five_transport hF e⟩
  · refine Or.inr (Or.inl ?_)
    apply Chapter1.Section02.LocalModels.RankTwoTheoremC.linear 1 (by decide)
    exact ⟨ZMod 2,inferInstance,inferInstance,by simp,
      RankOne.OddModels.linear_two_seven_transport hF e⟩

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Apply every completed ordinary-model exclusion to the actual 1.1.5 action. -/
theorem component_model_remainder {P : Sylow 2 I} {z : G}
    (c : ComponentData (T := T) (Mc := Mc) I P z)
    (hI : PlaneEscapes Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1) :
    ∃ a : MulAut c.component,
      (∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹) ∧
      RemainingModelAction115 c.component a := by
  obtain ⟨a,ha,hm⟩ := c.model
  refine ⟨a,ha,?_⟩
  cases hm with
  | lie hs hm hi => exact .lie hs hm hi
  | two_cover hn hz hm hi => exact .two_cover hn hz hm hi
  | six s hs hm => exact (not_six_component d c hI hz hzne a ha s hs hm).elim
  | seven s hs hm => exact (not_seven_component d c hI hz hzne a ha s hs hm).elim
  | odd hm hi =>
    rcases hm with hm | ⟨p,hp,hm⟩
    · exact (not_linear_three_component d c hI hz hzne a ha hm hi).elim
    · by_cases hs : p ≤ 7
      · let : IsQuasisimple c.component := c.isComponent.2
        obtain ⟨hsm,hlie⟩ := small_linear_two_is_lie hp hs hm
        exact .lie hsm hlie hi
      · exact (not_linear_two_component d c hI hP hz hzne hp (by omega) hm).elim
  | sporadic name hn hm hi =>
    obtain ⟨e⟩ := hm
    have he := sporadic_quotient_eq_j4 d c hI hz hzne name hn e a ha hi
    subst name
    exact .janko_four ⟨e⟩ hi

/-- Failure of source plane uniqueness yields one of the remaining marked
models on the same selected ordinary component, without a 15.2.24 callback. -/
theorem exists_remaining_component_of_nonunique
    (hquotient : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((Q ⧸ pCore 2 Q) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS)
    (hne : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) ≠ {Mc}) :
    ∃ (I : Subgroup G) (P : Sylow 2 I) (z : G),
      MinimalPlaneEscape Mc ZS I ∧
      (P : Subgroup I).map I.subtype = planeSylow T ZS ∧
      z ∈ centralInvolutions T ∧ z ≠ 1 ∧
      ∃ (c : ComponentData (T := T) (Mc := Mc) I P z) (a : MulAut c.component),
        (∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹) ∧
        RemainingModelAction115 c.component a := by
  obtain ⟨I,P,z,hI,hP,hz,hzne,⟨c⟩⟩ :=
    exists_component_data_of_nonunique d hquotient horbit ha hi hne
  obtain ⟨a,ha,hm⟩ := component_model_remainder d c hI.1 hP hz hzne
  exact ⟨I,P,z,hI,hP,hz,hzne,c,a,ha,hm⟩
end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
