module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.OddRankOne
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.Suzuki

/-!
# Applying the actual nonnormal component catalogue to the small offender

The original catalogue has even-field rank one, odd-prime rank one, J₁,
and Suzuki. The unmarked degree and TI bounds exclude even-field rank one
and J₁; the odd-prime case supplies the literal natural SL₃(2) geometry
and w≥2. The only remaining possibility is an actual Suzuki quotient,
acting on the entire full module with no fixed vectors, while J(T)
centralizes the local module and moves the full module.

The final theorem applies this reduction to SourceNonnormalSmallOffenderAt
itself. It retains the remaining Suzuki configuration as a disjunct; it
does not assert that it has been excluded. This case and final assembly
remain with qt-d-10-nona5-small-offender. HalfSylowUniqueAt retains producer
qt-d-10-nona5-half-sylow-unique and final discharge by
qt-d-10-nona5-point-control. Source: Aschbacher--Smith 1.2.1(3), 10.1.1--2
and 10.2.12, printed pp.504,741--742,754--755.
-/

public noncomputable section
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation BenderSuzuki.MatrixGroups
open Chapter3.Section02 ChapterE PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Every quiet catalogue branch is resolved except the fully moved Suzuki case. -/
theorem quiet_survivor_or_fully_moved_suzuki
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) :
    (Nonempty (SourceLinearThreeGeometry T D) ∧ 2 ≤ globalW D.fullModule (T : Subgroup G)) ∨
    (∃ m : ℕ, 1 ≤ m ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) ∧
      ⁅D.fullModule,L⁆ = D.fullModule ∧
      D.fullModule ⊓ centralizer (L : Set G) = ⊥ ∧
      ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)) := by
  cases ModuleChoice.component_quotient_model D c.nonnormal with
  | linear_even n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hF)
    let a : SL(2,F) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
      MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
        ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
    exact (no_quiet_binary_rank_one D c hJ hNL (e.trans a.symm) hn hF).elim
  | linear_prime p hp ho hm =>
    exact Or.inl (survivor_of_quiet_odd_prime D c hJ hNL hp ho hm)
  | janko he =>
    exact (no_quiet_janko_one D c hJ hNL he.some).elim
  | suzuki m hm he =>
    have hf := quiet_suzuki_moved_eq_full D c hJ hNL hm he.some
    have hz := quiet_moved_fixed_eq_bot D c.many c.minimal c.nonnormal hJ
    rw [hf] at hz
    exact Or.inr ⟨m,hm,he,hf,hz,quiet_suzuki_full_thompson_moves D c hJ hNL hm he.some⟩

/-- The literal original contract, with its sole remaining family retained openly.
No contradiction callback or unproved module marking is assumed. -/
theorem nonnormalSmallOffender_or_quiet_suzuki
    (hhalf : PointControl.HalfSylowUniqueAt T) :
    SourceNonnormalSmallOffenderAt T ∨
    (∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
      Configuration T D g ∧
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) ∧
      normalizer (L : Set G) ≤ D.maximalLocal ∧
      ∃ m : ℕ, 1 ≤ m ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) ∧
        ⁅D.fullModule,L⁆ = D.fullModule ∧
        D.fullModule ⊓ centralizer (L : Set G) = ⊥ ∧
        ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)) := by
  classical
  by_contra h
  obtain ⟨hs,hr⟩ := not_or.mp h
  apply hs
  apply nonnormalSmallOffender_of_quiet_models_and_halfSylow hhalf
  intro L D g c hJ
  have hNL := PointControl.component_normalizer_le_of_halfSylowUnique D c.nonnormal
    (hhalf c.many L D c.nonnormal c.notA5)
  rcases quiet_survivor_or_fully_moved_suzuki D c hJ hNL with hgood | hbad
  · exact ⟨D,le_rfl,Or.inl hgood.1⟩
  · exact (hr ⟨L,D,g,c,hJ,hNL,hbad⟩).elim

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
