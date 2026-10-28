module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.SmallModules.SectionIdentification
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupTheory.PrimeRankInvolutionLift

/-!
# Excluding the terminal binary three-dimensional component

The component has order 168, hence three-rank one. The corrected B.4.2
list and the actual strong offender leave only the natural SL₃ row; the
strong inequality on the original module also removes B.5.1's doubled row.
An embedded additive field square forces the defining field to have degree
one. The quotient dimension is then three, whereas all proper outer natural
extensions in B.5.1 have dimension four or six. Thus the component is proved
to be the whole late actor.

The resulting BinaryModuleCase retains the actual central fixed subspace
and its quotient, including nonsplit central extensions. Identifying its
moved space with the terminal point space feeds the existing intrinsic
point-core exclusion. No module coordinates or whole-actor equality are
assumed by the exported source application.

The field transport and three-rank comparison follow the corresponding
native Chapter B arguments, instantiated here for the distinct Chapter 15
source structures. Matrix field transport uses the attributed ATLAS port
in Theory.AtlasPort.ExceptionalIsomorphisms.Support (LICENSES/ATLAS.txt).
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2,
printed p.86, B.5.1, pp.99–103, and the PSL₃(2) paragraph of 15.3.49, p.1145.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.SmallModules
open ReducedModels ComponentReduction ModelReduction BinaryModels ModelExclusions

private theorem rank_three_of_card {D : Type*} [Group D] [Finite D]
    (hc : Nat.card D = 168) : primeRank 3 D = 1 := by
  obtain ⟨A, _, hA⟩ := exists_elementaryAbelian_card_primeRank (G := D) (p := 3)
  have hd : 3 ^ primeRank 3 D ∣ 168 := by
    rw [← hA, ← hc]
    exact A.card_subgroup_dvd_card
  have hu : primeRank 3 D < 2 := by
    by_contra! hn
    have hh : 9 ∣ 168 := (pow_dvd_pow 3 hn).trans hd
    norm_num at hh
  have hp : primeRank 3 D ≠ 0 := by
    intro hz
    have hh := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    norm_num [hc] at hh
  omega

private def shear (F : BinaryField) : Multiplicative (F.Carrier × F.Carrier) →*
    Matrix.SpecialLinearGroup (Fin 3) F.Carrier where
  toFun c := ⟨!![1,c.toAdd.1,c.toAdd.2; 0,1,0; 0,0,1], by simp [Matrix.det_fin_three]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' c d := by
    apply Subtype.ext
    change !![1,c.toAdd.1+d.toAdd.1,c.toAdd.2+d.toAdd.2; 0,1,0; 0,0,1] =
      !![1,c.toAdd.1,c.toAdd.2; 0,1,0; 0,0,1] *
        !![1,d.toAdd.1,d.toAdd.2; 0,1,0; 0,0,1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]

private theorem shear_injective (F : BinaryField) : Function.Injective (shear F) := by
  intro c d h
  exact Prod.ext (congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) F.Carrier =>
    g.val 0 1) h) (congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) F.Carrier =>
    g.val 0 2) h)

/-- A genuine SL₃ model of a group of order 168 has binary defining field. -/
theorem field_degree_one {D : Type*} [Group D] [Finite D] (F : BinaryField)
    (hD : Nat.card D = 168)
    (e : D ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) : F.degree = 1 := by
  have hd := Subgroup.card_dvd_of_injective (shear F) (shear_injective F)
  have hm : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) = 168 :=
    (Nat.card_congr e.toEquiv).symm.trans hD
  have hf : Nat.card (Multiplicative (F.Carrier × F.Carrier)) = 2 ^ (2 * F.degree) := by
    rw [Nat.card_congr (Multiplicative.toAdd : _ ≃ F.Carrier × F.Carrier), Nat.card_prod,
      F.card_eq, ← pow_add]
    congr 1
    omega
  rw [hf, hm] at hd
  have hn : F.degree < 2 := by
    by_contra! h
    have hh : 16 ∣ 168 := (pow_dvd_pow 2 (show 4 ≤ 2 * F.degree by omega)).trans hd
    norm_num at hh
  have hp := F.degree_pos
  omega


private theorem not_large_rank {D A : Type*} [Group D] [Group A] [Finite D] [Finite A]
    (hr : primeRank 3 D = 1) (e : D ≃* A) (ha : 2 ≤ primeRank 3 A) : False := by
  rw [← primeRank_equiv 3 e, hr] at ha
  omega

private theorem natural_of_rank_one {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {J P : Subgroup D}
    (hr : primeRank 3 J = 1)
    (h : ProjectiveLine.IrreducibleActionCase ρ J P) (hq : quadraticRatio ρ ≠ 1) :
    ∃ F : BinaryField, Nonempty (ActionEquiv (ρ.comp J.subtype) (linearNatural F 3)) := by
  cases h with
  | linearTwo _ _ _ _ h => exact (hq h).elim
  | linearThree F _ a _ => exact ⟨F, ⟨a⟩⟩
  | symplectic _ _ _ a _ =>
    exact (not_large_rank hr a.groupEquiv
      (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans
        (_root_.primeRank_le_of_injective 3 (_root_.commutator _).subtype
          (_root_.commutator _).subtype_injective))).elim
  | symplecticTwo a _ =>
    exact (not_large_rank hr a.subgroupEquiv
      Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic).elim
  | g2 _ _ _ _ _ h => exact (hq h).elim
  | g2Two _ _ h => exact (hq h).elim
  | symmetric _ _ _ _ h => exact (hq h).elim
  | alternatingSix _ _ _ h => exact (hq h).elim
  | alternatingSeven _ _ _ _ _ h => exact (hq h).elim
  | tripleSix _ _ h => exact (hq h).elim
  | binaryLinear d hd _ a _ =>
    exact (not_large_rank hr a.groupEquiv (BinaryLinear.SmallCubicRank.four_or_five hd)).elim
  | orthogonalSix _ _ _ _ h => exact (hq h).elim
  | symmetricEight _ a _ =>
    exact (not_large_rank hr a.subgroupEquiv
      (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide))).elim
  | exteriorFive _ _ _ _ _ h => exact (hq h).elim

/-- The binary endpoint changes matrices and vectors by the same field isomorphism. -/
noncomputable def binary_natural_equiv (F : BinaryField) (hF : F.degree = 1) (d : ℕ) :
    ActionEquiv (linearNatural F d) (linearNatural BinaryField.two d) := by
  letI := Fintype.ofFinite F.Carrier
  have hc : Fintype.card F.Carrier = 2 := by
    rw [← Nat.card_eq_fintype_card, F.card_eq, hF]
    decide
  let e : F.Carrier ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F.Carrier Nat.prime_two hc).symm
  let l : F.Carrier ≃ₗ[ZMod 2] ZMod 2 :=
    { e.toAddEquiv with map_smul' := ZMod.map_smul e }
  refine ⟨Atlas.fieldEquivSL d e, LinearEquiv.piCongrRight (fun _ : Fin d => l), ?_⟩
  intro g v
  funext i
  change e (∑ j, g.val i j * v j) = ∑ j, e (g.val i j) * e (v j)
  simp only [map_sum, map_mul]

private theorem whole_of_three_dimension {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {J : Subgroup D}
    (hd : Module.finrank (ZMod 2) W = 3)
    (hext : J = ⊤ ∨ (∀ T : Sylow 2 D, J ⊔ (T : Subgroup D) = ⊤) ∧
      OuterNaturalAction ρ) : J = ⊤ := by
  rcases hext with ht | ⟨_, hext⟩
  · exact ht
  exfalso
  rcases hext with ⟨n, hn, hN, ⟨a⟩⟩ | ⟨a⟩
  · have ha := a.linearEquiv.finrank_eq
    rw [hd] at ha
    interval_cases n
    · rw [BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)] at ha
      norm_num at ha
    · rw [BinaryPermutation.finrank_natural_even (Fin 6) (by decide)] at ha
      norm_num at ha
    · rw [BinaryPermutation.finrank_natural_odd (Fin 7) (by decide)] at ha
      norm_num at ha
    · rw [BinaryPermutation.finrank_natural_even (Fin 8) (by decide)] at ha
      norm_num at ha
  · obtain ⟨a⟩ := a
    have ha := a.linearEquiv.finrank_eq
    rw [hd, Atlas.G2.Natural.finrank_space] at ha
    omega

private theorem central_binary_of_natural {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
    (c : MovedSection ρ J) (ht : J = ⊤)
    (a : ActionEquiv (c.action.comp J.subtype) (linearNatural BinaryField.two 3)) :
    PointCases.BinaryModuleCase c.space.toRepresentation J := by
  subst J
  let e := Subgroup.topEquiv.symm.trans a.groupEquiv
  refine .centralNatural e rfl c.central c.central_eq a.linearEquiv ?_
  intro g v
  exact a.intertwines ⟨g, mem_top g⟩ v

/-- All corrected B.5.1 rows are considered. Strong offending excludes the
ratio-one rows, including the doubled row; the component order forces the
remaining SL₃ field to be binary. The dimension of its faithful quotient
excludes every proper outer extension, proving that the actor is the component. -/
theorem binary_case_of_source {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ J)
    (e : J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (hs : IsStrongFFModule ρ) :
    PointCases.BinaryModuleCase c.sectionData.space.toRepresentation J := by
  have hc : Nat.card J = 168 :=
    (Nat.card_congr (e.trans Matrix.PSL3Two.equiv.symm).toEquiv).trans Matrix.PSL3Two.card_SL
  have hr := rank_three_of_card hc
  have hq : quadraticRatio ρ ≠ 1 := ne_of_lt
    ((isStrongFFModule_iff_quadraticRatio_lt_one ρ).mp hs)
  have hsq : quadraticRatio c.sectionData.action ≠ 1 := by
    apply ne_of_lt
    apply (isStrongFFModule_iff_quadraticRatio_lt_one _).mp
    obtain ⟨A, hA⟩ := hs
    exact ⟨A, hA.1, (NaturalSelection.movedSection_codim_le c.sectionData A).trans_lt hA.2⟩
  cases c.clause_one with
  | doubleThree _ _ _ _ h => exact (hq h).elim
  | naturalDual d hd _ ha =>
    obtain ⟨a⟩ := ha
    exact (not_large_rank hr a.groupEquiv (BinaryLinear.SmallCubicRank.four_or_five hd)).elim
  | repeatedNatural d _ hd _ _ _ ha =>
    obtain ⟨a⟩ := ha
    exact (not_large_rank hr a.groupEquiv (BinaryLinear.SmallCubicRank.four_or_five hd)).elim
  | irreducible _ _ _ h hext =>
    obtain ⟨F, ⟨a⟩⟩ := natural_of_rank_one hr h hsq
    have hF := field_degree_one F hc a.groupEquiv
    let b := binary_natural_equiv F hF 3
    let t : ActionEquiv (c.sectionData.action.comp J.subtype)
        (linearNatural BinaryField.two 3) :=
      ⟨a.groupEquiv.trans b.groupEquiv, a.linearEquiv.trans b.linearEquiv,
        fun g v => (congrArg b.linearEquiv (a.intertwines g v)).trans (b.intertwines _ _)⟩
    have hd : Module.finrank (ZMod 2)
        (c.sectionData.space.toSubmodule ⧸ c.sectionData.central.toSubmodule) = 3 := by
      rw [t.linearEquiv.finrank_eq]
      exact Module.finrank_pi (ZMod 2)
    exact central_binary_of_natural c.sectionData
      (whole_of_three_dimension c.sectionData.action hd hext) t

universe u
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    {r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper}

/-- The full corrected source implication supplies the binary module case on
the literal point space. Only genuine earlier source implications are inputs. -/
theorem binary_on_point (p : TerminalPoint r) (s : StrongPlacement r)
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (source : ProjectiveLine.QuasisimpleClassificationInput.{u,u} κ)
    (e : starImage H L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    PointCases.BinaryModuleCase (PointOnLateActor.space p).toRepresentation
      ((starImage H L).subgroupOf (lateActor r.placed.action)) := by
  obtain ⟨c⟩ := r.late_source_conclusion sections orbits source
  have h := binary_case_of_source c
    ((subgroupOfEquivOfLe (r.component_le_late_actor sections orbits)).trans e)
    ⟨_, s.late_offender.2.2⟩
  rw [point_space_eq p sections orbits c.sectionData]
  exact h

/-- The PSL₃(2) component branch contradicts the original later strong
subgroup in the intrinsic two-core of the actual point stabilizer. -/
theorem exclude_binary (p : TerminalPoint r) (s : StrongPlacement r)
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (source : ProjectiveLine.QuasisimpleClassificationInput.{u,u} κ)
    (e : starImage H L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) : False :=
  PointOnLateActor.exclude_binary p s sections orbits
    (binary_on_point p s sections orbits source e)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.SmallModules
