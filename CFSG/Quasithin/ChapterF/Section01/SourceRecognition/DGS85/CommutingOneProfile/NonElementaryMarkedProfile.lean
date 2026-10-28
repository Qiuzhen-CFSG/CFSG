module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryMarkedProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalNonElementarySource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFormProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.ProfileComparisons
public import Theory.SpecificGroups.DihedralSolvable

/-!
# The nonelementary source profile and both marked unitary rows

For nonsolvable original parabolics, the source catalogue rules out the
small exceptional enlargements, so the enlarged actors equal the original
starred endpoints. Their literal quotient inclusions transport the constructed
Chapter 11 linear and PSU₃/SU₃ markings back to the original factors.
The special beta-core identities then supply the complete U₅ recognition
profile, including the two original core kernels and the actual SU₃ cover.
A Hermitian basis change fixes coordinates without discarding either cover.

The proved all-fields U₅ source theorem constructs one model equivalence
inducing both endpoint maps and the full Borel map. Splitting on the literal
S₀/Q_beta also constructs the exhaustive U₄/U₅ profile alternative for these
nonsolvable parabolics. The next module restores the original pair at the
full KnownSimple chosen-factor consumer.

The marked split quotient and rotation order four remain Chapter 14 inputs.
Nonsolvability is used explicitly; the unrestricted solvable order-144
source branch is not asserted here. Source: DGS (1985), (11.7)--(11.8),
pp.174--177, and Theorem D, p.224; Fong--Seitz II (8C), pp.202--210.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingNontrivial NoncommutingProfile Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open FongSeitzBinary FongSeitzBinary.UnitaryPresentation BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => reducedFamily L S
local notation "G₀" => Reduction.G₀ L S
local notation "R" => reducedSylow L S
local notation:max "M" b:arg => (Subgroup.map (Subgroup.subtype G₀) (graphLocalGroup F₀ (base F₀ b)))
local notation:max "P" i:arg => parabolic L R i

/-- Nonsolvability removes precisely the exceptional small enlargements.
The equality is with the original starred subgroup in the ambient group. -/
theorem nonsolvable_enlargedEndpoint_eq_starred (h : HypothesisF11 L S)
    (i : Fin 2) (hns : ¬ Group.IsSolvable (parabolic L S i)) :
    enlargedEndpoint L S i = starredParabolic L S i := by
  cases h.quotient i with
  | linear n hn hm =>
    obtain ⟨k,hF,hfin,hcard,⟨e⟩⟩ := hm
    let : Fintype k := Fintype.ofFinite k
    let : CharP k 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact reduced_enlargedEndpoint_eq_starred_of_linear h i e
  | suzuki m he =>
    exact reduced_enlargedEndpoint_eq_starred_of_suzuki_all h i m he.some
  | projective_unitary n hn hm =>
    have hn2 : 2 ≤ n := by
      by_contra hh
      have he : n = 1 := by omega
      subst n
      exact hns (parabolic_solvable_of_projective_unitary_two h i (by simpa using hm))
    obtain ⟨k,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    exact reduced_enlargedEndpoint_eq_starred_of_projective_unitary h i J hn2 hcard hconj e
  | special_unitary n hn hm =>
    have hn2 : 2 ≤ n := by
      by_contra hh
      have he : n = 1 := by omega
      subst n
      exact hns (parabolic_solvable_of_special_unitary_two h i (by simpa using hm))
    obtain ⟨k,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    exact reduced_enlargedEndpoint_eq_starred_of_special_unitary h i J hn2 hcard hconj e
  | dihedral he =>
    let := GLS3.Chapter5.dihedralGroup_isSolvable 5
    have hs : Group.IsSolvable (L i ⧸ pCore 2 (L i)) :=
      Group.isSolvable_of_surjective (f := he.some.symm.toMonoidHom) he.some.symm.surjective
    exact (hns ((h.parabolic_solvable_iff_local_quotient i).mpr hs)).elim

private def factorActorQuotient (h : HypothesisF11 L S) (b : Bool)
    (hns : ¬ Group.IsSolvable (parabolic L S (if b then 1 else 0))) :
    (L (if b then 1 else 0) ⧸ pCore 2 (L (if b then 1 else 0))) ≃*
      (M b ⧸ pCore 2 (M b)) := by
  have he : M b = starredParabolic L S (if b then 1 else 0) := by
    rw [reduced_graphLocalGroup_image h]
    cases b <;> exact nonsolvable_enlargedEndpoint_eq_starred h _ hns
  let a := MulEquiv.subgroupCongr he.symm
  exact (h.starredQuotientEquiv _).trans (QuotientGroup.congr _ _ a (pCore_map_iso 2 a))

private theorem profile_core_image (h : HypothesisF11 L S) (b : Bool) :
    (Q F₀ (base F₀ b)).map (G₀).subtype = (P (if b then 1 else 0)).pCoreIn 2 :=
  (reduced_base_Q_map h b).trans (reduced_parabolic_core h _).symm

private theorem profile_models (h : HypothesisF11 L S)
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L S i)) (b : Bool) :
    IsRankOneModel (M b ⧸ pCore 2 (M b)) := by
  let a := (graphLocalGroup F₀ (base F₀ b)).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  exact (reduced_actor_models_of_nonsolvable_parabolics h hns (base F₀ b)).of_equiv
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm

variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L S i))
    (hne : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := reducedSylow L S) 1
      ¬ IsElementaryAbelian 2 (reducedSylow L S ⧸
        ((parabolic L (reducedSylow L S) 1).pCoreIn 2).subgroupOf (reducedSylow L S)))
include h hc hb hcomm hns hne

/-- The genuine nonelementary source branch constructs the entire U₅
profile on the same marked quotient. Both original factors and the full
Borel two-core are retained; no model marking is an input. -/
theorem original_nonsolvable_nonElementary_marked_profile
    {X : Type*} [Group X] {endpoints : Fin 2 → Subgroup X}
    (quot : MarkedQuotient endpoints)
    (e : Iso (reducedAmalgam L S) quot.standardAmalgam)
    (split : SplitData quot.tits) (hrot : rotationOrder quot = 4) :
    ∃ m : ℕ, 0 < m ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
        (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2),
        Nonempty (UnitarySource.Combined.FiveProfile L R quot split k E m 0 1) := by
  have he : ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf R).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (R ⧸ ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf R) := by
    have hq : (Q F₀ (base F₀ true)).map (G₀).subtype = (P 1).pCoreIn 2 := profile_core_image h true
    rw [hq]
    exact ⟨QuadrangleStructure.original_core_normal_in_sylow 1,hne⟩
  let Ma := profile_models h hns false
  obtain ⟨m,hm,mb⟩ := original_borel_nonElementary_unitary_beta h hc hb hcomm Ma (profile_models h hns true) he
  have ma := (original_unitary_field_and_valences h hc hb hcomm Ma hm mb).1
  obtain ⟨k,hFk,hfink,hk,⟨ea⟩⟩ := ma
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  have hK : Nat.card k = (2^m)^2 := by rw [hk,←pow_mul,Nat.mul_comm m 2]
  let μ := (factorActorQuotient h false (hns 0)).trans ea
  have hunit : ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
      Nat.card E = (2^m)^2 ∧ (∀ x, J.conj x = x^(2^m)) ∧
        (Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* J.specialSubgroup) ∨
        Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rcases mb with hp | hs
    · obtain ⟨E,hFE,hfinE,J,hE,hconj,⟨eb⟩⟩ := hp
      exact ⟨E,hFE,hfinE,J,hE,hconj,Or.inr ⟨(factorActorQuotient h true (hns 1)).trans eb⟩⟩
    · obtain ⟨E,hFE,hfinE,J,hE,hconj,⟨eb⟩⟩ := hs
      exact ⟨E,hFE,hfinE,J,hE,hconj,Or.inl ⟨(factorActorQuotient h true (hns 1)).trans eb⟩⟩
  obtain ⟨E,hFE,hfinE,J,hE,hconj,hfactor⟩ := hunit
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (f := m*2)
    (by simpa only [Nat.card_eq_fintype_card,pow_mul,Nat.mul_comm 2 m] using hE)
  obtain ⟨hcard,_,hcent,hder,hphi,_⟩ := original_borel_unitary_beta_layers_from_marking h hc hb hcomm Ma hm mb
  have hq : (Q F₀ (base F₀ true)).map (G₀).subtype = (P 1).pCoreIn 2 := profile_core_image h true
  rw [hq] at hcard hcent hder hphi
  have hd : _root_.commutator ((P 1).pCoreIn 2) = center ((P 1).pCoreIn 2) := by
    apply Subgroup.map_injective ((P 1).pCoreIn 2).subtype_injective
    rw [_root_.commutator_def, map_commutator, ←MonoidHom.range_eq_map, Subgroup.range_subtype,
      ←centerIn_eq_map_center]
    exact hder.trans hcent.symm
  have hf : frattini ((P 1).pCoreIn 2) = center ((P 1).pCoreIn 2) := by
    apply Subgroup.map_injective ((P 1).pCoreIn 2).subtype_injective
    rw [←centerIn_eq_map_center]
    exact hphi.trans hcent.symm
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 m hm hE hconj
  obtain ⟨C,hC⟩ := exists_standard_basis J (2^m) hE hfixed
  have hfactor' : Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* (standardForm J).specialSubgroup) ∨
      Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* ProjectiveSpecialUnitaryMatrixGroup (standardForm J)) := by
    rcases hfactor with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · exact Or.inl ⟨f.trans (specialEquiv J C hC)⟩
    · exact Or.inr ⟨f.trans (projectiveEquiv J C hC)⟩
  obtain ⟨profile,_,_,_⟩ := QuadrangleStructure.marked_unitary_factor_profile quot
    ((intersectionToReduced h).trans e) (reduced_hypothesis h) split (standardForm J)
    hm hE hconj hK rfl hrot 0 1 (by decide) μ hfactor'
    (by rw [hcard,←pow_mul,Nat.mul_comm m 7]) hd hf
  exact ⟨m,hm,k,hFk,hfink,inferInstance,E,hFE,hfinE,inferInstance,⟨profile⟩⟩

/-- Apply the constructed source profile to the proved all-fields U₅
recognition theorem on this very quotient. -/
theorem original_nonsolvable_nonElementary_reduced_comparison
    {X : Type*} [Group X] {endpoints : Fin 2 → Subgroup X}
    (quot : MarkedQuotient endpoints)
    (e : Iso (reducedAmalgam L S) quot.standardAmalgam)
    (split : SplitData quot.tits) (hrot : rotationOrder quot = 4) :
    ∃ m : ℕ, 0 < m ∧ Nonempty (UnitarySource.Combined.FiveComparison quot e m false) := by
  obtain ⟨m,hm,k,hFk,hfink,hchk,E,hFE,hfinE,hchE,⟨profile⟩⟩ :=
    original_nonsolvable_nonElementary_marked_profile h hc hb hcomm hns hne quot e split hrot
  exact ⟨m,hm,UnitaryFiveSource.five_source_theorem quot e split h hrot k E m hm false profile⟩

/-- On the literal generated-source quotient, all three maps use its actual
quotient representatives and one common unitary model equivalence. -/
theorem original_nonsolvable_nonElementary_literal_comparison
    (quot : SourceQuotient L R) (split : SplitData quot.tits)
    (hrot : rotationOrder quot = 4) :
    ∃ (m : ℕ) (_ : 0 < m)
      (c : UnitarySource.Combined.FiveComparison quot
        (Assembly.UnitaryFourSource.literalMark h quot) m false),
      (∀ x : P 0, (c.comparison.left x : c.model.Carrier) =
        c.quotient (quot.q ⟨x,parabolic_le_generated 0 x.property⟩)) ∧
      (∀ x : commonBorel L R, (c.comparison.middle x : c.model.Carrier) =
        c.quotient (quot.q ⟨x,parabolic_le_generated 0 (commonBorel_le_parabolic 0 x.property)⟩)) ∧
      (∀ x : P 1, (c.comparison.right x : c.model.Carrier) =
        c.quotient (quot.q ⟨x,parabolic_le_generated 1 x.property⟩)) := by
  obtain ⟨m,hm,⟨c⟩⟩ := original_nonsolvable_nonElementary_reduced_comparison h hc hb hcomm
    hns hne quot (Assembly.UnitaryFourSource.literalMark h quot) split hrot
  exact ⟨m,hm,c,UnitarySource.Combined.five_literal_squares h quot m false c⟩

omit hne in
/-- Exhaustive profile selection on the nonsolvable commuting-edge branch.
This constructs the actual U₄ or U₅ actors and kernels, not just a row label. -/
theorem original_nonsolvable_commuting_one_marked_row
    {X : Type*} [Group X] {endpoints : Fin 2 → Subgroup X}
    (quot : MarkedQuotient endpoints)
    (e : Iso (reducedAmalgam L S) quot.standardAmalgam)
    (split : SplitData quot.tits) (hrot : rotationOrder quot = 4) :
    UnitarySource.Combined.Row.{_,_,0,0} L S quot split := by
  classical
  let := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := R) 1
  by_cases he : IsElementaryAbelian 2 (R ⧸ ((P 1).pCoreIn 2).subgroupOf R)
  · obtain ⟨m,hm,k,hFk,hfink,hchk,E,hFE,hfinE,hchE,_,hE,⟨profile⟩⟩ :=
      original_borel_elementary_marked_profile h hc hb hcomm
        (profile_models h hns false) (profile_models h hns true) he
    exact .four k E m hm hE false profile
  · obtain ⟨m,hm,k,hFk,hfink,hchk,E,hFE,hfinE,hchE,⟨profile⟩⟩ :=
      original_nonsolvable_nonElementary_marked_profile h hc hb hcomm hns he quot e split hrot
    exact .five k E m hm false profile

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
