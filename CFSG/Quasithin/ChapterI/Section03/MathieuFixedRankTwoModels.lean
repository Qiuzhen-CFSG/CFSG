module
public import CFSG.Quasithin.ChapterI.Section03.MathieuFixedSymplectic
public import Theory.SpecificGroups.Triality.InvolutionFixedComponents
public import Theory.SpecificGroups.Triality.InvolutionFixedRank
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.PerfectThreeRank
public import Theory.SpecificGroups.ReeF4.AutomorphismTwoRank
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.AtlasPort.LinearGroups.G2.PerfectTwoNormalizer
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.OuterComponents
public import Theory.SpecificGroups.G2Even.TwoRank.Elementary
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Order
public import Theory.SpecificGroups.SymplecticFour.FixedComponents
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectSubgroups
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# Rank-two exclusions for involution-fixed Mathieu components

A quasisimple cover of M₂₂ has three-rank at least two: otherwise its
cyclic Sylow three-subgroup would map onto a cyclic Sylow of M₂₂. The
actual parabolic bounds therefore exclude inner involutions in binary
symplectic, G₂, triality and Ree F₄ models. Ree involutions are inner.
Outer G₂ and triality involutions identify the fixed component with the
derived smaller-field model. Its two-rank, and the small G₂ order, exclude
M₂₂. The symplectic field and graph cases similarly use the actual derived
Sp₄ and Suzuki fixed groups. The order of SU₅(4) excludes its projective row.

These proofs keep the original component's center quotient. In particular,
no general invariance of prime rank under a central quotient is assumed.
The remaining list is the three odd Lie families, binary PSU₄, and McL.
Hall.OddNormalizer.PushingUpRankTwoProperModels applies it to the original
exterior cubic; Hall.OddNormalizer applies it to the literal Hall witness.

Source: Aschbacher--Smith 4.2.13, printed p.612, Theorem B, p.33, and the
involution and parabolic calculations cited in the imported model modules.
The separate odd-local endgame is on printed p.623.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.MathieuPumpup
open Sporadic.Mathieu

private theorem mathieu_quotient_rank {B : Type*} [Group B] [Finite B]
    (e : (B ⧸ center B) ≃* M22) : 2 ≤ primeRank 3 B := by
  by_contra hr
  let P : Sylow 3 B := Sylow.nonempty.some
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have h := P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega)) f hf
  rw [m22_primeRank_three] at h
  omega

variable {S : Type*} [Group S]

/-- The inner triality row has derived three-rank at most one; the outer row
identifies a simple smaller carrier of two-rank at least five. -/
theorem HasMathieuFixedComponent.not_binary_triality (h : HasMathieuFixedComponent S)
    {n : ℕ} (hn : 1 ≤ n) (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) S) : False := by
  classical
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff S n (by omega)).mp hm
  obtain ⟨a,ha,B,hB,⟨b⟩⟩ := h.of_mulEquiv e
  let D := B.subgroupOf a.fixedSubgroup
  have hD : IsComponent a.fixedSubgroup D := hB.2
  let := hD.2
  let db : D ≃* B := subgroupOfEquivOfLe hB.1
  have hr : 2 ≤ primeRank 3 D := by
    rw [primeRank_equiv 3 db]
    exact mathieu_quotient_rank b
  by_cases hi : a ∈ MulAut.innerSubgroup (Triality.Standard.BinaryCarrier n (show 0 < n from hn))
  · have hle : D ≤ commutator a.fixedSubgroup := by
      calc
        D = ⁅D,D⁆ := (commutator_eq_self (H := D)).symm
        _ ≤ ⁅(⊤ : Subgroup a.fixedSubgroup),⊤⁆ := commutator_mono le_top le_top
    have hb := (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hle) (inclusion_injective hle)).trans
      (Triality.Standard.InvolutionFixedRank.inner_fixed_derived_threeRank_le_one n (by omega) a ha hi)
    omega
  · obtain ⟨m,hm,_,E,_,⟨d⟩,hrank⟩ :=
      Triality.Standard.EvenField.outer_fixed_component n (by omega) a ha hi D hD
    let : IsSimpleGroup D := d.isSimpleGroup
    let : IsSimpleGroup B := db.symm.isSimpleGroup
    let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := db.toMonoidHom) db.surjective
    let b₀ : B ≃* M22 := QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq
        (center_eq_bot_of_simple_perfect (G := B))).symm.trans b)
    have hsmall : primeRank 2 D ≤ 4 := by
      rw [primeRank_equiv 2 (db.trans b₀)]
      exact m22_twoRank_le_four
    omega

/-- Every Ree involution is inner, and its perfect fixed subgroups have
three-rank at most one in the actual two-local normalizer. -/
theorem HasMathieuFixedComponent.not_ree_f4 [IsSimpleGroup S] [Group.IsPerfect S]
    (h : HasMathieuFixedComponent S) {m : ℕ} (hm : 1 ≤ m)
    (e : S ≃* ReeF4.Model m) : False := by
  classical
  let : IsSimpleGroup (ReeF4.Model m) := e.symm.isSimpleGroup
  let : Group.IsPerfect (ReeF4.Model m) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨a,ha,B,hB,⟨b⟩⟩ := h.of_mulEquiv e
  let := hB.quasisimple
  obtain ⟨x,hx⟩ := ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.inner_of_sq_eq_one hm
    a (by simpa only [ha] using pow_orderOf_eq_one a)
  have ho : orderOf x = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot (center_eq_bot_of_simple_perfect (G := ReeF4.Model m)) x).symm.trans
      ((congrArg orderOf hx).trans ha)
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,ho,pow_one])
  have hne : zpowers x ≠ ⊥ := by
    intro hh
    have hx1 := zpowers_eq_bot.mp hh
    simp [hx1] at ho
  have hN : B ≤ normalizer (zpowers x : Set (ReeF4.Model m)) := by
    apply hB.1.trans
    rw [←hx,MulAut.fixedSubgroup_conj]
    rw [←centralizer_closure ({x} : Set (ReeF4.Model m)),←zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hr := ReeF4.ConverseParabolics.perfect_two_normalizer_threeRank_le_one hm B (zpowers x) hp hne hN
  have hl := mathieu_quotient_rank b
  omega


/-- The inner G₂ parabolic bound and the outer smaller-field component
identification exclude M₂₂, including the derived binary endpoint. -/
theorem HasMathieuFixedComponent.not_binary_g2 (h : HasMathieuFixedComponent S)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassificationModels.IsG2At S (2 ^ n)) : False := by
  classical
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hn)
  let : IsSimpleGroup (Atlas.G2.Model F) := Atlas.G2.isSimple hq
  let : Group.IsPerfect (Atlas.G2.Model F) := Atlas.G2.isPerfect hq
  obtain ⟨a,ha,B,hB,⟨b⟩⟩ := h.of_mulEquiv e
  let := hB.quasisimple
  by_cases hi : ∃ x : Atlas.G2.Model F, a = MulAut.conj x
  · obtain ⟨x,rfl⟩ := hi
    have ho : orderOf x = 2 :=
      (MulAut.conj_orderOf_of_center_eq_bot (center_eq_bot_of_simple_perfect (G := Atlas.G2.Model F)) x).symm.trans ha
    have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers,ho,pow_one])
    have hne : zpowers x ≠ ⊥ := by
      intro hh
      have hx1 := zpowers_eq_bot.mp hh
      simp [hx1] at ho
    have hN : B ≤ normalizer (zpowers x : Set (Atlas.G2.Model F)) := by
      apply hB.1.trans
      rw [MulAut.fixedSubgroup_conj]
      rw [←centralizer_closure ({x} : Set (Atlas.G2.Model F)),←zpowers_eq_closure]
      exact Subgroup.centralizer_le_normalizer _
    have hr := Atlas.G2.PerfectSubgroups.perfect_subgroup_two_normalizer_odd_rank_le_one
      (zpowers x) hp hne hq B hN (by decide : Odd 3)
    have hl := mathieu_quotient_rank b
    omega
  · let D := B.subgroupOf a.fixedSubgroup
    have hD : IsComponent a.fixedSubgroup D := hB.2
    let db : D ≃* B := subgroupOfEquivOfLe hB.1
    obtain ⟨σ,m,hm,_,_,hc,_,_,E,_,_,⟨d⟩,_⟩ :=
      Atlas.G2.EvenFieldFixedResidual.outer_fixed_component_descent_of_equiv
        (MulEquiv.refl _) hn hF a ha (fun x hx => hi ⟨x,hx⟩) D hD
    let K := Atlas.G2.EvenFieldFixedResidual.fixedField σ
    let : IsSimpleGroup (commutator (Atlas.G2.Model K)) :=
      Atlas.G2.EvenFieldFixedResidual.derived_isSimple
    let : IsSimpleGroup B := (db.symm.trans d).isSimpleGroup
    let b₀ : B ≃* M22 := QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq
        (center_eq_bot_of_simple_perfect (G := B))).symm.trans b)
    let em : commutator (Atlas.G2.Model K) ≃* M22 :=
      d.symm.trans (db.trans b₀)
    by_cases hsmall : m = 1
    · have hcard := Atlas.G2.DerivedEvenOrder.card_derived_binary
        (F := K) (by simpa [hsmall] using hc)
      rw [Nat.card_congr em.toEquiv,m22_order] at hcard
      norm_num at hcard
    · let er := Atlas.G2.DerivedEvenOrder.derivedEquivModel (by omega : 2 ≤ m) hc
      have hr := Atlas.G2.EvenTwoRank.rank_ge K hc
      rw [primeRank_equiv 2 (er.symm.trans em)] at hr
      have hu := m22_twoRank_le_four
      omega

/-- The proved order of SU₅(4), and hence its projective quotient, is prime
to seven and eleven, whereas a Mathieu component forces both factors. -/
theorem HasMathieuFixedComponent.not_unitary_five_four (h : HasMathieuFixedComponent S)
    (hm : ClassicalGroup.IsPSU S 5 4) : False := by
  classical
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  have hcard : Nat.card F = 16 := hF
  let : CharP F 2 := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hcard
  obtain ⟨a⟩ := Theory.SpecificGroups.UnitaryFive.projective_equiv_identity_four J hcard hconj
  let J₀ := BenderSuzuki.MatrixGroups.HermitianForm.IdentityGram.identityGram J
  have hd := (h.of_mulEquiv (e.trans a)).card_dvd
  have hd' := hd.trans (Subgroup.card_dvd_of_surjective (Theory.SpecificGroups.UnitaryFive.project J₀) (Theory.SpecificGroups.UnitaryFive.project_surjective J₀))
  rw [Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.card_specialSubgroup_four
    J₀ hcard hconj rfl] at hd'
  norm_num at hd'


-- The symplectic exclusion is re-exported from MathieuFixedSymplectic.

/-- The proper-overcomponent models still requiring an involution-fixed
Mathieu exclusion. Every family retains its actual model isomorphism. -/
@[expose] def MathieuProperModelResidue (S : Type*) [Group S] : Prop :=
  RemainingMathieuLargeOddModel S ∨
  (∃ n, 1 ≤ n ∧ ClassicalGroup.IsPSU S 4 (2 ^ n)) ∨
  Nonempty (S ≃* Sporadic.LeechRelated.McL.Carrier)

/-- Remove the five proved rank-two rows from the actual Theorem B list. -/
theorem HasMathieuFixedComponent.proper_model_residue [IsSimpleGroup S] [Group.IsPerfect S]
    (h : HasMathieuFixedComponent S) (hm : ChapterA.Section02.IsTheoremBModel S) :
    MathieuProperModelResidue S := by
  rcases h.remaining_rows hm with ho | hr | hmc
  · exact Or.inl ho
  · rcases hr with hu | hfive | ⟨n,hn,hsp⟩ | ⟨n,hn,hg⟩ | ⟨n,hn,ht⟩ | ⟨m,hm,⟨er⟩⟩
    · exact Or.inr (Or.inl hu)
    · exact (h.not_unitary_five_four hfive).elim
    · exact (h.not_binary_symplectic hn hsp).elim
    · exact (h.not_binary_g2 hn hg).elim
    · exact (h.not_binary_triality hn ht).elim
    · exact (h.not_ree_f4 hm er).elim
  · exact Or.inr (Or.inr hmc)

end CFSG.Quasithin.ChapterI.MathieuPumpup
