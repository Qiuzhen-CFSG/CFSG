module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank
public import Theory.SpecificGroups.Janko4.TwoRankLower
public import Theory.Mathieu.M24.Properties.AutomorphismTwoRank
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms
public import Theory.SpecificGroups.BinaryLinear.AutomorphismTwoRank.Five
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Order

/-!
# Quasisimple subgroups normalized by a full J₄ Sylow subgroup

The native elementary subgroup of order 2¹¹ forces automorphism two-rank
at least eleven for a subgroup on which the full Sylow acts faithfully.
Perfect central descent preserves that action. The factor seven of the
source plane section also survives central descent, since the J₄ order
has only one factor seven.

The A.3.6 three-cover list is excluded by these rank and order constraints.
For a simple subgroup, the complete Theorem C catalogue leaves only J₄:
the defining two-parts bound the field sizes, exact orders remove the
remaining Lie-type rows, and the native automorphism bounds remove the
smaller Mathieu groups. Equality of orders then makes the subgroup the
whole group. The actual source application in Components/Janko uses this
to exclude trivial two-core in the original plane image in JT/O₂(JT).
It does not classify arbitrary proper Sylow overgroups of J₄.

Source: Aschbacher--Smith A.2.3, A.3.6 and 12.9.3, printed pp.33,
43--45 and 858--859 of refs/quasithin.pdf. The rank-and-order proof follows
the checked MathieuRank argument; all concrete facts retain the source
attributions of their imported carrier modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank

private theorem two_exponent_le_twentyone {k : ℕ} (h : 2 ^ k ∣ 86775571046077562880) : k ≤ 21 := by
  by_contra! hk
  have hd : 4194304 ∣ 86775571046077562880 := (pow_dvd_pow 2 hk).trans h
  norm_num at hd

variable {X : Type*} [Group X] [Finite X]

/-- The native J₄ order and rank-eleven automorphism obstruction exclude all binary rank-one carriers. -/
theorem not_bender_of_janko_order
    (hd : Nat.card X ∣ 86775571046077562880) (hr : 11 ≤ primeRank 2 (MulAut X)) :
    ¬ ClassificationModels.IsBenderModel X := by
  intro hm
  cases hm with
  | linear n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by
      simpa only [Nat.card_eq_fintype_card] using hF)
    have hc : Nat.card X = 2^n * ((2^n)^2 - 1) := by
      rw [Nat.card_congr e.toEquiv,← Nat.card_congr (Theory.PSL2.sl2QuotientEquiv F).toEquiv,
        GorensteinWalter.sl2_card_formula,hF]
    have hn21 : n ≤ 21 := two_exponent_le_twentyone (by
      apply dvd_trans (dvd_mul_right _ ((2^n)^2 - 1))
      rwa [←hc])
    have hn11 : 11 ≤ n := by
      rw [primeRank_equiv 2 (MulAut.congr e)] at hr
      exact hr.trans (Theory.PSL2.BinaryAutomorphismRank.psl2_automorphism_two_rank_le hn hF)
    rw [hc] at hd
    interval_cases n <;> norm_num at hd
  | unitary n hn hm =>
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv X e.toEquiv
    have hc := HermitianForm.BinarySylowOrder.cube_dvd_card_projective J (by omega) hF hconj
    rw [←Nat.card_congr e.toEquiv,←pow_mul] at hc
    have hn21 := two_exponent_le_twentyone (hc.trans hd)
    rw [primeRank_equiv 2 (MulAut.congr e)] at hr
    have hb := HermitianForm.EvenTwoRank.automorphism_two_rank_le J hn hF hconj
    omega
  | suzuki m hm he =>
    obtain ⟨e⟩ := he
    have hc := (SuzukiRootSubgroup m).card_subgroup_dvd_card
    rw [suzukiRootSubgroup_card m (by omega),←Nat.card_congr e.toEquiv,←pow_mul] at hc
    have hn21 := two_exponent_le_twentyone (hc.trans hd)
    rw [primeRank_equiv 2 (MulAut.congr e)] at hr
    have hb := suzuki_automorphism_two_rank m (by omega)
    omega

/-- The defining two-part and automorphism rank leave only PSL₃(64) and PSL₃(128); neither order divides the J₄ order. -/
theorem not_binary_three_of_janko_order
    (hd : Nat.card X ∣ 86775571046077562880) (hr : 11 ≤ primeRank 2 (MulAut X))
    {n : ℕ} (hn : 1 ≤ n) : ¬ ClassicalGroup.IsPSL X 3 (2^n) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  have hc := (Matrix.PSL3.LinearThree.unipotent F).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotent F,hF,←pow_mul,←Nat.card_congr e.toEquiv] at hc
  have hn21 := two_exponent_le_twentyone (hc.trans hd)
  rw [primeRank_equiv 2 (MulAut.congr e),Matrix.PSL3Even.automorphism_two_rank_eq F (by omega) hF] at hr
  rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF] at hd
  have hn7 : n ≤ 7 := by omega
  have hn6 : 6 ≤ n := by omega
  interval_cases n <;> norm_num at hd

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank

/-- The actual elementary kernel of order 2048 gives the lower bound in every J₄ Sylow subgroup. -/
theorem eleven_le_sylow_rank {G : Type*} [Group G] [Finite G]
    (e : G ≃* Janko4.Model) (S : Sylow 2 G) : 11 ≤ primeRank 2 S := by
  rw [←S.primeRank_eq,primeRank_equiv 2 e]
  exact Janko4.eleven_le_twoRank

/-- A faithful action of the full original Sylow transfers its rank-eleven lower bound to the normalized subgroup. -/
theorem eleven_le_automorphism_rank {G : Type*} [Group G] [Finite G]
    (e : G ≃* Janko4.Model) (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hf : (S : Subgroup G) ⊓ centralizer (B : Set G) = ⊥) :
    11 ≤ primeRank 2 (MulAut B) := by
  let f := B.normalizerMonoidHom.comp (inclusion hn)
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hf]
    refine ⟨a.property,?_⟩
    change inclusion hn a ∈ B.normalizerMonoidHom.ker at ha
    rwa [normalizerMonoidHom_ker] at ha
  exact (eleven_le_sylow_rank e S).trans (Theory.GroupTheory.primeRank_le_of_injective 2 f hi)

/-- Perfect central descent preserves the faithful action and its automorphism-rank obstruction. -/
theorem eleven_le_central_quotient_automorphism_rank
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* Janko4.Model) (S : Sylow 2 G) (B : Subgroup G)
    [Group.IsPerfect B]
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hf : (S : Subgroup G) ⊓ centralizer (B : Set G) = ⊥) :
    11 ≤ primeRank 2 (MulAut (B ⧸ center B)) :=
  (eleven_le_automorphism_rank e S B hn hf).trans
    (Theory.GroupTheory.primeRank_le_of_injective 2 (Subgroup.quotientAut (center B)) MulAut.quotient_center_injective)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank

namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank
open Subgroup Theory.GroupTheory

/-- The source factor seven survives perfect central descent under the actual J₄ order bound. -/
theorem seven_dvd_central_quotient
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (hd : Nat.card G ∣ 86775571046077562880) (h7 : 7 ∣ Nat.card G) :
    7 ∣ Nat.card (G ⧸ center G) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let f : PerfectCentralCovering.Cover G (G ⧸ center G) := {
    toMonoidHom := QuotientGroup.mk' (center G)
    surjective := QuotientGroup.mk'_surjective _
    isPerfect := inferInstance
    ker_le_center := (QuotientGroup.ker_mk' _).le }
  have hz : ¬ 7 ∣ Nat.card (center G) := by
    have hk := f.not_dvd_card_kernel_of_square_not_dvd (p := 7) (by
      intro hh
      have := hh.trans ((card_quotient_dvd_card (center G)).trans hd)
      norm_num at this)
    simpa only [f,QuotientGroup.ker_mk'] using hk
  have hc := card_eq_card_quotient_mul_card_subgroup (center G)
  rw [hc] at h7
  exact ((by decide : Nat.Prime 7).dvd_mul.mp h7).resolve_right hz

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank

namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank
open Subgroup Theory.GroupTheory Chapter1.Section02.LocalModels

/-- The complete A.3.6 three-cover list is incompatible with the actual J₄ order and the central-quotient action. -/
theorem not_three_cover_of_janko_order
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (hd : Nat.card G ∣ 86775571046077562880) (h7 : 7 ∣ Nat.card G)
    (hr : 11 ≤ primeRank 2 (MulAut (G ⧸ center G))) : ¬ ThreeCoverModel G := by
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  let : Group.IsPerfect (G ⧸ center G) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center G))
      (QuotientGroup.mk'_surjective _)
  have hdQ := (card_quotient_dvd_card (center G)).trans hd
  have h7Q := seven_dvd_central_quotient hd h7
  intro hm
  cases hm with
  | classical u q hq hm =>
    rcases ClassicalCoverQuotient.models u q hq hm with hm | hm | ⟨n,hn,hm⟩
    · exact MathieuRank.not_odd_of_large_automorphism_rank h7Q (by omega) hm
    · exact not_bender_of_janko_order hdQ hr hm
    · exact not_binary_three_of_janko_order hdQ hr hn hm
  | alternating_six hm =>
    obtain ⟨e⟩ := hm.2.2
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at h7Q
    norm_num at h7Q
  | alternating_seven hm =>
    obtain ⟨e⟩ := hm.2.2
    let a : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
      MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
        7 (by decide) (by decide))
    rw [primeRank_equiv 2 (MulAut.congr e),←primeRank_equiv 2 a] at hr
    have hb : primeRank 2 (Equiv.Perm (Fin 7)) ≤ 4 :=
      primeRank_le_of_prime_pow_not_dvd (by
        rw [Nat.card_perm,Nat.card_fin]
        norm_num)
    omega
  | mathieu hm =>
    obtain ⟨e⟩ := hm.2.2
    rw [primeRank_equiv 2 (MulAut.congr e)] at hr
    have hb := Sporadic.Mathieu.m22_automorphism_twoRank_le_five
    omega

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank

namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank
open Subgroup Theory.GroupTheory

/-- A quasisimple SQTK group with these J₄ order and action constraints is simple; every three-cover alternative is discharged. -/
theorem simple_of_janko_order
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (hsq : IsSQTK KnownSimple.IsKnownSimple G) (hcore : pCore 2 G = ⊥)
    (hd : Nat.card G ∣ 86775571046077562880) (h7 : 7 ∣ Nat.card G)
    (hr : 11 ≤ primeRank 2 (MulAut (G ⧸ center G))) : IsSimpleGroup G := by
  let : IsQuasisimple (⊤ : Subgroup G) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have ht : (⊤ : Subgroup G).IsCComponent :=
    (show IsComponent G ⊤ from ⟨.top,inferInstance⟩).isCComponent
  rcases quasisimple_containing_component_models_knownSimple hsq hcore ht with h | h
  · let := h.1
    exact (topEquiv (G := G)).symm.isSimpleGroup
  · have hc := Nat.card_congr (topEquiv (G := G)).toEquiv
    let a : ((⊤ : Subgroup G) ⧸ center (⊤ : Subgroup G)) ≃* (G ⧸ center G) :=
      QuotientGroup.congr _ _ topEquiv (by
        apply le_antisymm
        · rintro _ ⟨x,hx,rfl⟩
          exact (centerCongr topEquiv ⟨x,hx⟩).property
        · intro y hy
          exact ⟨topEquiv.symm y,(centerCongr topEquiv.symm ⟨y,hy⟩).property,rfl⟩)
    exact (not_three_cover_of_janko_order (hc.symm ▸ hd) (hc.symm ▸ h7)
      (by rwa [primeRank_equiv 2 (MulAut.congr a)]) h.2).elim

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank
open Subgroup Theory.GroupTheory
open scoped MatrixGroups

private theorem not_small_alternating
    {G : Type*} [Group G] [Finite G]
    (h7 : 7 ∣ Nat.card G) (hr : 11 ≤ primeRank 2 (MulAut G))
    {n : ℕ} (hn : n ≤ 8) (e : G ≃* alternatingGroup (Fin n)) : False := by
  have hn7 : 7 ≤ n := by
    have hh := h7.trans ((Nat.card_congr e.toEquiv).symm ▸
      (alternatingGroup (Fin n)).card_subgroup_dvd_card)
    rw [Nat.card_perm,Nat.card_fin] at hh
    exact (Nat.Prime.dvd_factorial (by decide : Nat.Prime 7)).mp hh
  have hncase : n = 7 ∨ n = 8 := by omega
  rcases hncase with rfl | rfl
  · let a : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
      MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
        7 (by decide) (by decide))
    rw [primeRank_equiv 2 (MulAut.congr e),←primeRank_equiv 2 a] at hr
    have hb : primeRank 2 (Equiv.Perm (Fin 7)) ≤ 4 :=
      primeRank_le_of_prime_pow_not_dvd (by rw [Nat.card_perm,Nat.card_fin]; norm_num)
    omega
  · have hb := BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le
    rw [primeRank_equiv 2 (MulAut.congr
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)] at hb
    rw [primeRank_equiv 2 (MulAut.congr e)] at hr
    omega

private theorem not_rank_two
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] [Group.IsPerfect G]
    (hd : Nat.card G ∣ 86775571046077562880) (h7 : 7 ∣ Nat.card G)
    (hr : 11 ≤ primeRank 2 (MulAut G))
    {n : ℕ} (hm : ChapterA.Section02.IsTheoremCRankTwoModel G n) : False := by
  have hsmall : ¬ 4194304 ∣ Nat.card G := by
    intro hh
    have := hh.trans hd
    norm_num at this
  have large_power {a b : ℕ} (hh : 22 ≤ a*b) : 4194304 ∣ (2^a)^b := by
    rw [←pow_mul]
    exact pow_dvd_pow 2 hh
  cases hm with
  | linear hn hm => exact not_binary_three_of_janko_order hd hr hn hm
  | symplectic hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
    have hu := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)).card_subgroup_dvd_card
    rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,hF,
      ←Nat.card_congr a.toEquiv,←pow_mul] at hu
    have hn21 := two_exponent_le_twentyone (hu.trans hd)
    rw [Nat.card_congr a.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF] at hd
    have hn5 : n ≤ 5 := by omega
    interval_cases n <;> norm_num at hd
  | g2 hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hu : 2^(n*6) ∣ Nat.card G := by
      rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model,hF]
      rw [pow_mul]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    have hn21 := two_exponent_le_twentyone (hu.trans hd)
    rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model,hF] at hd
    have hn3 : n ≤ 3 := by omega
    interval_cases n <;> norm_num at hd
  | triality hn hm =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G n (by omega)).mp hm
    let P := Triality.Standard.binaryParameters n (by omega : 0 < n)
    have hu := (Triality.Standard.Parabolics.unipotent P).card_subgroup_dvd_card
    rw [Triality.Standard.Parabolics.card_unipotent_binary P rfl] at hu
    change (2^n)^12 ∣ Nat.card (Triality.Standard.BinaryCarrier n _) at hu
    rw [←Nat.card_congr e.toEquiv] at hu
    have hn21 := two_exponent_le_twentyone (by simpa only [←pow_mul] using hu.trans hd)
    have he : n = 1 := by omega
    subst n
    rw [Nat.card_congr e.toEquiv,
      Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.card_binaryCarrier] at hd
    norm_num at hd
  | ree_f4 m _ _ he =>
    obtain ⟨e⟩ := he
    have hu := (ReeF4.Parabolics.unipotent m).card_subgroup_dvd_card
    rw [ReeF4.Parabolics.card_unipotent,←Nat.card_congr e.toEquiv] at hu
    exact hsmall ((large_power (by omega : 22 ≤ (2*m+1)*12)).trans hu)
  | symplectic_derived _ he =>
    rw [Nat.card_congr (he.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv,
      nat_card_alternatingGroup,Nat.card_fin] at h7
    norm_num at h7
  | g2_derived _ he =>
    obtain ⟨b⟩ := Atlas.G2.nonempty_commutator_binary_equiv_psu3
    have hm : ClassicalGroup.IsPSU G 3 3 := by
      refine ⟨GaloisField 3 2,inferInstance,inferInstance,ABG.unitaryForm 3 3 1 (by decide),
        GaloisField.card 3 2 (by decide),?_,⟨he.some.trans b⟩⟩
      intro x
      change iterateFrobeniusEquiv (GaloisField 3 2) 3 1 x = x^3
      simp only [iterateFrobeniusEquiv_def,pow_one]
    exact MathieuRank.not_odd_of_large_automorphism_rank h7 (by omega) (.unitary_three 3 (by decide) (by decide) hm)
  | tits _ he =>
    rw [Nat.card_congr he.some.toEquiv,Tits.parrottGroup_card] at hd
    norm_num at hd

private theorem held_seven_square : 49 ∣ Nat.card Held.He := by
  have ho : MulAction.orbit Held.He (0 : Fin 2058) = Set.univ := by
    ext x
    simp only [Set.mem_univ,iff_true]
    obtain ⟨g,hg⟩ := Held.Transitivity.exists_move_zero x
    exact ⟨g,hg⟩
  have hc := (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Held.He (0 : Fin 2058))).symm
  rw [Nat.card_prod,ho,Nat.card_congr (Equiv.Set.univ _),Nat.card_fin] at hc
  rw [hc]
  exact dvd_mul_of_dvd_left (by decide : 49 ∣ 2058) _

/-- The full simple Theorem C catalogue leaves only the actual J₄ carrier under the original order, seven-section and rank constraints. -/
theorem janko_of_simple_models
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] [Group.IsPerfect G]
    (hd : Nat.card G ∣ 86775571046077562880) (h7 : 7 ∣ Nat.card G)
    (hr : 11 ≤ primeRank 2 (MulAut G))
    (hm : ChapterA.Section02.IsTheoremCModel G) : Nonempty (G ≃* Janko4.Model) := by
  cases hm with
  | alternating n hn he => exact (not_small_alternating h7 hr hn he.some).elim
  | odd hm => exact (MathieuRank.not_odd_of_large_automorphism_rank h7 (by omega) hm).elim
  | bender hm => exact (not_bender_of_janko_order hd hr hm).elim
  | rank_two _ hm => exact (not_rank_two hd h7 hr hm).elim
  | linear_binary n hn hm =>
    rcases hn with rfl | rfl
    · exact (not_small_alternating h7 hr (by decide) (AlternatingEight.modelEquiv hm)).elim
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let := Fintype.ofFinite F
      let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
        simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
      let a := e.trans (Atlas.fieldEquivPSL 5 f)
      rw [primeRank_equiv 2 (MulAut.congr a)] at hr
      have hb := BinaryLinear.AutomorphismTwoRank.psl5_two_rank_le
      omega
  | sporadic hm =>
    change (∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧
      Nonempty (G ≃* name.Carrier)) ∨ Nonempty (G ≃* Janko1.Model) at hm
    rcases hm with ⟨name,hne,⟨e⟩⟩ | he
    · cases name with
      | m11 =>
        change G ≃* Sporadic.Mathieu.M11 at e
        rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m11_order] at h7
        norm_num at h7
      | m12 =>
        change G ≃* Sporadic.Mathieu.M12 at e
        rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m12_order] at h7
        norm_num at h7
      | m22 =>
        change G ≃* Sporadic.Mathieu.M22 at e
        rw [primeRank_equiv 2 (MulAut.congr e)] at hr
        exact (by have := Sporadic.Mathieu.m22_automorphism_twoRank_le_five; omega)
      | m23 =>
        change G ≃* Sporadic.Mathieu.M23 at e
        rw [primeRank_equiv 2 (MulAut.congr e)] at hr
        exact (by have := Sporadic.Mathieu.m23_automorphism_twoRank_le_four; omega)
      | m24 =>
        change G ≃* Sporadic.Mathieu.M24 at e
        rw [primeRank_equiv 2 (MulAut.congr e)] at hr
        have hb := Sporadic.Mathieu.m24_automorphism_rank_le_six
          Sporadic.Mathieu.M24InvolutionCentralizers.center_eq_bot
        omega
      | j2 =>
        change G ≃* Sporadic.LeechRelated.J2.Carrier at e
        rw [Nat.card_congr e.toEquiv,Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
        norm_num at hd
      | j3 => exact (hne rfl).elim
      | j4 => exact ⟨e⟩
      | hs =>
        change G ≃* Sporadic.LeechRelated.HS.Carrier at e
        rw [Nat.card_congr e.toEquiv,Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier] at hd
        norm_num at hd
      | he =>
        change G ≃* Held.He at e
        have hh := held_seven_square.trans ((Nat.card_congr e.toEquiv) ▸ hd)
        norm_num at hh
      | ru =>
        change G ≃* Rudvalis.Model at e
        rw [Nat.card_congr e.toEquiv,Rudvalis.model_card] at hd
        norm_num at hd
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv,Janko1.card_model] at hd
      norm_num at hd

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank

namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank
open Subgroup Theory.GroupTheory

/-- A quasisimple SQTK subgroup containing a seven-section and admitting the faithful action of a full J₄ Sylow is the whole ambient group. -/
theorem eq_top_of_quasisimple_faithful_sylow
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* Janko4.Model) (S : Sylow 2 G) (B : Subgroup G)
    [IsQuasisimple B] (hsq : IsSQTK KnownSimple.IsKnownSimple B)
    (hcore : pCore 2 B = ⊥) (h7 : 7 ∣ Nat.card B)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hf : (S : Subgroup G) ⊓ centralizer (B : Set G) = ⊥) : B = ⊤ := by
  have hd : Nat.card B ∣ 86775571046077562880 := by
    have hh := B.card_subgroup_dvd_card
    rwa [Nat.card_congr e.toEquiv,Janko4.Cardinality.model_card] at hh
  let : IsSimpleGroup B := simple_of_janko_order hsq hcore hd h7
    (eleven_le_central_quotient_automorphism_rank e S B hn hf)
  have hm := ChapterA.Section02.theoremC_knownSimple (G := B) inferInstance
    (Group.IsPerfect.not_isMulCommutative B) hsq.stronglyQuasithin hsq.isKGroup
  obtain ⟨a⟩ := janko_of_simple_models hd h7 (eleven_le_automorphism_rank e S B hn hf) hm
  exact B.eq_top_of_card_eq ((Nat.card_congr a.toEquiv).trans (Nat.card_congr e.toEquiv).symm)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank
