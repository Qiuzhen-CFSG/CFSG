module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionUnitaryFive
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOvercomponent
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalNormalizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSylow
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedCenter
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.Containing
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankTwoPerfect
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.G2Perfect
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.TrialityPerfect
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ReePerfect
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RudvalisOddRank
public import Theory.SpecificGroups.Classical.PairedOddRank
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.SpecificGroups.SU3.EvenFourCore.SylowStructure
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion.Normalizer
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality
public import Theory.Mathieu.M12.Properties.Order
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.Tits.SolvableSylowOvergroups

/-!
# Right maximality of the special U₅(4) amalgam

The actual line residual has quotient SU₃(4) = PSU₃(4). This simple
section survives solvable kernels, has five-rank two and order divisible
by thirteen, and its Sylow derived subgroup is elementary of order four.
The last fact excludes odd-model and noncentral-Fitting overcomponents.
After quotienting the containing component by its center, the complete
Theorem C catalogue gives equality: five-rank excludes proper rank-two
and Rudvalis embeddings; divisibility by thirteen excludes the small
alternating, binary and remaining sporadic carriers. The Bender and Tits
rows use their proper Sylow-overgroup theorems. Perfectness lifts equality
through the original center.

For the prepared U₅(4) pair, S lies in the right residual K = O²(H), so
O₂(H) = O₂(K). Every containing local component J has O₂(J) ≤ O₂(K).
The literal image of K in J/O₂(J) therefore retains its SU₃(4) section
and full Sylow normalization; the preceding non-enlargement theorem
forces K = J. The existing common-Sylow and enlarged-core identities
then give the original normalizer conditions of 5.3.

This discharges the U₅(4) paragraph of 5.2.8, retaining the actual
comparison and whole overlap. Original uniqueness stays in Preparation;
exhaustive amalgam comparison and ambient recognition remain necessary.
Source: Aschbacher–Smith 5.2.8, printed p.652, invoking 1.2.8(4),
printed pp.506–507 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFiveMaximal
open BenderSuzuki.MatrixGroups
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {X Y : Type*} [Group X] [Group Y]

private theorem projective_model (h : ChapterF.Source.IsSU X 3 4) : ClassicalGroup.IsPSU X 3 4 := by
  obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := h
  exact ⟨F,inferInstance,inferInstance,J,hF,hc,
    ⟨e.trans (HermitianForm.EvenProjectiveComparison.specialProjectiveEquiv J (by decide : Even 2) hc)⟩⟩

private theorem model_simple (h : ClassicalGroup.IsPSU X 3 4) : IsSimpleGroup X := by
  obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := h
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hF hc
  let := BenderSuzuki.External.huppert_II_10_13 J 4 (by decide) hF hf
  exact e.isSimpleGroup

private theorem model_card (h : ClassicalGroup.IsPSU X 3 4) : Nat.card X = 62400 := by
  obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv,Representation.SU3.BinaryDegree.card_projective J hF
    (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hF hc)]
  norm_num

private theorem model_five_rank [Finite X] (h : ClassicalGroup.IsPSU X 3 4) : 2 ≤ primeRank 5 X := by
  obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := h
  rw [primeRank_equiv 5 e]
  exact Theory.SpecificGroups.Classical.PairedOddRank.unitary_projective_of_dvd
    J (n := 2) (by decide) (by decide) (by decide) (by decide) hF hc

private theorem model_not_cyclic_sylow_derived [Finite X]
    (h : ClassicalGroup.IsPSU X 3 4)
    (hs : ∀ P : Sylow 2 X, IsCyclic (commutator P)) : False := by
  obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := h
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hF hc
  obtain ⟨a⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J 4 hF hf
  let J' := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  let b := e.trans a
  have hs' := sylow_derived_cyclic_of_surjective b.toMonoidHom b.surjective hs
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 4)
    (by simpa only [←Nat.card_eq_fintype_card, Nat.reducePow] using hF)
  obtain ⟨_,_,_,_,_,_,⟨R,D,_,_,_,_,_,_,hR,hcomm,hZ,_⟩,_⟩ :=
    BenderSuzuki.External.huppert_II_10_12 J' 4 hF hf rfl
  obtain ⟨P,hRP⟩ := (IsPGroup.of_card (show Nat.card R = 2^6 by exact hR)).exists_le_sylow
  have hP : Nat.card P = 64 := by
    rw [P.card_eq_multiplicity,
      Representation.SU3.BinaryDegree.card_projective J' hF hf]
    norm_num only [Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceGcd, Nat.reduceDiv]
    rw [show 62400 = 2^6 * 975 from rfl,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.factorization_pow_self (by decide : Nat.Prime 2),
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 975)]
    rfl
  have he : R = (P : Subgroup _) := eq_of_le_of_card_ge hRP (by omega)
  have hcomm' : commutator P = center P := he ▸ hcomm
  let := hs' P
  have hcent : IsCyclic (center P) := hcomm' ▸ (inferInstance : IsCyclic (commutator P))
  obtain ⟨hw,hel,hwc⟩ := HermitianForm.SylowOmega.projective_sylow_omega
    J' (n := 2) (by decide) hF hf rfl P
  let := hcent
  let : IsCyclic ((center P).map (P : Subgroup _).subtype) :=
    isCyclic_of_surjective ((P : Subgroup _).subtype.subgroupMap (center P))
      (MonoidHom.subgroupMap_surjective (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J')).subtype (center P))
  let : IsCyclic (omegaOneAmbient (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J'))) := by
    rw [hw]
    infer_instance
  let := hel
  have hd := IsElementaryAbelian.exponent_dvd_p 2 (omegaOneAmbient (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J')))
  rw [IsCyclic.exponent_eq_card,hwc] at hd
  norm_num at hd

private theorem not_odd_section [Finite X] (h : ChapterA.Section02.IsTheoremCOddModel X)
    (B : Subgroup X) (hb : ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 4) : False := by
  exact model_not_cyclic_sylow_derived hb
    (sylow_derived_cyclic_of_surjective (QuotientGroup.mk' (pCore 2 B))
      (QuotientGroup.mk'_surjective _) (sylow_derived_cyclic_of_injective
        B.subtype B.subtype_injective (AlternatingEight.odd_model_sylow_derived_cyclic h)))

private theorem section_map [Finite X] [Finite Y] (B : Subgroup X) [Group.IsPerfect B]
    (h : ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 4) (f : X →* Y)
    [Group.IsSolvable f.ker] : ClassicalGroup.IsPSU ((B.map f) ⧸ pCore 2 (B.map f)) 3 4 := by
  let := model_simple h
  let g := f.subgroupMap B
  let : Group.IsSolvable g.ker := by
    change Group.IsSolvable (f.subgroupMap B).ker
    rw [ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := B.subtype.subgroupComap f.ker) (fun a b he => Subtype.ext (Subtype.ext
        (congrArg (fun x : f.ker => (x : X)) he)))
  exact h.of_mulEquiv
    (PerfectCoreTwoExtension.solvableKernelQuotientEquiv g (f.subgroupMap_surjective B)).symm


variable {G : Type*} [Group G] [Finite G]

private theorem not_specialLinear_section (B : Subgroup G) [Group.IsPerfect B]
    (hB : ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 4)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : Chapter1.Section02.LocalModels.IsSL G 2 p) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let f : G →* PSL(2,F) := (QuotientGroup.mk' (center SL(2,F))).comp e.toMonoidHom
  have hk : f.ker ≤ center G := by
    intro x hx
    have hz : e x ∈ center SL(2,F) := (QuotientGroup.eq_one_iff _).mp hx
    exact mem_center_iff.mpr (fun y => e.injective (by
      simpa only [map_mul] using mem_center_iff.mp hz (e y)))
  let : Group.IsSolvable (center G) := Group.isSolvable_of_comm (fun a b => Subtype.ext
    (mem_center_iff.mp a.property b).symm)
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective (inclusion_injective hk)
  exact not_odd_section (.linear_two p 1 hp ho (by decide)
    ⟨F,inferInstance,inferInstance,by simpa using hF,⟨MulEquiv.refl _⟩⟩)
    (B.map f) (section_map B hB f)

/-- An actual SU₃(4) section forces the containing component to be quasisimple. -/
private theorem containing_quasisimple (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hO : pCore 2 G = ⊥) (S : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents S) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hsection : ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 4) : IsQuasisimple K := by
  have hfit : fittingSubgroup K ≤ center K := by
    by_contra hn
    obtain ⟨p,hp,hp3,⟨e⟩⟩ := NoncentralFitting.primeSL2FittingQuotient_of_noncentral
      ChapterA.RankActions.primeSL2CoverRigidity hG hO hK hn
    let : Fact p.Prime := ⟨hp⟩
    let q := QuotientGroup.mk' (fittingSubgroup K)
    let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
    let := Exceptional.local_perfect hB
    let : Group.IsPerfect (B.subgroupOf K) := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hBK).symm.toMonoidHom) (subgroupOfEquivOfLe hBK).symm.surjective
    have hb : ClassicalGroup.IsPSU ((B.subgroupOf K) ⧸ pCore 2 (B.subgroupOf K)) 3 4 :=
      hsection.of_mulEquiv (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBK)
        (pCore_map_iso 2 (subgroupOfEquivOfLe hBK)))
    let : Group.IsPerfect ((B.subgroupOf K).map q) := Group.IsPerfect.map q
    exact not_specialLinear_section ((B.subgroupOf K).map q) (section_map _ hb q)
      hp (hp.odd_of_ne_two (by omega))
      ⟨ZMod p,inferInstance,inferInstance,Nat.card_zmod p,⟨e⟩⟩
  have hs : solvableRadical K = center K :=
    le_antisymm (solvableRadical_le_center_of_fitting_le_center hfit)
      (le_solvableRadical _ inferInstance (Group.isSolvable_of_comm (fun a b =>
        Subtype.ext (mem_center_iff.mp a.property b).symm)))
  let := hK.perfect
  let := hK.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hs).symm.isSimpleGroup⟩

private theorem section_rank (B : Subgroup G)
    (h : ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 4) : 2 ≤ primeRank 5 B := by
  rw [← primeRank_quotient_eq_of_isTwoGroup 5 (by decide) (pCore 2 B) pCore_isPGroup]
  exact model_five_rank h

omit [Finite G] in
private theorem section_thirteen (B : Subgroup G)
    (h : ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 4) : 13 ∣ Nat.card G := by
  have hc : 13 ∣ Nat.card (B ⧸ pCore 2 B) := by rw [model_card h]; decide
  exact (hc.trans (card_quotient_dvd_card _)).trans B.card_subgroup_dvd_card

omit [Finite G] in
private theorem not_binary_linear (B : Subgroup G)
    (h : ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 4)
    {d : ℕ} (hd : 3 ≤ d ∧ d ≤ 5) (hm : ClassicalGroup.IsPSL G d 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let a : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let b := (e.trans (Atlas.fieldEquivPSL d a)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < d))
  have hc := section_thirteen B h
  rw [Nat.card_congr b.toEquiv,BinaryLinear.card_SL] at hc
  obtain ⟨hl,hu⟩ := hd
  interval_cases d <;> norm_num [BinaryLinear.order,Fin.prod_univ_succ] at hc

private theorem rankTwo_eq_top [IsQuasisimple G]
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (htop : (⊤ : Subgroup G).IsCComponent)
    (h : ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 4)
    {f : ℕ} (hm : ChapterA.Section02.IsTheoremCRankTwoModel G f) : B = ⊤ := by
  have hr := section_rank B h
  have hd := section_thirteen B h
  cases hm with
  | linear hn hm =>
    by_cases hf : f = 1
    · exact (not_binary_linear B h (by omega : 3 ≤ 3 ∧ 3 ≤ 5) (by simpa [hf] using hm)).elim
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact eq_of_linear_three_containing_component S hB htop le_top
      (by decide : Odd 5) hr (by omega) hF ((topEquiv (G := G)).trans e)
  | symplectic hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
    have hq : 2 < Nat.card F := by
      rw [hF]
      exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hn)
    exact eq_of_symplectic_four_containing_component S hB htop le_top
      (by decide : Odd 5) hr hq ((topEquiv (G := G)).trans a)
  | g2 hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
    have hq : 2 < Nat.card F := by
      rw [hF]
      exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hn)
    exact eq_of_g2_containing_component_of_odd_rank S hB htop le_top
      (by decide : Odd 5) hr hq ((topEquiv (G := G)).trans e)
  | triality hn hm =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G f (by omega)).mp hm
    exact eq_of_triality_containing_component_of_odd_rank S hB htop le_top
      (by decide : Odd 5) hr (by omega) ((topEquiv (G := G)).trans e)
  | ree_f4 m hm _ he =>
    exact eq_of_ree_containing_component_of_odd_rank S hB htop le_top
      (by decide : Odd 5) hr hm ((topEquiv (G := G)).trans he.some)
  | symplectic_derived _ he =>
    rw [Nat.card_congr (he.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv,
      nat_card_alternatingGroup] at hd
    norm_num at hd
  | g2_derived _ he =>
    rw [Nat.card_congr he.some.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
    norm_num at hd
  | tits _ he =>
    exact eq_of_solvable_sylow_overgroups S hB htop le_top
      (SolvableSylowOvergroups.of_equiv ((topEquiv (G := G)).trans he.some)
        Tits.ProperSylowOvergroups.solvableSylowOvergroups)

/-- The entire simple Theorem C catalogue admits no proper normalized SU₃(4) section. -/
private theorem simple_eq_top [IsSimpleGroup G] [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (htop : (⊤ : Subgroup G).IsCComponent)
    (h : ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 4)
    (hm : ChapterA.Section02.IsTheoremCModel G) : B = ⊤ := by
  have hd := section_thirteen B h
  cases hm with
  | alternating d hbound he =>
    by_cases hd2 : 2 ≤ d
    · let : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd2
      rw [Nat.card_congr he.some.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hd
      interval_cases d <;> norm_num at hd
    · have he : d = 0 ∨ d = 1 := by omega
      rcases he with rfl | rfl <;> rw [Nat.card_congr ‹Nonempty (G ≃* _)›.some.toEquiv,Nat.card_unique] at hd <;> norm_num at hd
  | odd hm => exact (not_odd_section hm B h).elim
  | bender hm => exact AlternatingEight.eq_top_of_bender_model S B hB hn hm
  | rank_two f hm => exact rankTwo_eq_top S hB htop h hm
  | linear_binary d hd hm => exact (not_binary_linear B h (by rcases hd with rfl | rfl <;> omega) hm).elim
  | sporadic hm =>
    rcases hm with ⟨name,hne,he⟩ | he
    · obtain ⟨e⟩ := he
      cases name with
      | m11 =>
        rw [Nat.card_congr e.toEquiv] at hd
        change 13 ∣ Nat.card Sporadic.Mathieu.M11 at hd
        rw [Sporadic.Mathieu.m11_order] at hd
        norm_num at hd
      | m12 =>
        rw [Nat.card_congr e.toEquiv] at hd
        change 13 ∣ Nat.card Sporadic.Mathieu.M12 at hd
        rw [Sporadic.Mathieu.m12_order] at hd
        norm_num at hd
      | m22 =>
        rw [Nat.card_congr e.toEquiv] at hd
        change 13 ∣ Nat.card Sporadic.Mathieu.M22 at hd
        rw [Sporadic.Mathieu.m22_order] at hd
        norm_num at hd
      | m23 =>
        rw [Nat.card_congr e.toEquiv] at hd
        change 13 ∣ Nat.card Sporadic.Mathieu.M23 at hd
        rw [Sporadic.Mathieu.m23_order] at hd
        norm_num at hd
      | m24 =>
        rw [Nat.card_congr e.toEquiv] at hd
        change 13 ∣ Nat.card Sporadic.Mathieu.M24 at hd
        rw [Sporadic.Mathieu.m24_order] at hd
        norm_num at hd
      | j3 => exact (hne rfl).elim
      | j2 =>
        rw [Nat.card_congr e.toEquiv] at hd
        change 13 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier at hd
        rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
        norm_num at hd
      | hs =>
        have hh := (Nat.card_congr e.toEquiv) ▸ hd
        have hh := hh.trans Sporadic.LeechRelated.HS.card_carrier_dvd
        norm_num at hh
      | j4 =>
        rw [Nat.card_congr e.toEquiv] at hd
        change 13 ∣ Nat.card Janko4.Model at hd
        rw [Janko4.Cardinality.model_card] at hd
        norm_num at hd
      | he =>
        rw [Nat.card_congr e.toEquiv] at hd
        have hc : Nat.card Held.He ∣ Nat.card Held.LocalPairs.PermutationNormalizer :=
          card_dvd_of_injective (inclusion Held.permutationGroup.le_normalizer)
            (inclusion_injective _)
        have hh := hd.trans hc
        rw [Held.OuterInvolution.Fusion.normalizer_card] at hh
        norm_num at hh
      | ru =>
        exact eq_of_rudvalis_containing_component_of_large_odd_rank S hB htop le_top
          (by decide : 3 < 5) (section_rank B h)
          (IsQuasisimple.of_mulEquiv (topEquiv (G := G)).symm) ((topEquiv (G := G)).trans e)
    · rw [Nat.card_congr he.some.toEquiv,Janko1.card_model] at hd
      norm_num at hd

/-- The full containing quotient, including every central cover, equals
its normalized local subgroup when that subgroup has an SU₃(4) section. -/
theorem local_eq_top
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (htop : (⊤ : Subgroup G).IsCComponent)
    (h : ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 4) : B = ⊤ := by
  let : IsQuasisimple (⊤ : Subgroup G) := containing_quasisimple hG hO S hB htop le_top h
  let : IsQuasisimple G := IsQuasisimple.of_mulEquiv (topEquiv (G := G))
  let := Exceptional.local_perfect hB
  let q := QuotientGroup.mk' (center G)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm (fun a b => IsMulCommutative.is_comm.comm a b)
  let Sq := S.mapSurjective (QuotientGroup.mk'_surjective (center G))
  have hb : B.map q ∈ localCComponents Sq :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB q
  have hbn : (Sq : Subgroup (G ⧸ center G)) ≤ normalizer (B.map q : Set _) :=
    (map_mono hn).trans (le_normalizer_map q)
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  let : IsQuasisimple (G ⧸ center G) := IsQuasisimple.of_surjective q (QuotientGroup.mk'_surjective _)
  have ht : (⊤ : Subgroup (G ⧸ center G)).IsCComponent := by
    simpa only [map_top_of_surjective q (QuotientGroup.mk'_surjective _)] using cComponent_map_of_solvable_ker htop q (QuotientGroup.mk'_surjective _)
  have he := simple_eq_top Sq (B.map q) hb hbn ht (section_map B h q)
    (quasisimple_center_quotient_theoremC_model hG)
  apply eq_top_of_sup_center_eq_top B
  have hc := congrArg (Subgroup.comap q) he
  simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hc

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFiveMaximal

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]

private theorem unitary_five_residual_mem_local
    {T : Sylow 2 G} {H : Subgroup G}
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hp : Group.IsPerfect (residual H))
    (hm : ChapterF.Source.IsSU (residual H ⧸ pCore 2 (residual H)) 3 4) :
    residual H ∈ Chapter1.L G (T : Subgroup G) := by
  rcases hH with ⟨hH,hTH⟩
  change (T : Subgroup G) ≤ H at hTH
  let := hp
  let : IsSimpleGroup (residual H ⧸ pCore 2 (residual H)) :=
    UnitaryFiveMaximal.model_simple (UnitaryFiveMaximal.projective_model hm)
  have hz : center (residual H ⧸ pCore 2 (residual H)) = ⊥ :=
    (inferInstance : (center (residual H ⧸ pCore 2 (residual H))).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht))
  let : IsQuasisimple (residual H ⧸ pCore 2 (residual H)) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hRH : residual H ≤ H := map_subtype_le _
  let e := (subgroupOfEquivOfLe hRH).symm
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let : IsQuasisimple (((residual H).subgroupOf H) ⧸ pCore 2 ((residual H).subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv q
  have hn : ((residual H).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_residual H)
  have hc := isCComponent_of_isPPerfect_of_quasisimple_core_quotient hn.isSubnormal
    ((isPPerfect_embedded_pResidual 2 H).of_surjective e.toMonoidHom e.surjective)
  change ((residual H).subgroupOf (residual H ⊔ (T : Subgroup G))).IsCComponent ∧ _
  rw [residual_sup_sylow T H hTH]
  refine ⟨hc,⟨T.subtype hTH,?_⟩,hH⟩
  simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]

private theorem unitary_five_embedding_context
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {K J : Subgroup G}
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKJ : K < J) (hRK : J.pCoreIn 2 ≤ normalizer (K : Set G))
    (hpK : Group.IsPerfect K) :
    let f := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hKJ.le)
    IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) ∧
      (⊤ : Subgroup (J ⧸ pCore 2 J)).IsCComponent ∧ f.range ≠ ⊤ ∧
      ∃ S : Sylow 2 J, (S : Subgroup J) = (T : Subgroup G).subgroupOf J ∧
        (let Sb := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
         f.range ∈ ChapterA.Section03.localCComponents Sb ∧
           (Sb : Subgroup (J ⧸ pCore 2 J)) ≤ normalizer (f.range : Set _)) := by
  let X := J ⊔ (T : Subgroup G)
  let JX := J.subgroupOf X
  let eJ : JX ≃* J := subgroupOfEquivOfLe le_sup_left
  let TX := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  obtain ⟨P,hP⟩ := TX.exists_subgroupOf_eq_of_subnormal JX hJ.1.subnormal
  let S := P.mapSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hSJ : (S : Subgroup J) = (T : Subgroup G).subgroupOf J := by
    change (P : Subgroup JX).map eJ.toMonoidHom = _
    rw [hP]
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hy
      exact ⟨eJ.symm y,hy,eJ.apply_symm_apply y⟩
  have hSK : (S : Subgroup J) ≤ normalizer (K.subgroupOf J : Set J) := by
    rw [← subgroupOf_normalizer_eq hKJ.le]
    rw [hSJ]
    exact comap_mono hTK
  let q := QuotientGroup.mk' (pCore 2 J)
  let f := q.comp (inclusion hKJ.le)
  let B := f.range
  have hBmap : B = (K.subgroupOf J).map q := by
    change (q.comp (inclusion hKJ.le)).range = _
    rw [MonoidHom.range_comp,inclusion_range]
  let Sb := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  have hnorm : (Sb : Subgroup (J ⧸ pCore 2 J)) ≤ normalizer (B : Set _) := by
    rw [hBmap]
    exact (map_mono hSK).trans (le_normalizer_map q)
  have hb : B ∈ ChapterA.Section03.localCComponents Sb := by
    have hl := ChapterA.Section03.SourceEmbeddings.local_restrict hK.1 hKJ.le
    rw [←hSJ] at hl
    let : Group.IsSolvable q.ker := by
      rw [QuotientGroup.ker_mk']
      let : Group.IsNilpotent (pCore 2 J) := pCore_isNilpotent
      infer_instance
    change B ∈ ChapterA.Section03.localCComponents ((S : Subgroup J).map q)
    simpa only [hBmap] using
      Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  have hne : B ≠ ⊤ := by
    intro ht
    let D := K.subgroupOf J
    have hgen : D ⊔ pCore 2 J = ⊤ := by
      have hh := congrArg (Subgroup.comap q) ht
      rw [hBmap,comap_map_eq,QuotientGroup.ker_mk',comap_top] at hh
      exact hh
    have hnD : D.Normal := (normalizer_eq_top_iff).mp (by
      have hh : D ⊔ pCore 2 J ≤ normalizer (D : Set J) := by
        refine sup_le D.le_normalizer ?_
        rw [←subgroupOf_normalizer_eq hKJ.le]
        intro x hx
        exact hRK (mem_map_of_mem J.subtype hx)
      rw [hgen] at hh
      exact top_unique hh)
    let := hnD
    let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hKJ.le).symm.toMonoidHom)
      (subgroupOfEquivOfLe hKJ.le).symm.surjective
    let : Group.IsPerfect J := Chapter1.mem_L_isPerfect hJ
    have hDtop : D = ⊤ :=
      (residuals_of_perfect_normal_sup_twoGroup D (pCore 2 J) pCore_isPGroup hgen).2.symm.trans
        solvableResidual_eq_top
    exact hKJ.ne (le_antisymm hKJ.le (subgroupOf_eq_top.mp hDtop))
  let qX := QuotientGroup.mk' (pCore 2 X)
  have hsq := Chapter1.Section02.uniqueness_local_quotient_sqtk hG hJ.2.2
  let eqJ : JX.map qX ≃* (J ⧸ pCore 2 J) :=
    (cComponentTwoCoreQuotientEquiv hJ.1).symm.trans
      (QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ))
  have hsqJ : IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) :=
    (IsSQTK.equiv eqJ).mp (hsq.subgroup _)
  have htop : (⊤ : Subgroup (J ⧸ pCore 2 J)).IsCComponent := by
    let := pCore_isNilpotent (p := 2) (G := X)
    have hh : (⊤ : Subgroup (JX.map qX)).IsCComponent := by
      simpa only [subgroupOf_self] using (hJ.1.map_quotient (pCore 2 X)).subgroupOf le_rfl
    simpa only [map_top_of_surjective eqJ.toMonoidHom eqJ.surjective] using hh.map_equiv eqJ
  exact ⟨hsqJ,htop,hne,S,hSJ,hb,hnorm⟩

/-- The actual U₅(4) comparison makes the original right residual maximal
in the local-component family. The SU₃(4) non-enlargement argument is proved
on the literal image in each containing component's two-core quotient. -/
theorem Preparation.unitaryFive_right_maximal
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (M : Model 4)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) M.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) M.amalgam.reverse)) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) := by
  have hTH := hH.1.1.2
  rcases he with he | he
  · exact (d.not_unitaryFive_unreversed h hTH hp M he).elim
  obtain ⟨e⟩ := he
  have hs : sourceS L H ≤ residual H := by
    let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
    have hSP : sourceS L H ≤ P := le_sup_right.trans le_sup_left
    have hb := IsPGroup.le_normal_of_index_primeTo M.leftLocal
      (((sourceS L H).subgroupOf P).map e.right.toMonoidHom)
      (((pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H)).comap_subtype).map e.right.toMonoidHom)
      (by rw [M.leftLocal_index_eq_three]; decide)
    have heq : M.leftLocal = solvableResidual M.leftParabolic := rfl
    rw [heq, ← map_solvableResidual_eq e.right.toMonoidHom e.right.surjective,
      map_le_map_iff_of_injective e.right.injective] at hb
    have hm := map_mono (f := P.subtype) hb
    rw [map_subgroupOf_eq_of_le hSP] at hm
    exact hm.trans_eq (d.parabolic_residuals h hTH hp 1)
  have hcore := residual_core_eq_of_sourceS_le h.sylow_normalizes hTH hs
  have hu := (d.unitaryFive_local_structure h hTH hp M e).2.2.2.1
  have hK := unitary_five_residual_mem_local hH.1.1 hp hu
  let := hp
  refine ⟨hK,?_⟩
  intro J hJ hKJ
  by_contra hne
  have hlt : residual H < J := lt_of_le_of_ne hKJ (Ne.symm hne)
  have hHJ : H ≤ J ⊔ (T : Subgroup G) := by
    rw [←residual_sup_sylow T H hTH]
    exact sup_le_sup hKJ le_rfl
  have hR : J.pCoreIn 2 ≤ (residual H).pCoreIn 2 :=
    (pCoreAmbient_mono_of_isSubnormalIn J (J ⊔ (T : Subgroup G)) 2
      le_sup_left hJ.1.subnormal).trans
        ((Chapter3.twoCore_le_of_sylow_le T hTH hHJ).trans_eq hcore)
  have hRN : J.pCoreIn 2 ≤ normalizer (residual H : Set G) :=
    hR.trans ((map_subtype_le _).trans (residual H).le_normalizer)
  obtain ⟨hsq,htop,hproper,S,hS,hb,hbn⟩ :=
    unitary_five_embedding_context h.qtke hK hJ (hTH.trans (le_normalizer_residual H)) hlt hRN hp
  let q := QuotientGroup.mk' (pCore 2 J)
  let f := q.comp (inclusion hKJ)
  let a := subgroupOfEquivOfLe hKJ
  have hm : ClassicalGroup.IsPSU (((residual H).subgroupOf J) ⧸
      pCore 2 ((residual H).subgroupOf J)) 3 4 :=
    (UnitaryFiveMaximal.projective_model hu).of_mulEquiv
      (QuotientGroup.congr _ _ a (pCore_map_iso 2 a))
  let : Group.IsPerfect ((residual H).subgroupOf J) :=
    Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let := pCore_isNilpotent (p := 2) (G := J)
    infer_instance
  have hmap : f.range = ((residual H).subgroupOf J).map q := by
    rw [MonoidHom.range_comp,inclusion_range]
  have hm' : ClassicalGroup.IsPSU (f.range ⧸ pCore 2 f.range) 3 4 := by
    rw [hmap]
    exact UnitaryFiveMaximal.section_map _ hm q
  exact hproper (UnitaryFiveMaximal.local_eq_top hsq (pCore_quotient_pCore_eq_bot 2)
    (S.mapSurjective (QuotientGroup.mk'_surjective _)) f.range hb hbn htop hm')

/-- Both compatible U₅(4) orientations satisfy the literal 5.3 normalizer
conditions; maximality, common Sylow and enlarged two-cores are discharged. -/
theorem Preparation.unitaryFive_normalizer_local_conditions
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (M : Model 4)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) M.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) M.amalgam.reverse)) :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) := by
  have hc : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) := .unitaryFive M he
  exact d.normalizer_local_conditions h hH (d.unitaryFive_right_maximal h hH hp M he) rfl
    (d.common_sylow_of_comparison h hH.1.1.2 hp hc)
    (d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp hc)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
