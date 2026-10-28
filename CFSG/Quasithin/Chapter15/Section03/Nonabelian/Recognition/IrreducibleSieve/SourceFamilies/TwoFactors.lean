module
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.SpecificGroups.SL2.SmallOddComparisons
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.AutomorphismSquare
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases
public import Theory.Representation.Suzuki.BinaryDegree
public import Theory.Representation.NonsplitFour
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# The two-component irreducible branch of 15.3.58

Minimal normality forces a proper component to be nonnormal in the actual
actor. The completed A/C source reduction gives its four concrete models.
The common-field tensor degree and original actor rank force full natural
SL₂ order on each factor: Suzuki is excluded by its binary degree bound,
J₁ by matrix-image order, and odd-prime PSL₂ reduces to PSL₂(5). The binary
SL₂ Schur-field alternatives leave exactly its natural constituent.

The resulting action on the actual component join is the split orthogonal
four-dimensional action over the common field. Its marked-involution sieve
contradicts the rank-two displacement from 15.3.58. No universal G.9.3 or
small-module classification premise is used.

Source: Aschbacher–Smith, combined manuscript, G.9.3, printed p.356,
and 15.3.58, printed p.1149.
-/

public noncomputable section
open scoped MatrixGroups MonoidAlgebra
open Subgroup Representation
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.TwoFactors
open CFSG.Quasithin.ChapterG.Section09
open TwoComponents TwoComponents.NaturalRecognition
open TwoComponents.FactorReduction.ModelRestrictions
universe u w
variable {H : Type u} [Group H] [Finite H] {W : Type w}
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K L L₂ : Subgroup H} {P : Sylow 2 H}
  {v : H} {s : ℕ}

private theorem factor_degree_bound (h : SourceData ρ X P v s)
    (T : TensorData ρ L L₂) (hL : Theory.GroupTheory.IsComponent H L)
    (hm : s + 1 ≤ 2 * primeRank 2 L) :
    Module.finrank (ZMod 2) T.I ≤ 2 * (primeRank 2 L + 1) := by
  have hk := T.two_le_factor_dimension hL
  have hd : T.n * T.k ^ 2 ≤ 2 * (2 * primeRank 2 L + 1) := by
    rw [← T.degree_eq, h.dimension]
    omega
  have hn : T.n ≤ primeRank 2 L := by
    have hsq : 4 ≤ T.k ^ 2 := by nlinarith
    have := Nat.mul_le_mul_left T.n hsq
    omega
  rw [T.factor_degree_eq]
  exact TensorBounds.factor_degree_le hn hd

private theorem low_rank_parameters (h : SourceData ρ X P v s)
    (T : TensorData ρ L L₂) (hL : Theory.GroupTheory.IsComponent H L)
    (hm : s + 1 ≤ 2 * primeRank 2 L) (hr : primeRank 2 L ≤ 3) :
    T.k = 2 ∧ 2 ≤ T.n ∧ T.n ≤ 3 := by
  have hk := T.two_le_factor_dimension hL
  have hn := T.n_pos
  have hd := T.degree_eq
  rw [h.dimension] at hd
  have hs := h.positive
  have hk4 : T.k < 4 := by
    by_contra! hbig
    have hsquare : 16 ≤ T.k ^ 2 := by nlinarith
    have := Nat.mul_le_mul_left T.n hsquare
    have : 16 ≤ T.n * T.k ^ 2 := by nlinarith
    omega
  have hk2 : T.k = 2 := by
    rcases (by omega : T.k = 2 ∨ T.k = 3) with htwo | hthree
    · exact htwo
    · rw [hthree] at hd
      norm_num at hd
      omega
  rw [hk2] at hd
  norm_num at hd
  exact ⟨hk2, by omega, by omega⟩

private theorem binary_orders (h : SourceData ρ X P v s)
    (T : TensorData ρ L L₂) (hL : Theory.GroupTheory.IsComponent H L)
    (hm : s + 1 ≤ 2 * primeRank 2 L)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {r : ℕ} (hr : 2 ≤ r) (e : L ≃* SL(2,F)) (hF : Nat.card F = 2 ^ r)
    (hrank : primeRank 2 L = r) :
    T.k = 2 ∧ Nat.card L = Nat.card SL(2,GaloisField 2 T.n) := by
  let τ : Representation (ZMod 2) L T.I := Representation.restrictScalars T.left
  let σ : Representation (ZMod 2) SL(2,F) T.I := τ.comp e.symm.toMonoidHom
  let : σ.IsIrreducible := (Representation.irreducible_comp_surjective_iff
    e.symm.toMonoidHom e.symm.surjective τ).mpr T.left_irreducible
  have hf : Function.Injective σ := by
    intro a b hab
    apply e.symm.injective
    apply T.left_faithful
    ext x
    exact congrArg (fun f : Module.End (ZMod 2) T.I => f x) hab
  have hschur := T.left_schur_degree_comp e.symm
  change Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,F)] σ.asModule) = T.n at hschur
  have hsmall := factor_degree_bound h T hL hm
  rw [hrank] at hsmall
  have hdeg := T.factor_degree_eq
  have hn := T.n_pos
  rcases DefiningCharacteristic.binary_small_faithful_classification σ hf r hr hF hsmall with
    hnat | horth | htriple
  · rw [hschur] at hnat
    have hk : T.k = 2 := by nlinarith [hnat.1, hnat.2.1]
    refine ⟨hk, ?_⟩
    rw [Nat.card_congr e.toEquiv, BenderSuzuki.External.huppert614_card_specialLinearGroup,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,
      GaloisField.card 2 T.n hn.ne', hF, hnat.1]
  · rw [hschur] at horth
    have hk : T.k = 4 := by nlinarith [horth.1, horth.2.1]
    exact (T.exclude_orthogonal_factor hm (hrank.trans horth.1.symm) hk
      (by rw [h.dimension])).elim
  · rw [hschur] at htriple
    have hk : T.k = 8 := by nlinarith [htriple.1, htriple.2.2.1]
    have hd := T.degree_eq
    rw [hk, htriple.1, h.dimension] at hd
    have hr3 : primeRank 2 L = 3 := hrank.trans htriple.2.1
    omega

private theorem not_suzuki (h : SourceData ρ X P v s)
    (T : TensorData ρ L L₂) (hL : Theory.GroupTheory.IsComponent H L)
    (hm : s + 1 ≤ 2 * primeRank 2 L)
    {j : ℕ} (hj : 0 < j) (e : L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup j) : False := by
  let τ : Representation (ZMod 2) L T.I := Representation.restrictScalars T.left
  let σ := τ.comp e.symm.toMonoidHom
  have hf : Function.Injective σ := by
    intro a b hab
    apply e.symm.injective
    apply T.left_faithful
    ext x
    exact congrArg (fun f : Module.End (ZMod 2) T.I => f x) hab
  have hlo := Representation.Suzuki.finrank_ge (by omega : 1 ≤ j) σ hf
  have hhi := factor_degree_bound h T hL hm
  have hr := (Theory.GroupTheory.primeRank_equiv 2 e).trans
    (BenderSuzuki.MatrixGroups.suzuki_two_rank j hj)
  omega

omit [FiniteDimensional (ZMod 2) W] in
private theorem card_dvd_GL (T : TensorData ρ L L₂) (hk : T.k = 2) :
    Nat.card L ∣ ((2 ^ T.n) ^ 2 - 1) * ((2 ^ T.n) ^ 2 - 2 ^ T.n) := by
  let : Finite T.F := Module.finite_iff_finite.mp T.finiteField
  let : Fintype T.F := Fintype.ofFinite _
  have hd := Representation.card_dvd_card_GL_of_injective T.left T.left_faithful
  change Module.finrank T.F T.I = 2 at hk
  rw [hk, Matrix.card_GL_field] at hd
  simpa [Fin.prod_univ_two, ← Nat.card_eq_fintype_card, T.field_card] using hd

private theorem not_janko (h : SourceData ρ X P v s)
    (T : TensorData ρ L L₂) (hL : Theory.GroupTheory.IsComponent H L)
    (hm : s + 1 ≤ 2 * primeRank 2 L) (e : L ≃* Janko1.Model) : False := by
  have ho : Nat.card L = 175560 := (Nat.card_congr e.toEquiv).trans Janko1.card_model
  have hr : primeRank 2 L ≤ 3 := by
    obtain ⟨E, _, hE⟩ := exists_elementaryAbelian_card_primeRank (G := L) (p := 2)
    have hd := E.card_subgroup_dvd_card
    rw [hE, ho] at hd
    by_contra! hb
    have hh : 2 ^ 4 ∣ 175560 := (pow_dvd_pow 2 hb).trans hd
    norm_num at hh
  obtain ⟨hk, hn, hn'⟩ := low_rank_parameters h T hL hm hr
  have hc := card_dvd_GL T hk
  rw [ho] at hc
  rcases (by omega : T.n = 2 ∨ T.n = 3) with he | he <;> rw [he] at hc <;> norm_num at hc

private theorem odd_prime_orders (h : SourceData ρ X P v s)
    (T : TensorData ρ L L₂) (hL : Theory.GroupTheory.IsComponent H L)
    (hm : s + 1 ≤ 2 * primeRank 2 L)
    (hodd : ∀ p : ℕ, p.Prime → Odd p → primeRank p L ≤ 1)
    {p a : ℕ} [Fact p.Prime] (hp : 3 < p) (ha : 1 ≤ a)
    (e : L ≃* PSL(2,GaloisField p a)) :
    T.k = 2 ∧ Nat.card L = Nat.card SL(2,GaloisField 2 T.n) := by
  have ha1 := odd_exponent_eq_one hp ha e
    (hodd p Fact.out ((Fact.out : p.Prime).odd_of_ne_two (by omega)))
  subst a
  let eF : GaloisField p 1 ≃+* ZMod p := (GaloisField.equivZmodP p).toRingEquiv
  let ep := e.trans (GorensteinWalter.psl2RingEquiv eF)
  have hr : primeRank 2 L = 2 := (Theory.GroupTheory.primeRank_equiv 2 ep).trans
    (Theory.PSL2.primeField_two_rank hp)
  obtain ⟨hk, hn, hn'⟩ := low_rank_parameters h T hL hm (by omega)
  have hdim := T.degree_eq
  rw [h.dimension, hk] at hdim
  have hn2 : T.n = 2 := by norm_num at hdim; omega
  have hgl := card_dvd_GL T hk
  rw [hn2] at hgl
  norm_num at hgl
  have hc : Nat.card L * 2 = p * (p ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv]
    simpa only [GaloisField.card p 1 (by decide), pow_one] using
      Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
        (F := GaloisField p 1) (by
          simpa only [GaloisField.card p 1 (by decide), pow_one] using
            (Fact.out : p.Prime).odd_of_ne_two (by omega))
  have hpd : p ∣ Nat.card L := by
    have hd : p ∣ Nat.card L * 2 := by rw [hc]; exact dvd_mul_right _ _
    rcases (Fact.out : p.Prime).dvd_mul.mp hd with hd | hd
    · exact hd
    · have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hd
      omega
  have hfac : p ∣ 2 ^ 2 * 3 ^ 2 * 5 := by
    norm_num
    exact hpd.trans hgl
  have hp5 : p = 5 := by
    rcases (Fact.out : p.Prime).dvd_mul.mp hfac with hh | hh
    · rcases (Fact.out : p.Prime).dvd_mul.mp hh with htwo | hthree
      · have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
          ((Fact.out : p.Prime).dvd_of_dvd_pow htwo)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp
          ((Fact.out : p.Prime).dvd_of_dvd_pow hthree)
        omega
    · exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by decide)).mp hh
  rw [hp5] at hc
  norm_num at hc
  refine ⟨hk, ?_⟩
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,
    GaloisField.card 2 T.n T.n_pos.ne', hn2]
  omega

/-- The source degree equality and the actual four-model factor catalogue force
full two-dimensional special-linear order over the tensor's own Schur field. -/
private theorem tensor_orders (h : SourceData ρ X P v s)
    (T : TensorData ρ L L₂) (hL : Theory.GroupTheory.IsComponent H L)
    (hm : s + 1 ≤ 2 * primeRank 2 L)
    (hmodels : QuotientModel L)
    (hodd : ∀ p : ℕ, p.Prime → Odd p → primeRank p L ≤ 1) :
    T.k = 2 ∧ Nat.card L = Nat.card SL(2,GaloisField 2 T.n) := by
  rcases hmodels with ⟨n, hn, ⟨e⟩⟩ | ⟨j, hj, ⟨e⟩⟩ | hjanko | ⟨p, hp, a, hpa, ha, _, ⟨e⟩⟩
  · let : NeZero n := ⟨by omega⟩
    have hc := GaloisField.card 2 n (by omega)
    have hl := Matrix.SpecialLinearGroup.fieldExponent_le_primeRank_of_injective
      hc e.symm.toMonoidHom e.symm.injective
    have hu : primeRank 2 (MulAut L) ≤ n := by
      rw [Theory.GroupTheory.primeRank_equiv 2 (MulAut.congr e)]
      exact Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn hc
    have hi : primeRank 2 L ≤ primeRank 2 (MulAut L) := by
      rw [Theory.GroupTheory.primeRank_equiv 2 e,
        Theory.GroupTheory.primeRank_equiv 2 (MulAut.congr e)]
      exact Theory.GroupTheory.primeRank_le_of_injective 2 MulAut.conj
        (MulAut.conj_injective_of_center_eq_bot (Theory.PSL2.sl2_center_eq_bot _))
    exact binary_orders h T hL hm hn e hc (by omega)
  · exact (not_suzuki h T hL hm hj e).elim
  · obtain ⟨e⟩ := hjanko
    exact (not_janko h T hL hm e).elim
  · let := hp
    exact odd_prime_orders h T hL hm hodd hpa ha e

/-- In the two-component source branch the exact factor catalogue suffices;
no G.9.3 or auxiliary small-module classification is assumed. -/
private theorem false_of_tensor_models
    (h : SourceData ρ X P v s) (hK : ComponentData ρ K)
    (hc : ComponentHypothesis KnownSimple.IsKnownSimple ρ X L K (s + 1))
    (h₂ : Theory.GroupTheory.IsComponent H L₂) (hjoin : K = L ⊔ L₂)
    (hne : L ≠ L₂) (e : L ≃* L₂) (T : TensorData ρ L L₂)
    (hz : center L = ⊥) (hmodels : QuotientModel L)
    (hodd : ∀ p : ℕ, p.Prime → Odd p → primeRank p L ≤ 1) : False := by
  have hb : BinaryAutomorphismRankTheorem := fun F _ _ _ n hn hF =>
    Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn hF
  obtain ⟨hr, ha, _⟩ := model_ranks hb hmodels hodd
  have hm := actor_rank_bound_of_factor_automorphism_rank hc h₂ hjoin hne e hz hr ha
  obtain ⟨hk,ho⟩ := tensor_orders h T hc.component hm hmodels hodd
  let : Theory.GroupTheory.IsQuasisimple L := hc.component.2
  let : Theory.GroupTheory.IsQuasisimple L₂ := h₂.2
  have hd := component_pair_disjoint_of_center_eq_bot hc.component h₂ hne hz
  have hnat := quasiequivalent_trans
    (tensor_natural_of_order T (hc.component.commutator_eq_bot_of_ne h₂ hne) hd hjoin
      T.fieldEquiv hk ho ((Nat.card_congr e.toEquiv).symm.trans ho))
    (naturalTensor_fourOrthogonal T.n)
  obtain ⟨hdegree,hmlo⟩ := T.dimension_two_bounds hk hc.degree_le
  exact TensorCases.not_plusCase h hK
    ⟨T.n, two_dimensional_field_degree T hc.component hk ho, hnat, hdegree, hmlo⟩

omit [Finite H] in
private theorem quotientModel_of_four (hL : Theory.GroupTheory.IsComponent H L)
    (hm : CFSG.Quasithin.Chapter1.Section02.NonnormalCComponentModel L) : QuotientModel L := by
  let : Theory.GroupTheory.IsQuasisimple L := hL.2
  cases hm with
  | linear_even n hn iso =>
    let : NeZero n := ⟨by omega⟩
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
    let : Fintype F := Fintype.ofFinite _
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    let eF : F ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
        GaloisField.card 2 n (by omega)])
    exact .inl ⟨n,hn,⟨(e.trans (GorensteinWalter.psl2RingEquiv eF)).trans
      (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 n)).symm⟩⟩
  | suzuki j hj iso => exact .inr (.inl ⟨j,by omega,iso⟩)
  | janko iso => exact .inr (.inr (.inl iso))
  | linear_prime p hp hodd iso =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
    let : Fact p.Prime := ⟨hp⟩
    have hp3 : 3 < p := by
      have hp2 := hp.two_le
      have hne2 : p ≠ 2 := by intro he; rw [he] at hodd; norm_num at hodd
      by_contra! hh
      have he : p = 3 := by omega
      have hperfect : Group.IsPerfect PSL(2,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three (hF.trans he) hperfect
    let : Fintype F := Fintype.ofFinite _
    let : Fintype (GaloisField p 1) := Fintype.ofFinite _
    let eF : F ≃+* GaloisField p 1 := FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
        GaloisField.card p 1 (by decide), pow_one])
    exact .inr (.inr (.inr ⟨p,inferInstance,1,hp3,by omega,by omega,
      ⟨e.trans (GorensteinWalter.psl2RingEquiv eF)⟩⟩))

/-- The complete two-factor irreducible contradiction for the original
15.3.58 action data. The proper component is forced to be nonnormal by
minimality; original A/C give its four models, and the actual tensor action
is excluded by the marked-involution geometry. -/
theorem false_of_proper_component
    (h : SourceData ρ X P v s) (hK : ComponentData ρ K)
    (hc : ComponentHypothesis KnownSimple.IsKnownSimple ρ X L K (s + 1))
    (hLK : L < K) (hG : IsSQTK KnownSimple.IsKnownSimple H)
    (hcore : pCore 2 H = ⊥) : False := by
  obtain ⟨L₂,h₂,hjoin,hne,hcomm,⟨e⟩,hq⟩ := exists_component_pair hc hLK
  have hnebot : L ≠ ⊥ := by
    let : Theory.GroupTheory.IsQuasisimple L := hc.component.2
    let : IsSimpleGroup (L ⧸ center L) := Theory.GroupTheory.IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    exact (nontrivial_iff_ne_bot L).mp inferInstance
  have hnon : ¬ L.Normal := by
    intro hn
    rcases hK.minimal L hn hLK.le with hb | he
    · exact hnebot hb
    · exact hLK.ne he
  have hmodel := CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource.nonnormal_component_model
    (fun D _ _ => CFSG.Quasithin.ChapterA.Section02.theoremA_knownSimple (G := D))
    (fun D _ _ => CFSG.Quasithin.ChapterA.Section02.theoremC_knownSimple (G := D))
    hG hcore L hc.component hnon
  have hi : Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype) := hjoin ▸ hK.irreducible
  obtain ⟨T⟩ := TwoComponents.CommonField.tensorConstruction ρ L L₂ h.faithful hc.component h₂ hne hi hq
  have hA : SemisimpleSectionRankTheorem KnownSimple.IsKnownSimple :=
    semisimpleSectionRank_of_theoremA
      (fun D _ _ => CFSG.Quasithin.ChapterA.Section02.theoremA_knownSimple (G := D))
  have hz := component_center_eq_bot hA hc h₂ hne e T
  have hodd : ∀ p : ℕ, p.Prime → Odd p → primeRank p L ≤ 1 := fun p hp ho =>
    odd_rank_le_one hc.component h₂ hjoin hne e hz
      (hG.subgroup K).stronglyQuasithin hp ho
  exact false_of_tensor_models h hK hc h₂ hjoin hne e T hz
    (quotientModel_of_four hc.component hmodel) hodd
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.TwoFactors
