module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveMaximal
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SixLocalFF.RankTwo
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.Coordinates
public import Theory.SpecificGroups.Triality.ThreeFreeSylowOvergroups
public import Theory.GroupTheory.SylowInvariantThreeFree.Overgroups
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.PrimeActors

/-!
# Selecting the containing carrier of the Ree Suzuki residual

A proper local component with Suzuki two-core quotient, normalized by the
full Sylow of its containing component, forces that component's central
quotient to be a positive-parameter Ree group. The Suzuki Sylow derived
subgroup contains the additive field, excluding all odd-characteristic
and noncentral-Fitting rows. Solvable-kernel maps preserve the simple
Suzuki section, so this argument also passes through the containing center.

In the simple Theorem C catalogue, proper classical local quotients are
SL₂ and cannot be Suzuki; the genuine triality carrier forces a cubic
divisor. Bender and Tits carriers have solvable proper Sylow overgroups.
The Suzuki root order bounds its parameter in every remaining numerical
case. The Rudvalis case uses the actual proper Sylow-overgroup section
orders, since the ambient order alone does not exclude Sz(8).

The companion ReeOvercomponent module applies this selection to the
literal image of O²(H) in J/O₂(J), discharging the last containing-carrier
premise of Ree right maximality. This is the specialized A.3.12(3) route
used in Aschbacher–Smith 5.2.8, printed pp.47–48 and652
(`refs/quasithin.pdf`), rather than an assumed general embedding list.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.ReeContaining
open BenderSuzuki.MatrixGroups
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

private theorem not_cyclic_sylow_derived {m : ℕ} (hm : 0 < m)
    (hs : ∀ S : Sylow 2 (SuzukiMatrixGroup m), IsCyclic (commutator S)) : False := by
  obtain ⟨P,hP⟩ := suzukiRootSubgroup_isSylow m hm
  have hcy : IsCyclic (commutator (SuzukiRootSubgroup m)) := hP ▸ hs P
  let := hcy
  let F := SchurCover.Family.Field m
  let f : Multiplicative F →* commutator (SuzukiRootSubgroup m) :=
    { toFun := fun b => ⟨SchurCover.Family.rootPoint m 0 b.toAdd, by
        rw [←SchurCover.Family.rootCoordinate_ker m hm]
        rfl⟩
      map_one' := Subtype.ext (SchurCover.Family.rootPoint_zero m)
      map_mul' := fun b c => Subtype.ext (by
        simpa using (SchurCover.Family.rootPoint_mul m hm 0 b.toAdd 0 c.toAdd).symm) }
  have hf : Function.Injective f := by
    intro b c he
    have hh := congrArg (fun x : commutator (SuzukiRootSubgroup m) => x.val.val.val 0 2) he
    exact hh
  let : IsCyclic (Multiplicative F) := isCyclic_of_injective f hf
  have he : Monoid.exponent (Multiplicative F) ∣ 2 := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro b
    change Multiplicative.ofAdd (2 • b.toAdd) = 1
    simp [two_smul,CharTwo.add_self_eq_zero]
  rw [IsCyclic.exponent_eq_card] at he
  have hc : Nat.card (Multiplicative F) = 2^(2*m+1) := GaloisField.card 2 (2*m+1) (by omega)
  rw [hc] at he
  have hlo : 4 ≤ 2^(2*m+1) := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega : 2 ≤ 2*m+1)
  have hh := Nat.le_of_dvd (by decide : 0 < (2:ℕ)) he
  omega

variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]

private theorem section_map (B : Subgroup X) [Group.IsPerfect B]
    {m : ℕ} (hm : 0 < m) (a : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m)
    (f : X →* Y) [Group.IsSolvable f.ker] :
    Nonempty (((B.map f) ⧸ pCore 2 (B.map f)) ≃* SuzukiMatrixGroup m) := by
  let : IsSimpleGroup (B ⧸ pCore 2 B) := a.isSimpleGroup_congr.mpr
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
  let g := f.subgroupMap B
  let : Group.IsSolvable g.ker := by
    change Group.IsSolvable (f.subgroupMap B).ker
    rw [ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := B.subtype.subgroupComap f.ker) (fun a b he => Subtype.ext (Subtype.ext
        (congrArg (fun x : f.ker => (x : X)) he)))
  exact ⟨(PerfectCoreTwoExtension.solvableKernelQuotientEquiv g
    (f.subgroupMap_surjective B)).symm.trans a⟩

private theorem not_odd_section
    (h : ChapterA.Section02.IsTheoremCOddModel X) (B : Subgroup X)
    {m : ℕ} (hm : 0 < m) (a : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m) : False := by
  exact not_cyclic_sylow_derived hm
    (sylow_derived_cyclic_of_surjective a.toMonoidHom a.surjective
      (sylow_derived_cyclic_of_surjective (QuotientGroup.mk' (pCore 2 B))
        (QuotientGroup.mk'_surjective _) (sylow_derived_cyclic_of_injective
          B.subtype B.subtype_injective (AlternatingEight.odd_model_sylow_derived_cyclic h))))

private theorem not_specialLinear_section (B : Subgroup X) [Group.IsPerfect B]
    {m : ℕ} (hm : 0 < m) (a : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : Chapter1.Section02.LocalModels.IsSL X 2 p) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
  let f : X →* PSL(2,F) := (QuotientGroup.mk' (center SL(2,F))).comp e.toMonoidHom
  have hk : f.ker ≤ center X := by
    intro x hx
    have hz : e x ∈ center SL(2,F) := (QuotientGroup.eq_one_iff _).mp hx
    exact mem_center_iff.mpr (fun y => e.injective (by
      simpa only [map_mul] using mem_center_iff.mp hz (e y)))
  let : Group.IsSolvable (center X) := Group.isSolvable_of_comm (fun a b => Subtype.ext
    (mem_center_iff.mp a.property b).symm)
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective (inclusion_injective hk)
  exact not_odd_section (.linear_two p 1 hp ho (by decide)
    ⟨F,inferInstance,inferInstance,by simpa using hF,⟨MulEquiv.refl _⟩⟩)
    (B.map f) hm (section_map B hm a f).some

/-- A containing component of a Suzuki local section is quasisimple. -/
theorem containing_quasisimple (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (hO : pCore 2 X = ⊥) (S : Sylow 2 X) {B K : Subgroup X}
    (hB : B ∈ localCComponents S) (hK : K.IsCComponent) (hBK : B ≤ K)
    {m : ℕ} (hm : 0 < m) (a : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m) :
    IsQuasisimple K := by
  have hfit : fittingSubgroup K ≤ center K := by
    by_contra hn
    obtain ⟨p,hp,hp3,⟨e⟩⟩ := NoncentralFitting.primeSL2FittingQuotient_of_noncentral
      ChapterA.RankActions.primeSL2CoverRigidity hX hO hK hn
    let : Fact p.Prime := ⟨hp⟩
    let q := QuotientGroup.mk' (fittingSubgroup K)
    let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
    let := Exceptional.local_perfect hB
    let : Group.IsPerfect (B.subgroupOf K) := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hBK).symm.toMonoidHom) (subgroupOfEquivOfLe hBK).symm.surjective
    let b := (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBK)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hBK))).trans a
    let : Group.IsPerfect ((B.subgroupOf K).map q) := Group.IsPerfect.map q
    exact not_specialLinear_section ((B.subgroupOf K).map q) hm (section_map _ hm b q).some
      hp (hp.odd_of_ne_two (by omega))
      ⟨ZMod p,inferInstance,inferInstance,Nat.card_zmod p,⟨e⟩⟩
  have hs : solvableRadical K = center K :=
    le_antisymm (solvableRadical_le_center_of_fitting_le_center hfit)
      (le_solvableRadical _ inferInstance (Group.isSolvable_of_comm (fun a b =>
        Subtype.ext (mem_center_iff.mp a.property b).symm)))
  let := hK.perfect
  let := hK.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hs).symm.isSimpleGroup⟩

private theorem not_order {m c : ℕ} (hm : 0 < m)
    (h2 : ¬ 2^22 ∣ c) (h13 : ¬ 13 ∣ c) (h41 : ¬ 41 ∣ c)
    (h127 : ¬ 127 ∣ c) (h73 : ¬ 73 ∣ c) : ¬ Nat.card (SuzukiMatrixGroup m) ∣ c := by
  intro hd
  have hpow : 2^(4*m+2) ∣ c := by
    have hh := (SuzukiRootSubgroup m).card_subgroup_dvd_card.trans hd
    rw [suzukiRootSubgroup_card m hm,←pow_mul] at hh
    simpa only [show (2*m+1)*2 = 4*m+2 by omega] using hh
  have hb : m < 5 := by
    by_contra hn
    exact h2 ((pow_dvd_pow 2 (by omega : 22 ≤ 4*m+2)).trans hpow)
  rw [suzukiMatrixGroup_card m hm] at hd
  interval_cases m
  · exact h13 ((by norm_num : 13 ∣ ((2^(2*1+1))^2+1)*(2^(2*1+1))^2*(2^(2*1+1)-1)).trans hd)
  · exact h41 ((by norm_num : 41 ∣ ((2^(2*2+1))^2+1)*(2^(2*2+1))^2*(2^(2*2+1)-1)).trans hd)
  · exact h127 ((by norm_num : 127 ∣ ((2^(2*3+1))^2+1)*(2^(2*3+1))^2*(2^(2*3+1)-1)).trans hd)
  · exact h73 ((by norm_num : 73 ∣ ((2^(2*4+1))^2+1)*(2^(2*4+1))^2*(2^(2*4+1)-1)).trans hd)

omit [Finite X] in
private theorem section_card (B : Subgroup X) {m : ℕ}
    (a : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m) :
    Nat.card (SuzukiMatrixGroup m) ∣ Nat.card X := by
  rw [←Nat.card_congr a.toEquiv]
  exact (card_quotient_dvd_card _).trans B.card_subgroup_dvd_card

omit [Finite X] in
private theorem not_binary_linear (B : Subgroup X) {m d : ℕ}
    (hm : 0 < m) (a : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m)
    (hd : 3 ≤ d ∧ d ≤ 5) (he : ClassicalGroup.IsPSL X d 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
  let := Fintype.ofFinite F
  let b : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let c := (e.trans (Atlas.fieldEquivPSL d b)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < d))
  have hh := section_card B a
  rw [Nat.card_congr c.toEquiv,BinaryLinear.card_SL] at hh
  obtain ⟨hl,hu⟩ := hd
  interval_cases d <;> apply not_order hm (c := BinaryLinear.order _) (by decide)
    (by decide) (by decide) (by decide) (by decide) hh

omit [Finite Y] in
private theorem transport_false (e : X ≃* Y) (S : Sylow 2 X) (B : Subgroup X)
    (hB : B ∈ localCComponents S) (hn : (S : Subgroup X) ≤ normalizer (B : Set X))
    (ht : (⊤ : Subgroup X).IsCComponent) (hp : B ≠ ⊤)
    {m : ℕ} (_hm : 0 < m) (a : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m)
    (hf : ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ localCComponents S →
      (S : Subgroup Y) ≤ normalizer (B : Set Y) →
      (⊤ : Subgroup Y).IsCComponent → B ≠ ⊤ →
      (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m → False) : False := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  have ht' : (⊤ : Subgroup Y).IsCComponent := by
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using ht.map_equiv e
  have hp' : B.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hp
    apply map_injective (f := e.toMonoidHom) e.injective
    rwa [map_top_of_surjective e.toMonoidHom e.surjective]
  let b := e.subgroupMap B
  exact hf (S.mapSurjective e.surjective) (B.map e.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB e.toMonoidHom)
    ((map_mono hn).trans (le_normalizer_map e.toMonoidHom)) ht' hp'
    ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans a)

private theorem not_sl2_section {F Z : Type*} [Field F] [Finite F] [CharP F 2] [Group Z]
    {m : ℕ} (hm : 0 < m) (a : (Z ⧸ pCore 2 Z) ≃* SuzukiMatrixGroup m)
    (b : (Z ⧸ pCore 2 Z) ≃* SL(2,F)) : False := by
  apply not_nonempty_psl2_char_two_equiv_suzuki F hm
  exact ⟨(Theory.PSL2.sl2QuotientEquiv F).symm.trans (b.symm.trans a)⟩

private theorem not_linear_three {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (S : Sylow 2 PSL(3,F)) (B : Subgroup PSL(3,F))
    (hB : B ∈ localCComponents S) (hp : B ≠ ⊤)
    {m : ℕ} (hm : 0 < m) (a : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m) : False := by
  obtain ⟨g,hg⟩ := FiveLocalFF.linear_three_local_placement hF hn S B hB hp
  let b := (MulAut.conj g).subgroupMap B
  let bq := QuotientGroup.congr (pCore 2 B) _ b (pCore_map_iso 2 b)
  rcases hg with hg | hg <;> apply not_sl2_section (F := F) hm a <;> refine bq.trans ?_
  · change ((B.map (MulAut.conj g).toMonoidHom) ⧸ pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hg]
    exact Matrix.PSL3.LinearThree.pointLocalCoreQuotientEquiv F
  · change ((B.map (MulAut.conj g).toMonoidHom) ⧸ pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hg]
    exact Matrix.PSL3.LinearThree.lineLocalCoreQuotientEquiv F

private theorem not_symplectic {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (B : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hB : B ∈ localCComponents S) (hp : B ≠ ⊤)
    {m : ℕ} (hm : 0 < m) (a : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m) : False := by
  obtain ⟨g,hg⟩ := FiveLocalFF.symplectic_local_placement hF hn S B hB hp
  let b := (MulAut.conj g).subgroupMap B
  let bq := QuotientGroup.congr (pCore 2 B) _ b (pCore_map_iso 2 b)
  rcases hg with hg | hg <;> apply not_sl2_section (F := F) hm a <;> refine bq.trans ?_
  · change ((B.map (MulAut.conj g).toMonoidHom) ⧸ pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hg]
    exact Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF hn
  · change ((B.map (MulAut.conj g).toMonoidHom) ⧸ pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hg]
    exact Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF hn

private theorem not_g2 {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (S : Sylow 2 (Atlas.G2.Model F)) (B : Subgroup (Atlas.G2.Model F))
    (hB : B ∈ localCComponents S) (hp : B ≠ ⊤)
    {m : ℕ} (hm : 0 < m) (a : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m) : False := by
  obtain ⟨g,hg⟩ := FiveLocalFF.G2.local_placement hq S B hB hp
  let b := (MulAut.conj g).subgroupMap B
  let bq := QuotientGroup.congr (pCore 2 B) _ b (pCore_map_iso 2 b)
  rcases hg with hg | hg <;> apply not_sl2_section (F := F) hm a <;> refine bq.trans ?_
  · change ((B.map (MulAut.conj g).toMonoidHom) ⧸ pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hg]
    exact (QuotientGroup.quotientMulEquivOfEq Atlas.G2.LieParabolicSetup.local₁_intrinsic_pCore).trans
      Atlas.G2.LieParabolicSetup.local₁RadicalQuotientEquivSL
  · change ((B.map (MulAut.conj g).toMonoidHom) ⧸ pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hg]
    exact (QuotientGroup.quotientMulEquivOfEq Atlas.G2.LieParabolicSetup.local₂_pCore).trans
      Atlas.G2.LieParabolicSetup.local₂RadicalQuotientEquivSL

private theorem not_three_free_overgroups
    (S : Sylow 2 X) (B : Subgroup X) (hB : B ∈ localCComponents S)
    (hnorm : (S : Subgroup X) ≤ normalizer (B : Set X))
    {m : ℕ} (hm : 0 < m) (a : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m)
    (hmodel : ∀ D : Subgroup X, (S : Subgroup X) ≤ D →
      ¬ 3 ∣ Nat.card D → Group.IsSolvable D) : False := by
  have hthree := three_free_of_suzuki_core_quotient m hm a
  have hSthree : ¬ 3 ∣ Nat.card S := by
    obtain ⟨k,hk⟩ := S.isPGroup'.exists_card_eq
    rw [hk]
    exact fun hd => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hjoin : ¬ 3 ∣ Nat.card (B ⊔ (S : Subgroup _) : Subgroup _) := by
    intro hd
    have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes B (S : Subgroup _) hnorm
    have hh : 3 ∣ Nat.card B * Nat.card S := by
      rw [hprod]
      exact dvd_mul_of_dvd_right hd _
    exact (Nat.prime_three.dvd_mul.mp hh).elim hthree hSthree
  let := hmodel (B ⊔ (S : Subgroup X)) le_sup_right hjoin
  exact hB.not_isSolvable inferInstance

private theorem not_rudvalis [IsQuasisimple Rudvalis.Model]
    (S : Sylow 2 Rudvalis.Model) (B : Subgroup Rudvalis.Model)
    (hB : B ∈ localCComponents S) (ht : (⊤ : Subgroup Rudvalis.Model).IsCComponent)
    (hp : B ≠ ⊤) {m : ℕ} (hm : 0 < m)
    (a : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m) : False := by
  have ho : pCore 2 Rudvalis.Model = ⊥ := bot_unique
    ((IsQuasisimple.pCore_le_center 2).trans_eq Rudvalis.LowCentralizers.model_center_eq_bot)
  have hcover := Rudvalis.SylowOvergroups.oddIndexMaximalCover_of_twoCore_of_radicalCover ho
    Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.rudvalis_oddIndexMaximalTwoCore
    Rudvalis.SylowOvergroups.oddIndexMaximalRadicalCover
  have hd := Rudvalis.SylowOvergroups.proper_overgroup_section_order hcover S
    (B ⊔ (S : Subgroup Rudvalis.Model)) B le_sup_right
    (local_sup_ne_top_of_ne_top ht S B hB hp) le_sup_left
  rw [Nat.card_congr a.toEquiv] at hd
  exact not_order hm (by decide) (by decide) (by decide) (by decide) (by decide) hd

private theorem rankTwo_ree [IsQuasisimple X]
    (S : Sylow 2 X) (B : Subgroup X) (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup X) ≤ normalizer (B : Set X))
    (ht : (⊤ : Subgroup X).IsCComponent) (hp : B ≠ ⊤)
    {m : ℕ} (hm : 0 < m) (a : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m)
    {f : ℕ} (hc : ChapterA.Section02.IsTheoremCRankTwoModel X f) :
    ∃ k, 0 < k ∧ Nonempty (X ≃* ReeF4.Model k) := by
  have hd := section_card B a
  cases hc with
  | linear hf hc =>
    by_cases hf1 : f = 1
    · exact (not_binary_linear B hm a (by omega : 3 ≤ 3 ∧ 3 ≤ 5)
        (by simpa [hf1] using hc)).elim
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hc
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact (transport_false e S B hB hn ht hp hm a
      (fun S B hb _ _ hp b => not_linear_three hF (by omega) S B hb hp hm b)).elim
  | symplectic hf hc =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hc
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let e' := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
    exact (transport_false e' S B hB hn ht hp hm a
      (fun S B hb _ _ hp b => not_symplectic hF (by omega) S B hb hp hm b)).elim
  | g2 hf hc =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hc
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
    have hq : 2 < Nat.card F := by
      rw [hF]
      exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hf)
    exact (transport_false e S B hB hn ht hp hm a
      (fun S B hb _ _ hp b => not_g2 hq S B hb hp hm b)).elim
  | triality hf hc =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff X f (by omega)).mp hc
    exact (transport_false e S B hB hn ht hp hm a
      (fun S B hb hn _ _ b => not_three_free_overgroups S B hb hn hm b
        (Triality.Standard.ThreeFreeSylowOvergroups.isSolvable_of_three_free f (by omega) S))).elim
  | ree_f4 k hk _ he => exact ⟨k,by omega,he⟩
  | symplectic_derived _ he =>
    rw [Nat.card_congr (he.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv,
      nat_card_alternatingGroup,Nat.card_fin] at hd
    exact (not_order hm (by decide) (by decide) (by decide) (by decide) (by decide) hd).elim
  | g2_derived _ he =>
    rw [Nat.card_congr he.some.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
    exact (not_order hm (by decide) (by decide) (by decide) (by decide) (by decide) hd).elim
  | tits _ he =>
    exact (hp (eq_of_solvable_sylow_overgroups S hB ht le_top
      (SolvableSylowOvergroups.of_equiv ((topEquiv (G := X)).trans he.some)
        Tits.ProperSylowOvergroups.solvableSylowOvergroups))).elim

private theorem simple_ree [IsSimpleGroup X] [IsQuasisimple X]
    (S : Sylow 2 X) (B : Subgroup X) (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup X) ≤ normalizer (B : Set X))
    (ht : (⊤ : Subgroup X).IsCComponent) (hp : B ≠ ⊤)
    {m : ℕ} (hm : 0 < m) (a : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m)
    (hc : ChapterA.Section02.IsTheoremCModel X) :
    ∃ k, 0 < k ∧ Nonempty (X ≃* ReeF4.Model k) := by
  have hd := section_card B a
  cases hc with
  | alternating d hbound he =>
    by_cases hd2 : 2 ≤ d
    · let : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd2
      rw [Nat.card_congr he.some.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hd
      interval_cases d <;> exact (not_order hm (by decide) (by decide)
        (by decide) (by decide) (by decide) hd).elim
    · have hz : d = 0 ∨ d = 1 := by omega
      rcases hz with rfl | rfl <;> rw [Nat.card_congr he.some.toEquiv, Nat.card_unique (α := alternatingGroup (Fin _))] at hd <;>
        exact (not_order hm (by decide) (by decide) (by decide) (by decide) (by decide) hd).elim
  | odd hc => exact (not_odd_section hc B hm a).elim
  | bender hc => exact (hp (AlternatingEight.eq_top_of_bender_model S B hB hn hc)).elim
  | rank_two f hc => exact rankTwo_ree S B hB hn ht hp hm a hc
  | linear_binary d hb hc =>
    exact (not_binary_linear B hm a (by rcases hb with rfl | rfl <;> omega) hc).elim
  | sporadic hc =>
    rcases hc with ⟨name,hne,⟨e⟩⟩ | he
    · cases name with
      | m11 =>
        rw [Nat.card_congr e.toEquiv] at hd
        change Nat.card (SuzukiMatrixGroup m) ∣ Nat.card Sporadic.Mathieu.M11 at hd
        rw [Sporadic.Mathieu.m11_order] at hd
        exact (not_order hm (by decide) (by decide) (by decide) (by decide) (by decide) hd).elim
      | m12 =>
        rw [Nat.card_congr e.toEquiv] at hd
        change Nat.card (SuzukiMatrixGroup m) ∣ Nat.card Sporadic.Mathieu.M12 at hd
        rw [Sporadic.Mathieu.m12_order] at hd
        exact (not_order hm (by decide) (by decide) (by decide) (by decide) (by decide) hd).elim
      | m22 =>
        rw [Nat.card_congr e.toEquiv] at hd
        change Nat.card (SuzukiMatrixGroup m) ∣ Nat.card Sporadic.Mathieu.M22 at hd
        rw [Sporadic.Mathieu.m22_order] at hd
        exact (not_order hm (by decide) (by decide) (by decide) (by decide) (by decide) hd).elim
      | m23 =>
        rw [Nat.card_congr e.toEquiv] at hd
        change Nat.card (SuzukiMatrixGroup m) ∣ Nat.card Sporadic.Mathieu.M23 at hd
        rw [Sporadic.Mathieu.m23_order] at hd
        exact (not_order hm (by decide) (by decide) (by decide) (by decide) (by decide) hd).elim
      | m24 =>
        rw [Nat.card_congr e.toEquiv] at hd
        change Nat.card (SuzukiMatrixGroup m) ∣ Nat.card Sporadic.Mathieu.M24 at hd
        rw [Sporadic.Mathieu.m24_order] at hd
        exact (not_order hm (by decide) (by decide) (by decide) (by decide) (by decide) hd).elim
      | j3 => exact (hne rfl).elim
      | j2 =>
        rw [Nat.card_congr e.toEquiv] at hd
        change Nat.card (SuzukiMatrixGroup m) ∣ Nat.card Sporadic.LeechRelated.J2.Carrier at hd
        rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
        exact (not_order hm (by decide) (by decide) (by decide) (by decide) (by decide) hd).elim
      | hs =>
        have hh := (Nat.card_congr e.toEquiv) ▸ hd
        have hh := hh.trans Sporadic.LeechRelated.HS.card_carrier_dvd
        exact (not_order hm (by decide) (by decide) (by decide) (by decide) (by decide) hh).elim
      | j4 =>
        rw [Nat.card_congr e.toEquiv] at hd
        change Nat.card (SuzukiMatrixGroup m) ∣ Nat.card Janko4.Model at hd
        rw [Janko4.Cardinality.model_card] at hd
        exact (not_order hm (by decide) (by decide) (by decide) (by decide) (by decide) hd).elim
      | he =>
        rw [Nat.card_congr e.toEquiv] at hd
        have hh : Nat.card Held.He ∣ Nat.card Held.LocalPairs.PermutationNormalizer :=
          card_dvd_of_injective (inclusion Held.permutationGroup.le_normalizer) (inclusion_injective _)
        have hh := hd.trans hh
        rw [Held.OuterInvolution.Fusion.normalizer_card] at hh
        exact (not_order hm (by decide) (by decide) (by decide) (by decide) (by decide) hh).elim
      | ru =>
        let : IsQuasisimple Rudvalis.Model := IsQuasisimple.of_mulEquiv e
        exact (transport_false e S B hB hn ht hp hm a
          (fun S B hb _ ht hp b => not_rudvalis S B hb ht hp hm b)).elim
    · rw [Nat.card_congr he.some.toEquiv,Janko1.card_model] at hd
      exact (not_order hm (by decide) (by decide) (by decide) (by decide) (by decide) hd).elim

/-- A proper full-Sylow-normalized Suzuki local section forces the actual
central quotient of the containing component to be a positive-parameter Ree group. -/
theorem central_quotient_ree
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (hO : pCore 2 X = ⊥)
    (S : Sylow 2 X) (B : Subgroup X) (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup X) ≤ normalizer (B : Set X))
    (ht : (⊤ : Subgroup X).IsCComponent) (hp : B ≠ ⊤)
    {m : ℕ} (hm : 0 < m) (a : (B ⧸ pCore 2 B) ≃* SuzukiMatrixGroup m) :
    ∃ k, 0 < k ∧ Nonempty ((X ⧸ center X) ≃* ReeF4.Model k) := by
  let : IsQuasisimple (⊤ : Subgroup X) := containing_quasisimple hX hO S hB ht le_top hm a
  let : IsQuasisimple X := IsQuasisimple.of_mulEquiv (topEquiv (G := X))
  let := Exceptional.local_perfect hB
  let q := QuotientGroup.mk' (center X)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm (fun a b => IsMulCommutative.is_comm.comm a b)
  let Sq := S.mapSurjective (QuotientGroup.mk'_surjective (center X))
  have hb : B.map q ∈ localCComponents Sq := Chapter1.Section02.localCComponents_map_of_solvable_ker hB q
  have hbn : (Sq : Subgroup (X ⧸ center X)) ≤ normalizer (B.map q : Set _) :=
    (map_mono hn).trans (le_normalizer_map q)
  let : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
  let : IsQuasisimple (X ⧸ center X) := IsQuasisimple.of_surjective q (QuotientGroup.mk'_surjective _)
  have htq : (⊤ : Subgroup (X ⧸ center X)).IsCComponent := by
    simpa only [map_top_of_surjective q (QuotientGroup.mk'_surjective _)] using
      cComponent_map_of_solvable_ker ht q (QuotientGroup.mk'_surjective _)
  have hpq : B.map q ≠ ⊤ := by
    intro he
    apply hp
    apply eq_top_of_sup_center_eq_top B
    have hh := congrArg (Subgroup.comap q) he
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh
  exact simple_ree Sq (B.map q) hb hbn htq hpq hm (section_map B hm a q).some
    (quasisimple_center_quotient_theoremC_model hX)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.ReeContaining
