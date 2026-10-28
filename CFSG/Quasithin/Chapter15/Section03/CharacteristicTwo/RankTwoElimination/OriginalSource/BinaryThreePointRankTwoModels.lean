module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankOne
public import Theory.SpecificGroups.PSL3Two.SolvableSylowOvergroups
public import Theory.SpecificGroups.G2.BinarySolvableSylowOvergroups
public import Theory.SpecificGroups.Tits.SolvableSylowOvergroups
public import Theory.SpecificGroups.Triality.OddSupplement
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure
public import Theory.SpecificGroups.Triality.FullParabolicActions.CyclicQuotient
public import Theory.SpecificGroups.SL2.BinaryThreeSection
public import Theory.SpecificGroups.ReeF4.OddSupplement
public import Theory.SpecificGroups.ReeF4.BinaryThreeSection
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups

/-!
# Rank-two carriers cannot enlarge the original binary-three local component

Restrict the original full Sylow to the containing C-component, and map
its actual smaller subgroup to the supplied carrier. For binary PSL₃,
Sp₄ and G₂, the proper parabolic residual has SL₂ two-core quotient,
whose order is never 168. The genuine triality and Ree parabolics give
the same binary SL₂ obstruction or a three-free Suzuki quotient.
Solvable proper Sylow overgroups settle the small derived and Tits rows.

Every equality retains the original pair B ≤ K and the actual quotient
B/O₂(B). No quasisimplicity of B or embedding catalogue is assumed.
The parabolic calculations adapt the generic proofs already used in
Chapter12 Section05 Local/Components/PointEvenRankTwo.
Source: Aschbacher--Smith A.3.12 and15.3.23, pp.47--48,1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

private theorem sl2_card_ne {F : Type*} [Field F] [Finite F] :
    Nat.card SL(2,F) ≠ 168 := by
  intro he
  rw [GorensteinWalter.sl2_card_formula] at he
  have hq : Nat.card F ≤ 5 := by
    by_contra! hq
    have hq6 : 6 ≤ Nat.card F := by omega
    have hh : 35 ≤ Nat.card F ^ 2 - 1 := by
      have hsq := Nat.pow_le_pow_left hq6 2
      omega
    have hh' := Nat.mul_le_mul hq6 hh
    omega
  interval_cases h : Nat.card F <;> simp at he

private theorem core_card_ne_of_equiv {A F : Type*} [Group A] [Field F] [Finite F]
    (e : (A ⧸ pCore 2 A) ≃* SL(2,F)) : Nat.card (A ⧸ pCore 2 A) ≠ 168 := by
  rw [Nat.card_congr e.toEquiv]
  exact sl2_card_ne

private theorem linear_local_eq_top {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 PSL(3,F)) (B : Subgroup PSL(3,F))
    (hB : B ∈ localCComponents S) (hc : Nat.card (B ⧸ pCore 2 B) = 168) : B = ⊤ := by
  by_contra hp
  obtain ⟨g,hg⟩ := FiveLocalFF.linear_three_local_placement hF hn S B hB hp
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hc' : Nat.card ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) = 168 :=
    (Nat.card_congr aq.toEquiv).symm.trans hc
  rcases hg with hg | hg
  · rw [hg] at hc'
    exact core_card_ne_of_equiv (Matrix.PSL3.LinearThree.pointLocalCoreQuotientEquiv F) hc'
  · rw [hg] at hc'
    exact core_card_ne_of_equiv (Matrix.PSL3.LinearThree.lineLocalCoreQuotientEquiv F) hc'

private theorem symplectic_local_eq_top {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (B : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hB : B ∈ localCComponents S) (hc : Nat.card (B ⧸ pCore 2 B) = 168) : B = ⊤ := by
  by_contra hp
  obtain ⟨g,hg⟩ := FiveLocalFF.symplectic_local_placement hF hn S B hB hp
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hc' : Nat.card ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) = 168 :=
    (Nat.card_congr aq.toEquiv).symm.trans hc
  rcases hg with hg | hg
  · rw [hg] at hc'
    exact core_card_ne_of_equiv
      (Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF hn) hc'
  · rw [hg] at hc'
    exact core_card_ne_of_equiv
      (Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF hn) hc'

private theorem g2_local_eq_top {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (S : Sylow 2 (Atlas.G2.Model F)) (B : Subgroup (Atlas.G2.Model F))
    (hB : B ∈ localCComponents S) (hc : Nat.card (B ⧸ pCore 2 B) = 168) : B = ⊤ := by
  by_contra hp
  obtain ⟨g,hg⟩ := FiveLocalFF.G2.local_placement hq S B hB hp
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hc' : Nat.card ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) = 168 :=
    (Nat.card_congr aq.toEquiv).symm.trans hc
  rcases hg with hg | hg
  · rw [hg] at hc'
    exact core_card_ne_of_equiv
      (local₁CoreQuotientEquivPSL.trans longSLEquivPSL.symm) hc'
  · rw [hg] at hc'
    exact core_card_ne_of_equiv
      (local₂CoreQuotientEquivPSL.trans longSLEquivPSL.symm) hc'

private theorem local_perfect {X : Type*} [Group X] (S : Subgroup X)
    {B : Subgroup X} (hB : B ∈ localCComponents S) : Group.IsPerfect B := by
  let := hB.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective

private theorem local_join_ne_top {X : Type*} [Group X]
    (S : Subgroup X) {B : Subgroup X} (hB : B ∈ localCComponents S)
    (hp : B ≠ ⊤) (hcomp : ∀ J : Subgroup X, J.IsCComponent → J = ⊤) : B ⊔ S ≠ ⊤ := by
  intro ht
  have hc : B.IsCComponent := by
    change (B.subgroupOf (B ⊔ S)).IsCComponent at hB
    rw [ht] at hB
    simpa only [map_subgroupOf_eq_of_le le_top] using hB.map_subtype (.top)
  exact hp (hcomp B hc)

private theorem triality_perfect_le_local (P : Triality.Standard.Parameters)
    (hp : P.prime = 2) (a : Triality.Standard.Parabolics.Node)
    (B : Subgroup (Triality.Standard.Carrier P)) [Group.IsPerfect B]
    (hB : B ≤ Triality.Standard.Parabolics.parabolic P a) :
    B ≤ Triality.Standard.Parabolics.localFactor P a := by
  let X := B.subgroupOf (Triality.Standard.Parabolics.parabolic P a)
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hB).symm.toMonoidHom) (subgroupOfEquivOfLe hB).symm.surjective
  let N := (Triality.Standard.Parabolics.localFactor P a).subgroupOf
    (Triality.Standard.Parabolics.parabolic P a)
  let : IsCyclic (Triality.Standard.Parabolics.parabolic P a ⧸ N) :=
    Triality.Standard.Parabolics.parabolic_quotient_isCyclic P hp a
  let : CommGroup (Triality.Standard.Parabolics.parabolic P a ⧸ N) := IsCyclic.commGroup
  have hh := le_of_isPerfect_of_solvable_quotient X N
  intro x hx
  exact hh (show (⟨x,hB hx⟩ : Triality.Standard.Parabolics.parabolic P a) ∈ X from hx)

private theorem triality_local_eq_top (n : ℕ) (hn : 0 < n)
    (S : Sylow 2 (Triality.Standard.BinaryCarrier n hn))
    (B : Subgroup (Triality.Standard.BinaryCarrier n hn))
    (hB : B ∈ localCComponents S)
    (hcomp : ∀ J : Subgroup (Triality.Standard.BinaryCarrier n hn), J.IsCComponent → J = ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* SL(3,ZMod 2)) : B = ⊤ := by
  by_contra hp
  let P := Triality.Standard.binaryParameters n hn
  let : Group.IsPerfect B := local_perfect (X := Triality.Standard.BinaryCarrier n hn) (S : Subgroup (Triality.Standard.BinaryCarrier n hn)) hB
  obtain ⟨_,a,_,hS⟩ := Theory.GroupTheory.SolvableSylowControl.exists_aligned_equiv
    (MulEquiv.refl (Triality.Standard.BinaryCarrier n hn)) S
    (Triality.Standard.Parabolics.unipotentSylow P rfl)
  change (S : Subgroup (Triality.Standard.BinaryCarrier n hn)).map a.toMonoidHom = Triality.Standard.Parabolics.unipotent P at hS
  let H := B ⊔ (S : Subgroup (Triality.Standard.BinaryCarrier n hn))
  have hH : H.map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply local_join_ne_top (S : Subgroup (Triality.Standard.BinaryCarrier n hn)) hB hp hcomp
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  obtain ⟨j,hj⟩ := Triality.Standard.OddSupplement.le_parabolic n hn
    (H.map a.toMonoidHom) (hS ▸ map_mono le_sup_right) hH
  let A := B.map a.toMonoidHom
  let : Group.IsPerfect A := Group.IsPerfect.map a.toMonoidHom
  have hAL := triality_perfect_le_local P rfl j A ((map_mono le_sup_left).trans hj)
  let f : B →* Triality.Standard.Parabolics.localFactor P j :=
    (a.toMonoidHom.comp B.subtype).codRestrict _
      (fun b => hAL (mem_map_of_mem a.toMonoidHom b.property))
  have hf : Function.Injective f := fun b c he => Subtype.ext
    (a.injective (congrArg Subtype.val he))
  have hk : IsPGroup 2 f.ker := by
    rw [f.ker_eq_bot_iff.mpr hf]
    exact IsPGroup.of_card (n := 0) (by simp)
  let π := eB.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
  have hπ : Function.Surjective π := eB.surjective.comp (QuotientGroup.mk'_surjective _)
  cases j with
  | arms =>
    exact Matrix.SpecialLinearGroup.no_binary_three_quotient_of_binary_core_quotient π hπ f hk
      ((Triality.Standard.Parabolics.localFactorArmsQuotientEquivPSL2 P rfl).trans
        (Theory.PSL2.sl2QuotientEquiv (Triality.Standard.ExtensionField P)).symm)
  | central =>
    exact Matrix.SpecialLinearGroup.no_binary_three_quotient_of_binary_core_quotient π hπ f hk
      ((Triality.Standard.Parabolics.localFactorCentralQuotientEquivPSL2 P rfl).trans
        (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 n)).symm)

private theorem ree_local_eq_top (m : ℕ) (hm : 1 ≤ m)
    (S : Sylow 2 (ReeF4.Model m)) (B : Subgroup (ReeF4.Model m))
    (hB : B ∈ localCComponents S)
    (hcomp : ∀ J : Subgroup (ReeF4.Model m), J.IsCComponent → J = ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* SL(3,ZMod 2)) : B = ⊤ := by
  by_contra hp
  let : Group.IsPerfect B := local_perfect (X := ReeF4.Model m) (S : Subgroup (ReeF4.Model m)) hB
  obtain ⟨_,a,_,hS⟩ := Theory.GroupTheory.SolvableSylowControl.exists_aligned_equiv
    (MulEquiv.refl (ReeF4.Model m)) S (ReeF4.Parabolics.ThreeSylowContainment.positiveSylow m)
  rw [ReeF4.Parabolics.ThreeSylowContainment.positiveSylow_coe] at hS
  let H := B ⊔ (S : Subgroup (ReeF4.Model m))
  have hH : H.map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply local_join_ne_top (S : Subgroup (ReeF4.Model m)) hB hp hcomp
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  obtain ⟨j,hj⟩ := ReeF4.OddSupplement.le_parabolic m hm
    (H.map a.toMonoidHom) (hS ▸ map_mono le_sup_right) hH
  have hBP : B.map a.toMonoidHom ≤ ReeF4.ConverseParabolics.parabolic m j :=
    (map_mono le_sup_left).trans hj
  let f : B →* ReeF4.ConverseParabolics.parabolic m j :=
    (a.toMonoidHom.comp B.subtype).codRestrict _
      (fun b => hBP (mem_map_of_mem a.toMonoidHom b.property))
  have hf : Function.Injective f := fun b c he => Subtype.ext
    (a.injective (congrArg Subtype.val he))
  exact ReeF4.ConverseParabolics.no_binary_three_quotient_in_parabolic
    (eB.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B)))
    (eB.surjective.comp (QuotientGroup.mk'_surjective _)) hm j f hf

variable {G : Type*} [Group G] [Finite G]

private theorem eq_of_binary_three_local_models
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    {X : Type*} [Group X] [Finite X] (eX : K ≃* X)
    (hX : ∀ (S : Sylow 2 X) (A : Subgroup X), A ∈ localCComponents S →
      (∀ J : Subgroup X, J.IsCComponent → J = ⊤) →
      ((A ⧸ pCore 2 A) ≃* SL(3,ZMod 2)) → A = ⊤) : B = K := by
  obtain ⟨S,_,hl⟩ := exists_local_sylow_restriction T hB hBK hK.subnormal
  let A := B.subgroupOf K
  let b := subgroupOfEquivOfLe hBK
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let c := eX.subgroupMap A
  let cq := QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  let eSL := eB.trans Matrix.PSL3Two.equiv.symm
  let : Group.IsSolvable eX.toMonoidHom.ker := by
    rw [eX.toMonoidHom.ker_eq_bot_iff.mpr eX.injective]
    infer_instance
  have hcomp : ∀ J : Subgroup X, J.IsCComponent → J = ⊤ := by
    intro J hJ
    have ht := hK.eq_top_of_isCComponent (hJ.map_equiv eX.symm)
    apply map_injective (f := eX.symm.toMonoidHom) eX.symm.injective
    rw [ht,map_top_of_surjective _ eX.symm.surjective]
  have ht := hX (S.mapSurjective (f := eX.toMonoidHom) eX.surjective)
    (A.map eX.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl eX.toMonoidHom)
    hcomp (cq.symm.trans (bq.trans eSL))
  have hAtop : A = ⊤ := by
    apply map_injective (f := eX.toMonoidHom) eX.injective
    rw [ht,map_top_of_surjective _ eX.surjective]
  exact le_antisymm hBK (subgroupOf_eq_top.mp hAtop)

/-- Every binary PSL₃ carrier, including the field of two elements, forces
equality of the actual local component and containing component. -/
theorem binary_three_eq_of_even_linear_three
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSL K 3 (2 ^ n)) : B = K := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  by_cases hn1 : n = 1
  · apply eq_of_solvable_sylow_overgroups T hB hK hBK
    exact SolvableSylowOvergroups.of_equiv e
      (Matrix.PSL3Two.solvableSylowOvergroups_projective_of_card_two (by simpa [hn1] using hF))
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact eq_of_binary_three_local_models T hB hK hBK eB e (fun S A hA _ ea =>
    linear_local_eq_top hF (by omega) S A hA
      ((Nat.card_congr ea.toEquiv).trans Matrix.PSL3Two.card_SL))

/-- The original binary-three section excludes proper local containment
in every nonbinary symplectic-four carrier. -/
theorem binary_three_eq_of_even_symplectic
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSp K 2 (2 ^ n)) : B = K := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
  exact eq_of_binary_three_local_models T hB hK hBK eB a (fun S A hA _ ea =>
    symplectic_local_eq_top hF (by omega) S A hA
      ((Nat.card_congr ea.toEquiv).trans Matrix.PSL3Two.card_SL))

/-- Both actual G₂ parabolic residuals are incompatible with the original
PSL₃(2) two-core quotient. -/
theorem binary_three_eq_of_even_g2
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassificationModels.IsG2At K (2 ^ n)) : B = K := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hn)
  exact eq_of_binary_three_local_models T hB hK hBK eB e (fun S A hA _ ea =>
    g2_local_eq_top hq S A hA
      ((Nat.card_congr ea.toEquiv).trans Matrix.PSL3Two.card_SL))

/-- The genuine triality carriers, including the binary endpoint, have
no proper local component with the original binary-three quotient. -/
theorem binary_three_eq_of_even_triality
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    {n : ℕ} (hn : 1 ≤ n) (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) K) : B = K := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff K n (by omega)).mp hm
  exact eq_of_binary_three_local_models T hB hK hBK eB e (triality_local_eq_top n (by omega))

/-- The original full Ree family is retained through its actual local-block
carrier equivalence; both parabolics exclude the binary-three section. -/
theorem binary_three_eq_of_ree
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    {m : ℕ} (hm : 1 ≤ m) (he : Chapter1.Section02.LocalModels.IsReeF4At K m) : B = K := by
  obtain ⟨e⟩ := (ReeF4.exists_localBlockInput_mulEquiv_iff K m).mp he
  exact eq_of_binary_three_local_models T hB hK hBK eB e (ree_local_eq_top m hm)

/-- The derived binary symplectic carrier is the actual alternating-six
group, whose proper full-Sylow overgroups are solvable. -/
theorem binary_three_eq_of_binary_symplectic_derived
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (e : K ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) : B = K :=
  eq_of_solvable_sylow_overgroups T hB hK hBK
    (SolvableSylowOvergroups.of_equiv
      (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
      AlternatingSix.ProperSylowOvergroups.isSolvable)

/-- Proper full-Sylow overgroups in G₂(2)′ are solvable. -/
theorem binary_three_eq_of_binary_g2_derived
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (e : K ≃* commutator (Atlas.G2.Model (ZMod 2))) : B = K :=
  eq_of_solvable_sylow_overgroups T hB hK hBK
    (SolvableSylowOvergroups.of_equiv e Atlas.G2.BinaryDerived.solvableSylowOvergroups)

/-- Proper full-Sylow overgroups in the literal Tits carrier are solvable. -/
theorem binary_three_eq_of_tits
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (e : K ≃* Tits.ParrottGroup) : B = K :=
  eq_of_solvable_sylow_overgroups T hB hK hBK
    (SolvableSylowOvergroups.of_equiv e Tits.ProperSylowOvergroups.solvableSylowOvergroups)

/-- Every original characteristic-two rank-two carrier forces equality
with the supplied local PSL₃(2) component. -/
theorem binary_three_eq_of_rank_two_model
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (hm : Chapter1.Section02.LocalModels.RankTwoTheoremC K) : B = K := by
  cases hm with
  | linear n hn hm => exact binary_three_eq_of_even_linear_three T hB hK hBK eB hn hm
  | symplectic n hn hm => exact binary_three_eq_of_even_symplectic T hB hK hBK eB hn hm
  | g2 n hn hm => exact binary_three_eq_of_even_g2 T hB hK hBK eB hn hm
  | triality n hn hm => exact binary_three_eq_of_even_triality T hB hK hBK eB hn hm
  | ree m hm he => exact binary_three_eq_of_ree T hB hK hBK eB hm he
  | symplectic_derived he => exact binary_three_eq_of_binary_symplectic_derived T hB hK hBK he.some
  | g2_derived he => exact binary_three_eq_of_binary_g2_derived T hB hK hBK he.some
  | tits he => exact binary_three_eq_of_tits T hB hK hBK he.some

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
