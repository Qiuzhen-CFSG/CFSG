module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCentralizerCoverSieve
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Triality
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.TwoLocalOrders
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import Theory.SpecificGroups.Tits.TwoLocalFifteenFree

/-!
# Excluding rank-two containers of the original Mathieu residual

The literal full-Sylow placement in PSL₃, Sp₄, G₂ and triality identifies
proper local residuals with parabolic residuals. Their two-core quotients
are SL₂ groups, whose orders cannot equal 1080. The binary derived endpoints
are too small. The genuine Ree and Tits models have fifteen-free normalizers
of nontrivial two-subgroups, while the original residual normalizes its own
nontrivial core and has order divisible by fifteen. Thus no rank-two row
can contain the residual in source 8.2.13. General Ree fixed-group carriers
are transported by their actual model equivalence.

Source: Aschbacher–Smith A.3.12 and 8.2.13, printed pp.47–48 and 722–723.
The literal chosen-module application belongs to qt-d-1222-nonff-mathieu
and is in NonFFSourceMathieuM24ComponentIdentification.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
open ChapterA.Section03.SourceEmbeddings Chapter1.Section02.LocalModels
variable {F : Type*} [Field F] [Finite F]

private theorem not_sl2_core_card {A : Type*} [Group A]
    (hc : Nat.card (A ⧸ pCore 2 A) = 1080)
    (e : (A ⧸ pCore 2 A) ≃* SL(2,F)) : False := by
  have hh : Nat.card F * (Nat.card F ^ 2 - 1) = 1080 := by
    rw [←GorensteinWalter.sl2_card_formula,←Nat.card_congr e.toEquiv,hc]
  have hq : Nat.card F ≤ 10 := by
    by_contra! h
    have h2 : 121 ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left h 2
    have hm := Nat.mul_le_mul h (show 120 ≤ Nat.card F ^ 2 - 1 by omega)
    omega
  interval_cases h : Nat.card F <;> norm_num at hh

variable [CharP F 2]

private theorem no_symplectic {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (B : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hB : B ∈ ChapterA.Section03.localCComponents S) (hproper : B ≠ ⊤)
    (hc : Nat.card (B ⧸ pCore 2 B) = 1080) : False := by
  obtain ⟨g,hg⟩ := FiveLocalFF.symplectic_local_placement hF hn S B hB hproper
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr (pCore 2 B) _ a (pCore_map_iso 2 a)
  rcases hg with hp | hp <;> apply not_sl2_core_card (F := F) hc <;> refine aq.trans ?_
  · change ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hp]
    exact Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF hn
  · change ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hp]
    exact Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF hn

private theorem no_g2 (hq : 2 < Nat.card F)
    (S : Sylow 2 (Atlas.G2.Model F)) (B : Subgroup (Atlas.G2.Model F))
    (hB : B ∈ ChapterA.Section03.localCComponents S) (hproper : B ≠ ⊤)
    (hc : Nat.card (B ⧸ pCore 2 B) = 1080) : False := by
  obtain ⟨g,hg⟩ := FiveLocalFF.G2.local_placement hq S B hB hproper
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr (pCore 2 B) _ a (pCore_map_iso 2 a)
  rcases hg with hp | hp <;> apply not_sl2_core_card (F := F) hc <;> refine aq.trans ?_
  · change ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hp]
    exact (QuotientGroup.quotientMulEquivOfEq Atlas.G2.LieParabolicSetup.local₁_intrinsic_pCore).trans
      Atlas.G2.LieParabolicSetup.local₁RadicalQuotientEquivSL
  · change ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hp]
    exact (QuotientGroup.quotientMulEquivOfEq Atlas.G2.LieParabolicSetup.local₂_pCore).trans
      Atlas.G2.LieParabolicSetup.local₂RadicalQuotientEquivSL


private theorem no_triality (n : ℕ) (hn : 0 < n)
    (S : Sylow 2 (Triality.Standard.BinaryCarrier n hn))
    (B : Subgroup (Triality.Standard.BinaryCarrier n hn))
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hcore : pCore 2 B ≠ ⊥) (hc : Nat.card (B ⧸ pCore 2 B) = 1080) : False := by
  have hq : 2 < 2 ^ n := by
    have hge := (Triality.Standard.binaryParameters n hn).q_ge_two
    change 2 ≤ 2 ^ n at hge
    by_contra! hh
    have htwo : (Triality.Standard.binaryParameters n hn).q = 2 := le_antisymm hh hge
    have hd := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
    rw [hc] at hd
    have hfive := (by decide : 5 ∣ 1080).trans hd
    change 5 ∣ Nat.card (Triality.Standard.Carrier (Triality.Standard.binaryParameters n hn)) at hfive
    rw [Triality.Standard.ConcreteBruhat.FixedCellCount.card_carrier,
      Triality.Standard.ConcreteBruhat.FixedCellCount.card_borel,htwo] at hfive
    norm_num at hfive
  obtain ⟨g,a,hg⟩ := FiveLocalFF.Triality.local_placement n hn hq S B hB hcore
  let c := (MulAut.conj g).subgroupMap B
  let cq := QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  cases a with
  | arms =>
    apply not_sl2_core_card (F := Triality.Standard.ExtensionField (Triality.Standard.binaryParameters n hn)) hc
    refine cq.trans ?_
    change ((B.map (MulAut.conj g).toMonoidHom) ⧸ pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* _
    rw [hg]
    exact (Triality.Standard.Parabolics.localFactorArmsQuotientEquivPSL2 _ rfl).trans
      (Theory.PSL2.sl2QuotientEquiv _).symm
  | central =>
    apply not_sl2_core_card (F := GaloisField 2 n) hc
    refine cq.trans ?_
    change ((B.map (MulAut.conj g).toMonoidHom) ⧸ pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* _
    rw [hg]
    exact (Triality.Standard.Parabolics.localFactorCentralQuotientEquivPSL2 _ rfl).trans
      (Theory.PSL2.sl2QuotientEquiv _).symm

private theorem mapped_data {G H : Type*} [Group G] [Finite G] [Group H]
    (e : G ≃* H) (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ ChapterA.Section03.localCComponents S) (hne : B ≠ ⊤)
    (hc : Nat.card (B ⧸ pCore 2 B) = 1080) (hcore : pCore 2 B ≠ ⊥) :
    B.map e.toMonoidHom ∈ ChapterA.Section03.localCComponents ((S.mapSurjective (f := e.toMonoidHom) e.surjective) : Subgroup H) ∧
      B.map e.toMonoidHom ≠ ⊤ ∧
      Nat.card ((B.map e.toMonoidHom) ⧸ pCore 2 (B.map e.toMonoidHom)) = 1080 ∧
      pCore 2 (B.map e.toMonoidHom) ≠ ⊥ := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  let a := e.subgroupMap B
  have hmap := pCore_map_iso 2 a
  refine ⟨Chapter1.Section02.localCComponents_map_of_solvable_ker hB e.toMonoidHom,?_,?_,?_⟩
  · intro hh
    apply hne
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [hh,map_top_of_surjective _ e.surjective]
  · exact (Nat.card_congr (QuotientGroup.congr _ _ a hmap).toEquiv).symm.trans hc
  · intro hh
    apply hcore
    exact (map_eq_bot_iff_of_injective _ a.injective).mp (hmap.trans hh)

/-- Inspection of the rank-two rows leaves only the genuine Ree and Tits
carriers; the full local quotient is the nonsplit triple-six group of order 1080. -/
theorem rankTwo_containing_ree_or_tits
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hne : B ≠ ⊤) (hcard : Nat.card B = 17280)
    (hc : Nat.card (B ⧸ pCore 2 B) = 1080) (hcore : pCore 2 B ≠ ⊥)
    (hm : RankTwoTheoremC G) :
    (∃ m, 1 ≤ m ∧ IsReeF4At G m) ∨ Nonempty (G ≃* Tits.ParrottGroup) := by
  cases hm with
  | linear n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact (not_binary_three_central_image hn hF S B hB hne hcard e.toMonoidHom e.surjective
      (by rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]; exact bot_le)
      (by rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]; simp)).elim
  | symplectic n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
    obtain ⟨hl,hp,ho,_⟩ := mapped_data a S B hB hne hc hcore
    exact (no_symplectic hF (by omega) (S.mapSurjective a.surjective)
      (B.map a.toMonoidHom) hl hp ho).elim
  | g2 n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    have hq : 2 < Nat.card F := by
      rw [hF]
      have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
      norm_num at hh
      omega
    obtain ⟨hl,hp,ho,_⟩ := mapped_data e S B hB hne hc hcore
    exact (no_g2 hq (S.mapSurjective e.surjective) (B.map e.toMonoidHom) hl hp ho).elim
  | triality n hn hm =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G n (by omega)).mp hm
    obtain ⟨hl,_,ho,hk⟩ := mapped_data e S B hB hne hc hcore
    exact (no_triality n (by omega) (S.mapSurjective e.surjective)
      (B.map e.toMonoidHom) hl hk ho).elim
  | symplectic_derived hm =>
    have hd := B.card_subgroup_dvd_card
    rw [hcard,Nat.card_congr (hm.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv,
      nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
  | g2_derived hm =>
    have hd := B.card_subgroup_dvd_card
    rw [hcard,Nat.card_congr hm.some.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
    norm_num at hd
  | ree m hm e => exact .inl ⟨m,hm,e⟩
  | tits hm => exact .inr hm

private theorem no_fifteen_free {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) (B : Subgroup G) (hcard : Nat.card B = 17280) (hcore : pCore 2 B ≠ ⊥)
    (hn : ∀ U : Subgroup H, U ≠ ⊥ → IsPGroup 2 U →
      ¬ 15 ∣ Nat.card (normalizer (U : Set H))) : False := by
  let U := (B.pCoreIn 2).map e.toMonoidHom
  have hu : U ≠ ⊥ := by
    intro hh
    apply hcore
    have hm := (map_eq_bot_iff_of_injective _ e.injective).mp hh
    exact (map_eq_bot_iff_of_injective _ B.subtype_injective).mp hm
  have hBN : B ≤ normalizer (B.pCoreIn 2 : Set G) :=
    B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hmap : B.map e.toMonoidHom ≤ normalizer (U : Set H) :=
    (map_mono hBN).trans (le_normalizer_map e.toMonoidHom)
  apply hn U hu ((isPGroup_pCoreIn 2 B).map e.toMonoidHom)
  apply dvd_trans ?_ (card_dvd_of_le hmap)
  rw [card_map_of_injective e.injective,hcard]
  decide

/-- None of the genuine rank-two source models contains the original residual.
The Ree and Tits exclusions use the original nontrivial two-core normalizer. -/
theorem not_rankTwo_containing
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hne : B ≠ ⊤) (hcard : Nat.card B = 17280)
    (hc : Nat.card (B ⧸ pCore 2 B) = 1080) (hcore : pCore 2 B ≠ ⊥)
    (hm : RankTwoTheoremC G) : False := by
  rcases rankTwo_containing_ree_or_tits S B hB hne hcard hc hcore hm with hre | hti
  · obtain ⟨m,hm,d,⟨e⟩⟩ := hre
    exact no_fifteen_free (e.trans d.modelEquiv) B hcard hcore
      (fun U hU hp => ReeF4.ConverseParabolics.normalizer_fifteen_free hm U hU hp)
  · obtain ⟨e⟩ := hti
    exact no_fifteen_free e B hcard hcore Tits.normalizer_fifteen_free

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
