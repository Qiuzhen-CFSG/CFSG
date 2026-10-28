module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic

public import Theory.GroupTheory.PerfectNormalizerLift

/-!
# Local alternating-six sections in characteristic-two rank one and two

The checked full-Sylow placement theorems identify proper local components
in PSL₃, Sp₄ and G₂ with the original parabolic residuals. Their two-core
quotients are SL₂ over the same field. The order360 of A₆ is not an SL₂
order, so the original A₆ section excludes each such row. Rank one is
excluded by solvable proper Sylow overgroups. The central projection of
SL₃ preserves the smaller section because its kernel there lies in the
two-core; the binary derived G₂ endpoint is excluded by order6048.

The source consumer is Section12.6's SmallThompsonExclusion, which applies
these results to the actual image of L_v in K_v/O₂(K_v).
Source: Aschbacher--Smith A.3.12, printed pp.47--48, and12.6.14, p.826,
combined manuscript of1 March2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SixLocalFF
variable {F : Type*} [Field F] [Finite F]

/-- The A₆ order is not an SL₂ order over any finite field. -/
theorem not_equiv_sl2 (e : alternatingGroup (Fin 6) ≃* SL(2,F)) : False := by
  have hc : Nat.card F * (Nat.card F ^ 2 - 1) = 360 := by
    rw [← GorensteinWalter.sl2_card_formula,
      Nat.card_congr e.symm.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hl : Nat.card F ≤ 7 := by
    by_contra! hb
    have hs : 63 ≤ Nat.card F ^ 2 - 1 := by
      have hh : 64 ≤ Nat.card F ^ 2 := by nlinarith
      omega
    have hh := Nat.mul_le_mul (show 8 ≤ Nat.card F by omega) hs
    omega
  interval_cases h : Nat.card F <;> simp_all

theorem not_sl2_core_section {A : Type*} [Group A]
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6))
    (a : (A ⧸ pCore 2 A) ≃* SL(2,F)) : False :=
  not_equiv_sl2 (e.symm.trans a)

variable [CharP F 2]

theorem not_linear_three {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 PSL(3,F)) (B : Subgroup PSL(3,F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  obtain ⟨g,hg⟩ := FiveLocalFF.linear_three_local_placement hF hn S B hB hproper
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr (pCore 2 B) _ a (pCore_map_iso 2 a)
  rcases hg with hp | hp <;> apply not_sl2_core_section (F := F) e <;> refine aq.trans ?_
  · change ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hp]
    exact Matrix.PSL3.LinearThree.pointLocalCoreQuotientEquiv F
  · change ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hp]
    exact Matrix.PSL3.LinearThree.lineLocalCoreQuotientEquiv F

theorem not_symplectic {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (B : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  obtain ⟨g,hg⟩ := FiveLocalFF.symplectic_local_placement hF hn S B hB hproper
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr (pCore 2 B) _ a (pCore_map_iso 2 a)
  rcases hg with hp | hp <;> apply not_sl2_core_section (F := F) e <;> refine aq.trans ?_
  · change ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hp]
    exact Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF hn
  · change ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)
    rw [hp]
    exact Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF hn

theorem not_g2 (hq : 2 < Nat.card F)
    (S : Sylow 2 (Atlas.G2.Model F)) (B : Subgroup (Atlas.G2.Model F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  obtain ⟨g,hg⟩ := FiveLocalFF.G2.local_placement hq S B hB hproper
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr (pCore 2 B) _ a (pCore_map_iso 2 a)
  rcases hg with hp | hp <;> apply not_sl2_core_section (F := F) e <;> refine aq.trans ?_
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

theorem not_linear_three_all {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 PSL(3,F)) (B : Subgroup PSL(3,F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  by_cases hn : 1 < n
  · exact not_linear_three hF hn S B hB hproper e
  have hn1 : n = 1 := by
    have hf := Finite.one_lt_card (α := F)
    by_cases hz : n = 0
    · simp [hz] at hF
      omega
    · omega
  have htwo : Nat.card F = 2 := by simpa [hn1] using hF
  have hd := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
    Matrix.PSL3.LinearThree.card_projective F,htwo] at hd
  norm_num [Nat.factorial] at hd


theorem not_linear_two
    (S : Sylow 2 SL(2,F)) (B : Subgroup SL(2,F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  have hq : 2 < Nat.card F := by
    have hf := Finite.one_lt_card (α := F)
    by_contra! hn
    have he : Nat.card F = 2 := by omega
    have hd := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
      GorensteinWalter.sl2_card_formula,he] at hd
    norm_num [Nat.factorial] at hd
  let : IsSimpleGroup SL(2,F) :=
    Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hq
  have ht : B ⊔ (S : Subgroup SL(2,F)) = ⊤ := by
    by_contra hn
    let := Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup
      S (B ⊔ (S : Subgroup SL(2,F))) le_sup_right hn
    exact hB.not_isSolvable inferInstance
  have hc : B.IsCComponent := by
    have hh := hB
    change (B.subgroupOf (B ⊔ (S : Subgroup SL(2,F)))).IsCComponent at hh
    rw [ht] at hh
    simpa only [map_subgroupOf_eq_of_le le_top] using hh.map_subtype .top
  exact (hc.subnormal.eq_bot_or_top_of_isSimpleGroup inferInstance).elim hc.ne_bot hproper

theorem not_special_linear_three {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 SL(3,F)) (B : Subgroup SL(3,F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  let f := Matrix.PSL3.projection F
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect B := by
    let := hB.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup SL(3,F)) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  have hfc : f.ker ≤ center SL(3,F) := (Matrix.PSL3.projection_ker F).le
  have hk : IsPGroup 2 (f.subgroupMap B).ker := by
    apply pCore_isPGroup.to_le
    intro b hb
    have hc : (b : SL(3,F)) ∈ center SL(3,F) := hfc (congrArg Subtype.val hb)
    let q := QuotientGroup.mk' (pCore 2 B)
    have hz : e (q b) ∈ center (alternatingGroup (Fin 6)) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨z,rfl⟩ := e.surjective y
      obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
      rw [←e.map_mul,←e.map_mul,←q.map_mul,←q.map_mul]
      exact congrArg (fun x : B => e (q x)) (Subtype.ext (mem_center_iff.mp hc z))
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hz
    exact (QuotientGroup.eq_one_iff b).mp (e.injective (hz.trans e.map_one.symm))
  have hp : B.map f ≠ ⊤ := by
    intro ht
    apply hproper
    apply top_unique
    apply le_of_map_le_of_perfect f hfc ⊤ B
    rw [ht]
    exact le_top
  let : Group.IsSolvable f.ker := by
    dsimp only [f]
    rw [Matrix.PSL3.projection_ker]
    infer_instance
  exact not_linear_three_all hF
    (S.mapSurjective (Matrix.PSL3.projection_surjective F)) (B.map f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB f) hp
    (((f.subgroupMap B).pCoreQuotientEquiv (f.subgroupMap_surjective B) hk).symm.trans e)


omit [CharP F 2] in
theorem not_g2_two_derived (hF : Nat.card F = 2)
    (B : Subgroup (commutator (Atlas.G2.Model F)))
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  have hd := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,
    Atlas.G2.DerivedEvenOrder.card_derived_binary hF] at hd
  norm_num [Nat.factorial] at hd

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SixLocalFF


