module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicClassicalContainers
public import Theory.SpecificGroups.Triality.PerfectSylowOvergroups
public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.SpecificGroups.PSL3.SplitPrimeRank
public import Theory.SpecificGroups.SymplecticFour.SplitTorusRank
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicClassicalContainers

/-!
# Binary triality cannot contain the original diagram residual

Every original binary PSL₃, SL₃ or Sp₄ diagram quotient has an odd prime
of rank at least two. The split torus supplies the prime; in the projective
cubic case the diagonal/cycle subgroup preserves cubic rank. Passing through
the literal two-core kernel retains that rank and the original full Sylow.

A perfect subgroup of odd-prime rank two cannot lie in a proper full-Sylow
overgroup of genuine triality, including the field-two endpoint. The original
local component would therefore be the whole triality group. Its two-rank
and Sylow-order formulas would then identify (2f,3f) or (3f,4f) with
(5g,12g), which is impossible. In the special linear row the cubic center
is retained until simplicity of this hypothetical whole group kills it.

The source and Chapter 12 applications preserve the same selected pair,
original Cartans and residual, relative normality and strict changed orbit.
Ree and Held containers, classical/cubic changed-orbit contradictions,
zero-core recognition and universal Cartan normalization remain explicit.
The internal import reuses only the earlier Sylow-order transport helper.

Source: Aschbacher–Smith A.3.12, 5.1.10 and 5.2.2, printed
pp.47–48,634,648–649, refs/quasithin.pdf. The imported genuine triality
root geometry includes the exponent-one case without a solvable-supplement
assumption.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02 LocalModels ChapterA.Section03.SourceEmbeddings

private theorem binary_split_prime {f : ℕ} (hf : 1 < f) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ 2^f-1 := by
  have hq : 4 ≤ 2^f := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ f)
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : 2^f-1 ≠ 1)
  refine ⟨p,hp,?_,hd⟩
  rcases hp.eq_two_or_odd with he | he
  · subst p
    have h2 : 2 ∣ 2^f := dvd_pow_self 2 (by omega)
    have hzero := Nat.mod_eq_zero_of_dvd h2
    have hone := Nat.mod_eq_zero_of_dvd hd
    omega
  · exact Nat.odd_iff.mpr he

private theorem diagram_odd_rank_two
    {Q : Type*} [Group Q] [Finite Q] {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL Q 3 (2^f) ∨ IsSL Q 3 (2^f) ∨
      ClassicalGroup.IsPSp Q 2 (2^f)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 2 ≤ primeRank p Q := by
  obtain ⟨p,hp,ho,hd⟩ := binary_split_prime hf
  let : Fact p.Prime := ⟨hp⟩
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · by_cases he : Even f
    · refine ⟨3,by decide,by decide,?_⟩
      rw [primeRank_equiv 3 e]
      exact Theory.SpecificGroups.SignedThreeCubicRank.linear_projective hF he
    · have hp3 : p ≠ 3 := by
        intro h3
        subst p
        exact he ((Nat.BinaryTorusParity.three_dvd_sub_one_iff f).mp hd)
      refine ⟨p,hp,ho,?_⟩
      rw [primeRank_equiv p e]
      exact Matrix.PSL3.SplitPrimeRank.projective_rank F hp3 (hF ▸ hd)
  · refine ⟨p,hp,ho,?_⟩
    rw [primeRank_equiv p e]
    exact Matrix.PSL3.SplitPrimeRank.special_rank F (hF ▸ hd)
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    refine ⟨p,hp,ho,?_⟩
    rw [primeRank_equiv p (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)]
    exact Theory.SpecificGroups.SymplecticFour.split_torus_prime_rank hp (hF ▸ hd)

private theorem linear_three_not_triality
    {F : Type*} [Field F] [Finite F] {f g : ℕ} (hf : 1 < f) (hg : 0 < g)
    (hF : Nat.card F = 2^f)
    (e : PSL(3,F) ≃* Triality.Standard.BinaryCarrier g hg) : False := by
  have hr := primeRank_equiv 2 e
  rw [Matrix.PSL3Even.two_rank F (by omega) hF,
    Triality.Standard.TwoRank.twoRank_eq_five_mul] at hr
  have hc := sylow_card_equiv e
    (Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF)
    (Triality.Standard.Parabolics.unipotentSylow (Triality.Standard.binaryParameters g hg) rfl)
  change Nat.card (Matrix.PSL3.LinearThree.unipotent F) =
    Nat.card (Triality.Standard.Parabolics.unipotent (Triality.Standard.binaryParameters g hg)) at hc
  rw [Matrix.PSL3.LinearThree.card_unipotent,
    Triality.Standard.Parabolics.card_unipotent_binary _ rfl,hF] at hc
  change (2^f)^3 = (2^g)^12 at hc
  rw [←pow_mul,←pow_mul] at hc
  have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
  omega

private theorem diagram_not_triality
    {Q : Type*} [Group Q] [Finite Q] {f g : ℕ} (hf : 1 < f) (hg : 0 < g)
    (hm : ClassicalGroup.IsPSL Q 3 (2^f) ∨ IsSL Q 3 (2^f) ∨
      ClassicalGroup.IsPSp Q 2 (2^f))
    (e : Q ≃* Triality.Standard.BinaryCarrier g hg) : False := by
  rcases hm with ⟨F,_,_,hF,⟨a⟩⟩ | ⟨F,_,_,hF,⟨a⟩⟩ | ⟨F,_,_,hF,⟨a⟩⟩
  · exact linear_three_not_triality hf hg hF (a.symm.trans e)
  · let : IsSimpleGroup SL(3,F) := (a.symm.trans e).isSimpleGroup
    let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
    have hz : center SL(3,F) = ⊥ :=
      (inferInstance : (center SL(3,F)).Normal).eq_bot_or_eq_top.resolve_right
        (fun ht => Group.IsPerfect.not_isMulCommutative SL(3,F) (center_eq_top_iff.mp ht))
    let b : PSL(3,F) ≃* SL(3,F) :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    exact linear_three_not_triality hf hg hF (b.trans (a.symm.trans e))
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let b := Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.trans (a.symm.trans e)
    have hr := primeRank_equiv 2 b
    rw [Theory.SpecificGroups.SymplecticFour.EvenTwoRank.rank hF (by omega),
      Triality.Standard.TwoRank.twoRank_eq_five_mul] at hr
    have hc := sylow_card_equiv b
      (Theory.SpecificGroups.SymplecticFour.unipotentSylow hF (by omega))
      (Triality.Standard.Parabolics.unipotentSylow (Triality.Standard.binaryParameters g hg) rfl)
    change Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)) =
      Nat.card (Triality.Standard.Parabolics.unipotent (Triality.Standard.binaryParameters g hg)) at hc
    rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,
      Triality.Standard.Parabolics.card_unipotent_binary _ rfl,hF] at hc
    change (2^f)^4 = (2^g)^12 at hc
    rw [←pow_mul,←pow_mul] at hc
    have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
    omega

private theorem triality_local_not_diagram
    {g f : ℕ} (hg : 0 < g) (hf : 1 < f)
    (S : Sylow 2 (Triality.Standard.BinaryCarrier g hg))
    (V : Subgroup (Triality.Standard.BinaryCarrier g hg))
    (hl : V ∈ ChapterA.Section03.localCComponents S)
    (hm : ClassicalGroup.IsPSL (V ⧸ pCore 2 V) 3 (2^f) ∨
      IsSL (V ⧸ pCore 2 V) 3 (2^f) ∨
      ClassicalGroup.IsPSp (V ⧸ pCore 2 V) 2 (2^f)) : False := by
  let Y := Triality.Standard.BinaryCarrier g hg
  let := hl.perfect
  let : Group.IsPerfect V := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show V ≤ V ⊔ (S : Subgroup Y) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  obtain ⟨p,hp,ho,hr⟩ := diagram_odd_rank_two hf hm
  let : Fact p.Prime := ⟨hp⟩
  rw [primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup] at hr
  have he : V ⊔ (S : Subgroup Y) = ⊤ :=
    Triality.Standard.PerfectSylowOvergroups.eq_top_of_perfect_odd_rank_two g hg S
      (V ⊔ (S : Subgroup Y)) le_sup_right V.subtype V.subtype_injective
      (by simpa only [range_subtype] using (le_sup_left : V ≤ V ⊔ (S : Subgroup Y))) ho hr
  let : IsQuasisimple Y := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (Triality.Standard.binaryCarrier_center_eq_bot g hg)).trans QuotientGroup.quotientBot).isSimpleGroup }
  have ht : (⊤ : Subgroup Y).IsCComponent :=
    (show IsComponent Y ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  change (V.subgroupOf (V ⊔ (S : Subgroup Y))).IsCComponent at hl
  rw [he] at hl
  have hV : V = ⊤ := le_antisymm le_top (subgroupOf_eq_top.mp (ht.eq_top_of_isCComponent hl))
  let e : V ≃* Y := (MulEquiv.subgroupCongr hV).trans topEquiv
  have hc : pCore 2 Y = ⊥ := by
    rcases (inferInstance : (pCore 2 Y).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · let : Group.IsNilpotent (⊤ : Subgroup Y) := ht ▸ pCore_isNilpotent
      let : Group.IsSolvable Y := Group.isSolvable_of_surjective
        (f := (topEquiv (G := Y)).toMonoidHom) topEquiv.surjective
      exact (Group.IsPerfect.not_isSolvable Y inferInstance).elim
  let eq : (V ⧸ pCore 2 V) ≃* Y :=
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)
  exact diagram_not_triality hf hg hm eq

variable {G : Type*} [Group G] [Finite G]

/-- No binary triality common component contains the original diagram residual.
The original full Sylow is restricted before the literal two-core quotient. -/
theorem SelectedSourceModels.parabolic_common_not_triality
    {T : Sylow 2 G} {H R X I : Subgroup G} {g : ℕ}
    (hs : SelectedSourceModels H R) (hn : ¬ (R.subgroupOf H).IsCComponent)
    (hTH : (T : Subgroup G) ≤ H) (hHX : H ≤ X)
    (_hIX : I ≤ X) (hI : (I.subgroupOf X).IsCComponent) (hKI : residual H ≤ I)
    (hg : 1 ≤ g) :
    ¬ Triality.Standard.IsTrialityGroupAt (2^g)
      ((I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) := by
  intro hm
  let Y := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff Y g (by omega)).mp hm
  let K := residual H
  have hKH : K ≤ H := map_subtype_le _
  have hKX : K ≤ X := hKH.trans hHX
  have hKlocal : K ∈ ChapterA.Section03.localCComponents (T : Subgroup G) := by
    change (K.subgroupOf (K ⊔ (T : Subgroup G))).IsCComponent
    rw [show K ⊔ (T : Subgroup G) = H from residual_sup_sylow T H hTH]
    exact hs.residual_component_of_not_right hn
  obtain ⟨S,_,hl⟩ := exists_local_sylow_restriction (T.subtype (hTH.trans hHX))
    (local_restrict hKlocal hKX) (subgroupOf_mono X hKI) hI.subnormal
  let q := QuotientGroup.mk' (pCore 2 X)
  let r₀ := q.subgroupMap (I.subgroupOf X)
  let r := e.toMonoidHom.comp r₀
  have hr : IsPGroup 2 r.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let : Group.IsNilpotent r.ker := hr.isNilpotent
  let : Group.IsSolvable r.ker := inferInstance
  let V₀ := (K.subgroupOf X).subgroupOf (I.subgroupOf X)
  let V := V₀.map r
  let a : V₀ ≃* pResidual 2 H :=
    ((subgroupOfEquivOfLe (subgroupOf_mono X hKI)).trans (subgroupOfEquivOfLe hKX)).trans
      ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hrv : IsPGroup 2 (r.subgroupMap V₀).ker := by
    rw [ker_subgroupMap]
    exact hr.comap_subtype
  let b := (r.subgroupMap V₀).quotientPCoreEquivOfSurjective (r.subgroupMap_surjective V₀) hrv
  obtain ⟨f,hf,_,hmodel⟩ := hs.resolve_left hn
  apply triality_local_not_diagram (by omega : 0 < g) hf
    (S.mapSurjective (e.surjective.comp (q.subgroupMap_surjective _))) V
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl r)
  rcases hmodel with ⟨F,_,_,hF,⟨z⟩⟩ | ⟨F,_,_,hF,⟨z⟩⟩ | ⟨F,_,_,hF,⟨z⟩⟩
  · exact .inl ⟨F,inferInstance,inferInstance,hF,⟨b.symm.trans (aq.trans z)⟩⟩
  · exact .inr (.inl ⟨F,inferInstance,inferInstance,hF,⟨b.symm.trans (aq.trans z)⟩⟩)
  · exact .inr (.inr ⟨F,inferInstance,inferInstance,hF,⟨b.symm.trans (aq.trans z)⟩⟩)

/-- The same source pair excludes every binary triality common container,
including the field-two endpoint, while retaining the strict changed orbit. -/
theorem source_prime_pair_parabolic_triality_exclusion
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R < T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
            ¬ (R.subgroupOf H).IsCComponent ∧
            (∃ f : ℕ, 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
              (ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))) ∧
            let X := normalizer (normalizingSylow T R : Set G) ⊔ H
            ∃ I : Subgroup G, residual H ≤ I ∧ I ≤ X ∧
              (I.subgroupOf X).IsCComponent ∧ (I.subgroupOf X).Normal ∧
              conjugateSpanBy R (U : Subgroup G) < I ∧
              let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
              IsQuasisimple Ibar ∧
                ((IsSimpleGroup Ibar ∧
                  ((∃ g : ℕ, 1 < g ∧
                    (ClassicalGroup.IsPSL Ibar 3 (2^g) ∨ ClassicalGroup.IsPSp Ibar 2 (2^g)) ∧
                    residual H = I) ∨
                   (∃ m : ℕ, 1 ≤ m ∧ IsReeF4At Ibar m) ∨
                   Nonempty (Ibar ≃* Held.He))) ∨
                  (Nonempty (center Ibar ≃* Multiplicative (ZMod 3)) ∧
                    (∃ f : ℕ, 1 < f ∧ (2^f) % 3 = 1 ∧ IsSL Ibar 3 (2^f) ∧
                      residual H = I ∧
                      IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2^f) ∧
                      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^f) ∧
                      p = 5 ∧ ¬ n ∣ f))))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_parabolic_classical_containers h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,hm⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,?_⟩
  rcases hm with ⟨hsi,hm⟩ | hm
  · refine .inl ⟨hsi,?_⟩
    rcases hm with hclass | ⟨g,hg,htrial⟩ | hree | hheld
    · exact .inl hclass
    · exact (hs.parabolic_common_not_triality hn hH.1.1.2 le_sup_right hIX hI hKI hg htrial).elim
    · exact .inr (.inl hree)
    · exact .inr (.inr hheld)
  · exact .inr hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
