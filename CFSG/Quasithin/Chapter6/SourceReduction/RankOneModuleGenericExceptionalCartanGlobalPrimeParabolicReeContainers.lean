module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicTrialityContainers
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ReeLocal
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound
public import Theory.SpecificGroups.Suzuki.OddSubgroups
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicTrialityContainers
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicClassicalContainers

/-!
# Ree common containers of the original diagram residual

The original full Sylow restricts to the common component before passing
through the literal two-core quotient. Every proper Ree local component
has a PSL₂ or Suzuki intrinsic quotient, whose odd-prime ranks are at most
one. The original binary PSL₃, SL₃ or Sp₄ quotient has an odd prime of
rank at least two, so its image must fill the Ree carrier.

The Ree two-rank bound 5(2m+1) and Sylow order 2^(12(2m+1)) contradict
the diagram pairs (2f,3f) and (3f,4f). In the SL₃ row, the cubic center
is retained until the inherited simplicity of the whole image removes it.
No independent simplicity or order certification of the Ree model is used.
The source application retains the same pair, both original Cartans,
relative normality, the original residual and the strict changed orbit.
Held, the classical/cubic changed-orbit argument, zero-core recognition
and full Cartan normalization remain with the original assembly.

The internal imports reuse the checked odd-rank and Sylow transport helpers.
Source: Aschbacher–Smith A.3.12 and5.2.2, printed pp.47–48,648–649,
refs/quasithin.pdf; GLS3 Lemma3.3.9 for the literal Ree rank bound.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02 LocalModels ChapterA.Section03.SourceEmbeddings

private theorem ree_two_rank_le {m : ℕ} (hm : 1 ≤ m) :
    primeRank 2 (ReeF4.Model m) ≤ 5*(2*m+1) := by
  exact (primeRank_le_iff_elementary_card_le _).mpr
    (ReeF4.ElementaryTwoBound.card_le m hm)

private theorem linear_three_not_ree
    {F : Type*} [Field F] [Finite F] {f m : ℕ} (hf : 1 < f) (hm : 1 ≤ m)
    (hF : Nat.card F = 2^f) (e : PSL(3,F) ≃* ReeF4.Model m) : False := by
  have hr := ree_two_rank_le hm
  rw [←primeRank_equiv 2 e,Matrix.PSL3Even.two_rank F (by omega) hF] at hr
  have hc := sylow_card_equiv e
    (Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF)
    (ReeF4.AutomorphismTwoRank.sylow m)
  change Nat.card (Matrix.PSL3.LinearThree.unipotent F) =
    Nat.card (ReeF4.AutomorphismTwoRank.sylow m) at hc
  rw [Matrix.PSL3.LinearThree.card_unipotent,ReeF4.AutomorphismTwoRank.sylow_card,hF,
    ←pow_mul] at hc
  have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
  omega

private theorem diagram_not_ree
    {Q : Type*} [Group Q] [Finite Q] {f m : ℕ} (hf : 1 < f) (hm : 1 ≤ m)
    [IsSimpleGroup (ReeF4.Model m)]
    (hmodel : ClassicalGroup.IsPSL Q 3 (2^f) ∨ IsSL Q 3 (2^f) ∨
      ClassicalGroup.IsPSp Q 2 (2^f)) (e : Q ≃* ReeF4.Model m) : False := by
  rcases hmodel with ⟨F,_,_,hF,⟨a⟩⟩ | ⟨F,_,_,hF,⟨a⟩⟩ | ⟨F,_,_,hF,⟨a⟩⟩
  · exact linear_three_not_ree hf hm hF (a.symm.trans e)
  · let : IsSimpleGroup SL(3,F) := (a.symm.trans e).isSimpleGroup
    let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
    have hz : center SL(3,F) = ⊥ :=
      (inferInstance : (center SL(3,F)).Normal).eq_bot_or_eq_top.resolve_right
        (fun ht => Group.IsPerfect.not_isMulCommutative SL(3,F) (center_eq_top_iff.mp ht))
    let b : PSL(3,F) ≃* SL(3,F) :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    exact linear_three_not_ree hf hm hF (b.trans (a.symm.trans e))
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let b := Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.trans (a.symm.trans e)
    have hr := ree_two_rank_le hm
    rw [←primeRank_equiv 2 b,Theory.SpecificGroups.SymplecticFour.EvenTwoRank.rank hF (by omega)] at hr
    have hc := sylow_card_equiv b
      (Theory.SpecificGroups.SymplecticFour.unipotentSylow hF (by omega))
      (ReeF4.AutomorphismTwoRank.sylow m)
    change Nat.card (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)) =
      Nat.card (ReeF4.AutomorphismTwoRank.sylow m) at hc
    rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,
      ReeF4.AutomorphismTwoRank.sylow_card,hF,←pow_mul] at hc
    have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
    omega

private theorem ree_local_not_diagram
    {m f : ℕ} (hm : 1 ≤ m) (hf : 1 < f) [IsSimpleGroup (ReeF4.Model m)]
    (htop : (⊤ : Subgroup (ReeF4.Model m)).IsCComponent)
    (S : Sylow 2 (ReeF4.Model m)) (V : Subgroup (ReeF4.Model m))
    (hl : V ∈ ChapterA.Section03.localCComponents S)
    (hmodel : ClassicalGroup.IsPSL (V ⧸ pCore 2 V) 3 (2^f) ∨
      IsSL (V ⧸ pCore 2 V) 3 (2^f) ∨
      ClassicalGroup.IsPSp (V ⧸ pCore 2 V) 2 (2^f)) : False := by
  have hV : V = ⊤ := by
    by_contra hne
    obtain ⟨g,s,hg⟩ := ReeLocal.local_placement hm htop S V hl hne
    let a := ((MulAut.conj g).subgroupMap V).trans (MulEquiv.subgroupCongr hg)
    let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
    obtain ⟨p,hp,ho,hr⟩ := diagram_odd_rank_two hf hmodel
    let : Fact p.Prime := ⟨hp⟩
    rw [primeRank_equiv p aq] at hr
    have hb : primeRank p (ReeF4.Parabolics.localFactor m s ⧸
        pCore 2 (ReeF4.Parabolics.localFactor m s)) ≤ 1 := by
      cases s with
      | linear =>
        rw [primeRank_equiv p (ReeF4.Parabolics.linearLocalQuotientEquiv m),
          ←primeRank_equiv p (Atlas.RankOneFieldAutomorphisms.slEquivPSL
            (F := ReeF4.CoefficientField m))]
        exact Matrix.SL2.binary_odd_primeRank_le_one ho
      | suzuki =>
        rw [primeRank_equiv p (ReeF4.Parabolics.suzukiLocalQuotientEquiv m)]
        let P : Sylow p (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := Classical.choice inferInstance
        exact P.primeRank_le_one_of_isCyclic
          (BenderSuzuki.MatrixGroups.suzukiSylow_isCyclic_of_ne_two (by omega)
            (by intro he; subst p; exact ho.not_two_dvd_nat (dvd_refl 2)) P)
    omega
  let e : V ≃* ReeF4.Model m := (MulEquiv.subgroupCongr hV).trans topEquiv
  let := htop.perfect
  let : Group.IsPerfect (ReeF4.Model m) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := ReeF4.Model m)).toMonoidHom) topEquiv.surjective
  have hc : pCore 2 (ReeF4.Model m) = ⊥ := by
    rcases (inferInstance : (pCore 2 (ReeF4.Model m)).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · let : Group.IsNilpotent (⊤ : Subgroup (ReeF4.Model m)) := ht ▸ pCore_isNilpotent
      let : Group.IsSolvable (ReeF4.Model m) := Group.isSolvable_of_surjective
        (f := (topEquiv (G := ReeF4.Model m)).toMonoidHom) topEquiv.surjective
      exact (Group.IsPerfect.not_isSolvable (ReeF4.Model m) inferInstance).elim
  let eq : (V ⧸ pCore 2 V) ≃* ReeF4.Model m :=
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)
  exact diagram_not_ree hf hm hmodel eq

variable {G : Type*} [Group G] [Finite G]

/-- A simple Ree common image cannot contain the original diagram residual.
Its simplicity is inherited from the ordinary common-container row. -/
theorem SelectedSourceModels.parabolic_common_not_ree
    {T : Sylow 2 G} {H R X I : Subgroup G} {m : ℕ}
    (hs : SelectedSourceModels H R) (hn : ¬ (R.subgroupOf H).IsCComponent)
    (hTH : (T : Subgroup G) ≤ H) (hHX : H ≤ X)
    (_hIX : I ≤ X) (hI : (I.subgroupOf X).IsCComponent) (hKI : residual H ≤ I)
    (hm : 1 ≤ m)
    (hsi : IsSimpleGroup ((I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)))) :
    ¬ IsReeF4At ((I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) m := by
  intro hmodel
  let Y := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  obtain ⟨d,⟨e₀⟩⟩ := hmodel
  let e := e₀.trans d.modelEquiv
  let : IsSimpleGroup Y := hsi
  let : IsSimpleGroup (ReeF4.Model m) := e.symm.isSimpleGroup
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  have hY : (⊤ : Subgroup Y).IsCComponent := by
    simpa only [subgroupOf_self] using (hI.map_quotient (pCore 2 X)).subgroupOf le_rfl
  have htop : (⊤ : Subgroup (ReeF4.Model m)).IsCComponent := by
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using hY.map_equiv e
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
  apply ree_local_not_diagram hm hf htop
    (S.mapSurjective (e.surjective.comp (q.subgroupMap_surjective _))) V
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl r)
  rcases hmodel with ⟨F,_,_,hF,⟨z⟩⟩ | ⟨F,_,_,hF,⟨z⟩⟩ | ⟨F,_,_,hF,⟨z⟩⟩
  · exact .inl ⟨F,inferInstance,inferInstance,hF,⟨b.symm.trans (aq.trans z)⟩⟩
  · exact .inr (.inl ⟨F,inferInstance,inferInstance,hF,⟨b.symm.trans (aq.trans z)⟩⟩)
  · exact .inr (.inr ⟨F,inferInstance,inferInstance,hF,⟨b.symm.trans (aq.trans z)⟩⟩)


/-- The same original pair excludes Ree common containers, retaining
classical equality, Held and the full cubic row with its strict changed orbit. -/
theorem source_prime_pair_parabolic_ree_exclusion
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
                   Nonempty (Ibar ≃* Held.He))) ∨
                  (Nonempty (center Ibar ≃* Multiplicative (ZMod 3)) ∧
                    (∃ f : ℕ, 1 < f ∧ (2^f) % 3 = 1 ∧ IsSL Ibar 3 (2^f) ∧
                      residual H = I ∧
                      IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2^f) ∧
                      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^f) ∧
                      p = 5 ∧ ¬ n ∣ f))))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_parabolic_triality_exclusion h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,hm⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,?_⟩
  rcases hm with ⟨hsi,hm⟩ | hm
  · refine .inl ⟨hsi,?_⟩
    rcases hm with hclass | ⟨m,hm,hree⟩ | hheld
    · exact .inl hclass
    · exact (hs.parabolic_common_not_ree hn hH.1.1.2 le_sup_right hIX hI hKI hm hsi hree).elim
    · exact .inr hheld
  · exact .inr hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
