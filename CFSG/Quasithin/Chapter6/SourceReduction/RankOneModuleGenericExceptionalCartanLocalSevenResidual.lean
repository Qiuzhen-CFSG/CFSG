module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalMathieu
public import Theory.SpecificGroups.Alternating.SevenRankOneCover
public import CFSG.Quasithin.ChapterF.Section01.RankOneSmallTwoPart
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicFiniteContainers
/-!
# The original residual in the alternating-seven covering rows

In the same normal containing component selected by the Cartan escape
sieve, the absence of 25 in the actual quotient order fixes the original
seed. Its full Sylow orbit is therefore the original residual. The source
E.2.2 alternatives and the literal quotient inclusion eliminate the
rank-two diagram residuals. The remaining rank-one quotient has two-part
at most eight. The seven-point coset argument, including its central-cover
version, then forces field order four. The original right Hall is cubic.

The two-core of the residual, the containing two-core and the cubic center
of the covering row remain distinct throughout. No A5 residual mark is an
input. The final original-input reduction retains every earlier clause,
including the original binary-triality endpoint. Excluding the triple cover,
constructing an escaping inverted cubic and exhausting the other containing
rows remain obligations of the local Cartan sieve.

Source: Aschbacher--Smith 5.1.10--13, printed pp.634--637,
refs/quasithin.pdf; the A7 coset argument is in SevenRankOneCover.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
/-- Both actual alternating-seven covering rows force the literal original
residual quotient to be PSL₂(4), once the original residual is the local seed. -/
theorem residual_section_of_alternating_seven
    {T : Sylow 2 G} {L W H A Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent)
    (hRC : residual H ≤ C.map Y.subtype)
    (hm : IsAlternating (C ⧸ pCore 2 C) 7 ∨ IsAlternatingCover (C ⧸ pCore 2 C) 7) :
    ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 := by
  have hR' : (pResidual 2 H).IsCComponent := by
    have hh := hR.1
    rw [residual_sup_sylow T H hH.1.1.2] at hh
    simpa only [residual,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hh
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hTY := hH.1.1.2.trans hY.2
  let q := QuotientGroup.mk' (pCore 2 Y)
  let S := T.subtype hTY
  let Rbar := ((residual H).subgroupOf Y).map q
  let Cbar := C.map q
  have hl : (residual H).subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTY hRY).mp ⟨hRY,hR⟩
  have hRC' : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hle : Rbar ≤ Cbar := map_mono hRC'
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  let U := Rbar.subgroupOf Cbar
  let r := q.subgroupMap ((residual H).subgroupOf Y)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let e₀ := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let e₁ := e₀.trans (subgroupOfEquivOfLe hRY).symm
  let e₂ := r.pCoreQuotientEquiv (q.subgroupMap_surjective _) hr
  let e₃ := (subgroupOfEquivOfLe hle).symm
  let eR : ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* (U ⧸ pCore 2 U) :=
    (QuotientGroup.congr _ _ e₁ (pCore_map_iso 2 e₁)).trans
      (e₂.trans (QuotientGroup.congr _ _ e₃ (pCore_map_iso 2 e₃)))
  let eC : Cbar ≃* (C ⧸ pCore 2 C) := (cComponentTwoCoreQuotientEquiv hC).symm
  have ho : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      (hH.1.1.2.trans (le_normalizer_residual H))) (le_componentOrbit _ _)
  have hlt := seed_image_lt_container h.qtke (map_subtype_le _) hH.1.1.2
    hR ho hY hescape C hC hRC
  have hu : U ≠ ⊤ := fun he => hlt.not_ge (subgroupOf_eq_top.mp he)
  have hCcard : Nat.card (C ⧸ pCore 2 C) ∣ 7560 := by
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      norm_num [Nat.factorial]
    · obtain ⟨_,⟨a⟩,⟨e⟩⟩ := hm
      rw [card_eq_card_quotient_mul_card_subgroup (center (C ⧸ pCore 2 C)),
        Nat.card_congr e.toEquiv,Nat.card_congr a.toEquiv,
        nat_card_alternatingGroup,Nat.card_fin]
      norm_num [Nat.factorial]
  have hd : Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ∣ 7560 := by
    rw [Nat.card_congr eR.toEquiv]
    have hh := (card_quotient_dvd_card (pCore 2 U)).trans U.card_subgroup_dvd_card
    rw [Nat.card_congr eC.toEquiv] at hh
    exact hh.trans hCcard
  have hmodel : ChapterF.Source.IsRankOneModel
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
    rcases Global.right_source_cases h.qtke h.sylow_normalizes hH hgen with hs | hs
    · obtain ⟨K,f,hK,hqs,_,_,hc | hc⟩ := hs
      · have hKR : K = pResidual 2 H := by
          apply hK.eq_of_le hR'
          let := hK.perfect
          apply le_sInf
          rintro N ⟨hn,hN⟩
          let := hn
          let : Group.IsNilpotent (H ⧸ N) := hN.isNilpotent
          exact (le_solvableResidual_of_isPerfect K).trans (solvableResidual_le_of_solvable_quotient N)
        subst K
        obtain ⟨t,_,hne,_⟩ := hc.1.exchanged_product
        exact (hne (mem_normalizer_iff_map_conj_eq.mp
          (show t⁻¹ ∈ normalizer (pResidual 2 H : Set H) by
            rw [normalizer_eq_top]; exact mem_top _)).symm).elim
      · have he : K = pResidual 2 H :=
          BenderHall.SingleClauses.component_eq_residual (S := T.subtype hH.1.1.2) hc.1 hK
        subst K
        have hO : pCore 2 H ≤ sourceKernel ((normalizer (L : Set G)).subgroupOf H) := by
          apply normal_le_normalCore.mpr
          exact (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2)).trans
            (comap_mono h.sylow_normalizes)
        exact Prime.single_bender_component_quotient hK hqs hO hc.1 hc.2
    · obtain ⟨K,f,hK,hqs,_,hf,hc,hm⟩ := hs
      have hmodels := Prime.diagram_source_residual_quotient h.sylow_normalizes hH.1.1.2 hK hqs hc hf hm
      have hf2 := Prime.diagram_finite_order hf (by simp [Prime.finiteOrders])
        (hd.trans (by decide : 7560 ∣ 604800)) hmodels
      subst f
      rcases hmodels with hlin | hsl | hsp
      · exact (not_linear_four_residual_of_escape h.qtke h.sylow_normalizes hH hY hescape hlin).elim
      · obtain ⟨F,_,_,hF,⟨a⟩⟩ := hsl
        rw [Nat.card_congr a.toEquiv,
          Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF] at hd
        norm_num at hd
      · obtain ⟨F,_,_,hF,⟨a⟩⟩ := hsp
        let : Fintype F := Fintype.ofFinite F
        let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
          (by simpa only [Nat.card_eq_fintype_card] using hF)
        let b := a.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
        rw [Nat.card_congr b.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF] at hd
        norm_num at hd
  have hns : ¬ Group.IsSolvable ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
    intro hs
    let := hs
    let : Group.IsNilpotent (pCore 2 (pResidual 2 H)) := pCore_isNilpotent
    exact hR'.not_isSolvable (Group.isSolvable_of_ker_le_range
      (pCore 2 (pResidual 2 H)).subtype
      (QuotientGroup.mk' (pCore 2 (pResidual 2 H))) (by simp))
  have hsmall : ¬ 16 ∣ Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
    intro hh
    have := hh.trans hd
    norm_num at this
  obtain ⟨f,hf,_,hlinear⟩ := hmodel.binary_of_small_twoPart hns hsmall
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hlinear
  let : Group.IsPerfect ((residual H).subgroupOf Y) :=
    Chapter1.mem_L_isPerfect hl
  let : Group.IsPerfect Rbar := Group.IsPerfect.map _
  let : Group.IsPerfect U := Group.IsPerfect.ofSurjective
    (f := e₃.toMonoidHom) e₃.surjective
  let : Group.IsPerfect Cbar := (hC.map_quotient (pCore 2 Y)).perfect
  have he : Nonempty (((C ⧸ pCore 2 C) ⧸ center (C ⧸ pCore 2 C)) ≃*
      alternatingGroup (Fin 7)) := by
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      have hc : center (C ⧸ pCore 2 C) = ⊥ := by
        apply eq_bot_iff.mpr
        intro x hx
        have hh := (centerCongr e ⟨x,hx⟩).property
        change e x ∈ center (alternatingGroup (Fin 7)) at hh
        rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
        exact e.map_eq_one_iff.mp hh
      exact ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e⟩
    · exact hm.2.2
  let eZ := QuotientGroup.congr _ _ eC (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr eC ⟨x,hx⟩).property
    · intro y hy
      exact ⟨eC.symm y,(centerCongr eC.symm ⟨y,hy⟩).property,eC.apply_symm_apply y⟩)
  have hf2 := alternatingGroup.SevenRankOneSection.degree_eq_two_of_central_cover
    (eZ.trans he.some) U hu hF hf (eR.symm.trans a)
  exact ⟨F,inferInstance,inferInstance,by simpa [hf2] using hF,⟨a⟩⟩

/-- Normality of the original container and its actual A7 or triple-cover
marking identify the original seed, residual quotient and right Hall order. -/
theorem normal_alternating_seven_residual_and_hall
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : IsAlternating (C ⧸ pCore 2 C) 7 ∨ IsAlternatingCover (C ⧸ pCore 2 C) 7) :
    K = residual H ∧
      ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
      Nat.card B = 3 := by
  have hKR : K = residual H := by
    apply seed_eq_residual_of_normal_twentyFive_free_container h.qtke hK hKT horbit
      hY hescape C hKC
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      norm_num [Nat.factorial]
    · obtain ⟨_,⟨a⟩,⟨e⟩⟩ := hm
      rw [card_eq_card_quotient_mul_card_subgroup (center (C ⧸ pCore 2 C)),
        Nat.card_congr e.toEquiv,Nat.card_congr a.toEquiv,
        nat_card_alternatingGroup,Nat.card_fin]
      norm_num [Nat.factorial]
  have hfour := residual_section_of_alternating_seven h hH hgen hY hescape
    (hKR ▸ hK) C hC (hKR ▸ hKC) hm
  have hA5 : Nonempty ((residual H ⧸ pCore 2 (residual H)) ≃* alternatingGroup (Fin 5)) := by
    let a := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
    let eq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
    obtain ⟨F,_,_,hF,⟨b⟩⟩ := hfour
    exact ⟨eq.symm.trans (b.trans
      (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)⟩
  exact ⟨hKR,hfour,right_hall_card_three_of_residual_A5 h hH hgen c hA5⟩


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- Both alternating-seven covering rows have the original PSL₂(4)
residual quotient and right cubic. Every previous clause, including the
original surviving binary-triality configuration, is retained. -/
theorem localCartan_escape_seed_seven_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
          n = 2 ∧ Nat.card A = 3 ∧ A ≤ C.map Y.subtype ∧
          localBorel T L ≤ omegaCentralizer T ∧
          IsOneOrTwoA5Modules L (layer L W) ∧ Nat.card B = 7 ∧
          B ≤ centralizer
            (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G)) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
            ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
            IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p)) ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko4.Model) ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22) ∧
        (Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M23) →
          K = residual H ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
          Nat.card B = 3) ∧
        (IsAlternating (C ⧸ pCore 2 C) 7 ∨ IsAlternatingCover (C ⧸ pCore 2 C) 7 →
          K = residual H ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
          Nat.card B = 3) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hOdd,hJ4,hM22,hM23⟩ :=
    localCartan_escape_seed_mathieu_reduction h hH hgen c hY hescape
  let : C.Normal := hCn
  exact ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hOdd,hJ4,hM22,hM23,
    fun hm => LocalSieve.normal_alternating_seven_residual_and_hall
      h hH hgen c hKL hKT hR hY hescape C hC hKC hm⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
