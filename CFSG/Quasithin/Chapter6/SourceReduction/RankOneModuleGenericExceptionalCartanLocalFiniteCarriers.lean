module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalQuadratic
public import CFSG.Quasithin.ChapterF.Section01.RankOneMathieuEleven
public import CFSG.Quasithin.ChapterF.Section01.RankOneBinaryLinear
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryIntrinsicQuotients
public import Theory.Mathieu.M12.SylowOvergroups.Solvable
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicFiniteContainers

/-!
# Finite containing carriers in the original Cartan escape

For PSL₄(2), PSL₅(2) and M₁₁, the containing order is prime to 25.
The original seed therefore equals the residual. The genuine E.2.2
alternatives and order divisibility force its intrinsic two-core quotient
to be a source rank-one model: normality removes the exchanged row,
Cartan escape removes PSL₃(4), and divisibility removes the other diagram
rows. No residual model or trivial quotient kernel is assumed.

In the two higher binary-linear carriers, the actual local embedding
forces this same intrinsic quotient to be GLₘ(2), m ≥ 3, contradicting
the rank-one model. The exceptional isomorphism also removes A₈.
In M₁₁, retain the two-group kernel and restrict the original full Sylow
to the containing image; the native M₁₁ rank-one exclusion applies.
M₁₂ has only solvable proper full-Sylow overgroups and is excluded directly.

All five exclusions are applied to the same selected container, retaining
both Hall subgroups, every previous exclusion, the A.3.6 alternatives and
the complete binary-triality endpoint. Other simple carriers, nonquasisimple
alternatives and binary-triality exclusion remain with the source assembly.
The internal import reuses this proof family's private finite-order lemmas.
Source: Aschbacher--Smith A.3.12, E.2.2 and 5.1.12--13, printed
pp.47--48,215--216,635--638, refs/quasithin.pdf. The exceptional
isomorphism uses the attributed ATLAS port under LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G]

private theorem residual_rankOne_of_order
    {T : Sylow 2 G} {L W H A Y : Subgroup G} {n m : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hR : (pResidual 2 H).IsCComponent)
    (hm : m = 20160 ∨ m = 9999360 ∨ m = 7920)
    (hd : Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ∣ m) :
    ChapterF.Source.IsRankOneModel ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
  rcases Global.right_source_cases h.qtke h.sylow_normalizes hH hgen with hs | hs
  · obtain ⟨K,f,hK,hqs,_,_,hc | hc⟩ := hs
    · have hKR : K = pResidual 2 H := by
        apply hK.eq_of_le hR
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
  · obtain ⟨K,f,hK,hqs,_,hf,hc,hdia⟩ := hs
    have hmodels := Prime.diagram_source_residual_quotient h.sylow_normalizes hH.1.1.2 hK hqs hc hf hdia
    have hf2 := Prime.diagram_finite_order hf (by
        rcases hm with rfl | rfl | rfl <;> simp [Prime.finiteOrders]) hd hmodels
    subst f
    rcases hmodels with hlin | hsl | hsp
    · exact (not_linear_four_residual_of_escape h.qtke h.sylow_normalizes hH hY hescape hlin).elim
    · obtain ⟨F,_,_,hF,⟨a⟩⟩ := hsl
      rw [Nat.card_congr a.toEquiv,
        Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF] at hd
      rcases hm with rfl | rfl | rfl <;> norm_num at hd
    · obtain ⟨F,_,_,hF,⟨a⟩⟩ := hsp
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
        (by simpa only [Nat.card_eq_fintype_card] using hF)
      let b := a.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
      rw [Nat.card_congr b.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF] at hd
      rcases hm with rfl | rfl | rfl <;> norm_num at hd

private theorem finite_container_residual
    {T : Sylow 2 G} {L W H A K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nat.card (C ⧸ pCore 2 C) = 20160 ∨
      Nat.card (C ⧸ pCore 2 C) = 9999360 ∨ Nat.card (C ⧸ pCore 2 C) = 7920) :
    K = residual H ∧
      ChapterF.Source.IsRankOneModel ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
  have he : K = residual H := by
    apply seed_eq_residual_of_normal_twentyFive_free_container h.qtke hKL hKT horbit
      hY hescape C hKC
    rcases hm with hm | hm | hm <;> rw [hm] <;> norm_num
  have hR : (pResidual 2 H).IsCComponent := by
    have hh := (he ▸ hKL).1
    rw [residual_sup_sylow T H hH.1.1.2] at hh
    simpa only [residual,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hh
  refine ⟨he,residual_rankOne_of_order h hH hgen hY hescape hR hm ?_⟩
  have hd := Prime.original_residual_card_dvd_common_image (map_subtype_le C) (he ▸ hKC)
  simp only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] at hd
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  rwa [←Nat.card_congr (cComponentTwoCoreQuotientEquiv hC).toEquiv] at hd

/-- Neither higher binary-linear containing row can occur for the original
escaping seed. The rank-one residual is derived from the original E.2.2 data. -/
theorem not_higher_binary_container
    {T : Sylow 2 G} {L W H A K Y : Subgroup G} {n k : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype) (hk : k = 4 ∨ k = 5) :
    ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) k 2 := by
  intro hm
  have hc := Prime.binary_linear_card hk hm
  obtain ⟨he,hrank⟩ := finite_container_residual h hH hgen hKL hKT horbit
    hY hescape C hC hKC (hc.imp_right Or.inl)
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let a := (e.trans (Atlas.fieldEquivPSL k f)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < k))
  have hKY : K ≤ Y := (show K ≤ H by rw [←hKT]; exact le_sup_left).trans hY.2
  have hTY := hH.1.1.2.trans hY.2
  let S := T.subtype hTY
  have hl : K.subgroupOf Y ∈ ChapterA.Section03.localCComponents S :=
    ((Chapter1.mem_LIn_iff_subgroupOf hTY hKY).mp ⟨hKY,hKL⟩).1
  have hKC' : K.subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hKC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  obtain ⟨m,hm,_,⟨b⟩⟩ :=
    ChapterA.Section03.SourceEmbeddings.BinaryIntrinsic.local_twoCore_quotient_of_containing_quotient
      S hl (ChapterA.Section03.isCComponent_mem_localCComponents hC) hKC' k (by omega) a
  let e₀ := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let e₁ := e₀.trans ((MulEquiv.subgroupCongr he).symm.trans (subgroupOfEquivOfLe hKY).symm)
  let eR := QuotientGroup.congr _ _ e₁ (pCore_map_iso 2 e₁)
  exact hrank.not_binary_linear hm (eR.trans b)

/-- The two binary-linear rows and their literal alternating-eight model are excluded together. -/
theorem not_higher_binary_or_eight_container
    {T : Sylow 2 G} {L W H A K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype) :
    ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 4 2 ∨
      ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 5 2 ∨ IsAlternating (C ⧸ pCore 2 C) 8) := by
  rintro (hm | hm | ⟨e⟩)
  · exact not_higher_binary_container h hH hgen hKL hKT horbit hY hescape C hC hKC (.inl rfl) hm
  · exact not_higher_binary_container h hH hgen hKL hKT horbit hY hescape C hC hKC (.inr rfl) hm
  · exact not_higher_binary_container h hH hgen hKL hKT horbit hY hescape C hC hKC (.inl rfl)
      ⟨ZMod 2,inferInstance,inferInstance,by simp,
        ⟨e.some.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩

/-- The full original escaping branch excludes the M₁₁ carrier, without an
assumed residual model or a trivial kernel for the original quotient map. -/
theorem not_mathieu_eleven_container
    {T : Sylow 2 G} {L W H A K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M11) := by
  intro hm
  obtain ⟨he,hrank⟩ := finite_container_residual h hH hgen hKL hKT horbit
    hY hescape C hC hKC (Or.inr (Or.inr (by
      rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m11_order])))
  subst K
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hTY := hH.1.1.2.trans hY.2
  let q := QuotientGroup.mk' (pCore 2 Y)
  let S := T.subtype hTY
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let Rbar := ((residual H).subgroupOf Y).map q
  let Cbar := C.map q
  have hl : (residual H).subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTY hRY).mp ⟨hRY,hKL⟩
  have hlq : Rbar ∈ ChapterA.Section03.localCComponents P :=
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hl
  have hRC' : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hKC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hle : Rbar ≤ Cbar := map_mono hRC'
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  obtain ⟨Q,hQ,hU⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    P hlq hle (hC.map_quotient (pCore 2 Y)).subnormal
  let U := Rbar.subgroupOf Cbar
  have hn : (P : Subgroup (Y ⧸ pCore 2 Y)) ≤ normalizer (Rbar : Set _) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRY]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_residual H))
  have hnU : (Q : Subgroup Cbar) ≤ normalizer (U : Set Cbar) := by
    rw [hQ,←subgroupOf_normalizer_eq hle]
    exact comap_mono hn
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
  let e := eC.trans hm.some
  let V := U.map e.toMonoidHom
  let b : U ≃* V := e.subgroupMap U
  let eV := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let : Group.IsPerfect ((residual H).subgroupOf Y) := Chapter1.mem_L_isPerfect hl
  let : Group.IsPerfect Rbar := Group.IsPerfect.map _
  let : Group.IsPerfect U := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hle).symm.toMonoidHom) (subgroupOfEquivOfLe hle).symm.surjective
  let : Group.IsPerfect V := Group.IsPerfect.map _
  have hns : ¬ Group.IsSolvable V := by
    intro hs
    let : Group.IsSolvable V := hs
    let : Group.IsSolvable U := Group.isSolvable_of_isSolvable_injective
      (f := b.toMonoidHom) b.injective
    exact hU.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show U ≤ U ⊔ (Q : Subgroup Cbar) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).injective)
  exact ChapterF.Source.MathieuEleven.not_rankOne_quotient
    (Q.mapSurjective (f := e.toMonoidHom) e.surjective) V hns
    ((map_mono hnU).trans (le_normalizer_map e.toMonoidHom))
    (hrank.of_equiv (eR.trans eV).symm)

/-- The original proper seed cannot lie in an M₁₂ containing component. -/
theorem not_mathieu_twelve_container
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M12) := by
  rintro ⟨e⟩
  exact not_solvableSylow_container hG hKH hTH hK horbit hY hescape C hC hKC
    (SolvableSylowOvergroups.of_equiv e
      Sporadic.Mathieu.M12SmallPair.SylowOvergroups.isSolvable_of_ne_top)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The original same-container reduction also excludes the higher binary-linear,
alternating-eight and small Mathieu carriers, retaining the full binary endpoint. -/
theorem localCartan_escape_seed_finiteCarriers_reduction
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
        (∀ p e : ℕ, p.Prime → Odd p → (e = 1 ∨ e = 2) →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 (p ^ e)) ∧
        ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 4 2 ∨
          ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 5 2 ∨ IsAlternating (C ⧸ pCore 2 C) 8) ∧
        ¬ (Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M11) ∨
          Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M12)) ∧
        let I := C.map (QuotientGroup.mk' (pCore 2 Y))
        Chapter1.Section02.A36Common I ∧
          ((IsSimpleGroup I ∧ TheoremCModel I) ∨
            Chapter1.Section02.A36Natural I ∨ Chapter1.Section02.A36Nilpotent I) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,
    hprime,h25,hCn,hJ,hOdd,hJ4,hM22,hM23,hOddLinear,hstructure⟩ :=
    localCartan_escape_seed_oddLinear_reduction h hH hgen c hY hescape
  let := hCn
  exact ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,
    hprime,h25,hCn,hJ,hOdd,hJ4,hM22,hM23,hOddLinear,
    LocalSieve.not_higher_binary_or_eight_container h hH hgen hKL hKT hR
      hY hescape C hC hKC,
    fun hm => hm.elim
      (LocalSieve.not_mathieu_eleven_container h hH hgen hKL hKT hR hY hescape C hC hKC)
      (LocalSieve.not_mathieu_twelve_container h.qtke hKH hH.1.1.2 hKL hR hY hescape C hC hKC),
    hstructure⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
