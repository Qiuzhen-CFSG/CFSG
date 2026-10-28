module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.SmallRadical
public import Theory.GroupAction.PerfectSmallPrimeSection
public import Theory.GroupTheory.NormalCentralQuotientAction.SolvableKernel
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Bounds

public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Full radical displacement in the small Mathieu pushing-up rows

The original intersection residual retains its marked simple quotient after
both literal maps into J₄. A prime-eleven orbit count kills its action on the
small quotient of the radical by the faithful module image. Thus the
commutator of the entire native radical with the residual image is exactly
the module image.

Pulling this equality through the original central cover gives a commutator
bound modulo the full covering center. Perfect commutator idempotence removes
that central factor. The original radical's central-product decomposition
then gives [O₂(J),(L intersect H)^infinity] = V in the ambient group.

In the M₁₂ row the residual has odd centralizer. Squares of radical elements
are fixed, so the entire radical image is elementary; J₄'s proved two-rank
bound reduces its order to at most 2048 and its index over the module to at
most two. The literal Hall application retains all witnesses, the original
strict gap and the separate factored witness. The M₁₂/M₂₂ contradictions and
SourceMathieuHallFaithfulAt remain open.

Source: Aschbacher–Smith 4.2.13 and 4.4.14, printed pp.611–612,624–625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The whole native radical has displacement exactly the original module image. -/
theorem sourceOrbit_pushingUp_small_radical_displacement
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let U := ((J.pCoreIn 2).comap j).map q
    let E := (V.comap j).map q
    let B := (F.comap j).map q
    ⁅U,B⁆ = E := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Fk := F.comap j
  let Ek := V.comap j
  let U := ((J.pCoreIn 2).comap j).map q
  let E := Ek.map q
  let B := Fk.map q
  have hj : Function.Injective j := H.subtype_injective.comp K.subtype_injective
  have hjr : j.range = K.map H.subtype := by rw [MonoidHom.range_comp,range_subtype]
  have hc := hw.2.2.2.2.2.2.1
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK := hc.ordinary_component_contains_original K hK
  let b : Fk ≃* F := (subgroupOfEquivOfLe hFK).trans (subgroupOfEquivOfLe hFH)
  let : Group.IsPerfect F := Group.IsPerfect.map _
  let : Group.IsPerfect Fk := Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective Fk)
  have hEV : Ek.map j = V := map_comap_eq_self
    ((D.sourceOrbit_pushingUp_module_disjoint_central_factor hfix hw K hK).1.trans
      inf_le_right |>.trans_eq hjr.symm)
  have hBF : Fk.map j = F := by
    apply map_comap_eq_self
    rw [hjr]
    intro f hf
    exact ⟨⟨f,hFH hf⟩,hFK hf,rfl⟩
  have hmove : ⁅E,B⁆ = E := by
    have hk : ⁅Ek,Fk⁆ = Ek := map_injective hj (by
      rw [map_commutator,hEV,hBF]
      exact hw.2.2.2.2.2.2.2.2.2.1.symm)
    rw [←map_commutator,hk]
  have hn := @sourceOrbit_pushingUp_native_radical G instG finG T L V D hfix A J H W hw K hK e
  dsimp only at hn
  have hBU : B ≤ normalizer (U : Set Janko4.Model) := hn.2.2.2.1
  have hBE : B ≤ normalizer (E : Set Janko4.Model) := hn.2.2.2.2.1
  have hEU : E ≤ U := hn.2.2.2.2.2.1
  have hcent := @sourceOrbit_pushingUp_small_radical_centralizes G instG finG T L V D
    h hV hfix hm A J H W hw K hK e
  let : (E.subgroupOf U).Normal := normal_subgroupOf_of_le_normalizer
    (hcent.trans (Subgroup.centralizer_le_normalizer _))
  have hb := @sourceOrbit_pushingUp_small_radical_bounds G instG finG T L V D
    h hV hfix A J H W hw K hK e
  let a : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L) := hn.2.2.2.2.2.2.2.2.some
  let z := (centerQuotientCongr a).trans (D.orbitCentralQuotientEquiv h)
  have hupper : ⁅U,B⁆ ≤ E := by
    have small {S : Type} [Group S] [IsSimpleGroup S]
        (em : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* S)
        (h11 : 11 ∣ Nat.card S) (hi : E.relIndex U ≤ 32) : ⁅U,B⁆ ≤ E := by
      let f := em.toMonoidHom.comp
        ((QuotientGroup.mk' (center (B ⧸ pCore 2 B))).comp (QuotientGroup.mk' (pCore 2 B)))
      let : Group.IsSolvable f.ker := by
        rw [MonoidHom.ker_comp_of_injective _ _ em.injective,
          ←MonoidHom.comap_ker,QuotientGroup.ker_mk']
        exact centralPreimage_pCore_isSolvable 2
      exact commutator_perfect_le_of_primitive_small_section (m := 5) B U E f
        (em.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)))
        (by decide : Nat.Prime 11) h11 hn.2.1.isPGroup hi
        (by rw [Representation.BinaryPrimeDegree.orderOf_two_mod_eleven]; decide) hBU hBE
    rcases hm with em | em
    · let := Sporadic.Mathieu.m12_isSimpleGroup
      exact small (z.trans em.some) (by rw [Sporadic.Mathieu.m12_order]; decide) (hb.1 em).2.1
    · let := Sporadic.Mathieu.m22_isSimpleGroup
      exact small (z.trans em.some) (by rw [Sporadic.Mathieu.m22_order]; decide)
        ((hb.2 em).2.trans (by decide))
  exact le_antisymm hupper (hmove.symm.le.trans (commutator_mono hEU le_rfl))

/-- In the M12 row the entire original radical image is elementary of order at most 2048. -/
theorem sourceOrbit_pushingUp_m12_radical_elementary
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let U := ((J.pCoreIn 2).comap j).map q
    let E := (V.comap j).map q
    IsElementaryAbelian 2 U ∧ Nat.card U ≤ 2048 ∧ E.relIndex U ≤ 2 := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let U := ((J.pCoreIn 2).comap j).map q
  let E := (V.comap j).map q
  let B := (F.comap j).map q
  have hn := @sourceOrbit_pushingUp_native_radical G instG finG T L V D hfix A J H W hw K hK e
  dsimp only at hn
  have hEU : E ≤ U := hn.2.2.2.2.2.1
  let : IsElementaryAbelian 2 E := hn.2.2.2.2.2.2.1
  have hb := @sourceOrbit_pushingUp_small_radical_bounds G instG finG T L V D
    h hV hfix A J H W hw K hK e
  have hodd := (hb.1 hm).2.2
  have hfixed : U ⊓ centralizer (B : Set Janko4.Model) = ⊥ := by
    by_contra hne
    have hp := hn.2.1.isPGroup.to_le (show U ⊓ centralizer (B : Set Janko4.Model) ≤ U from inf_le_left)
    have hd := hp.card_eq_or_dvd.resolve_left (fun hc => hne (card_eq_one.mp hc))
    exact hodd (hd.trans (card_dvd_of_le inf_le_right))
  have hcent := @sourceOrbit_pushingUp_small_radical_centralizes G instG finG T L V D
    h hV hfix (.inl hm) A J H W hw K hK e
  have hdisp := @sourceOrbit_pushingUp_small_radical_displacement G instG finG T L V D
    h hV hfix (.inl hm) A J H W hw K hK e
  let hElem : IsElementaryAbelian 2 U := elementary_of_central_binary_displacement U E B hcent hdisp.le hfixed
  let := hElem
  have hupper : Nat.card U ≤ 2048 :=
    (primeRank_le_iff_elementary_card_le Janko4.Model).mp
      Janko4.TwoRank.model_twoRank_le_eleven U hElem
  have hlower : 1024 ≤ Nat.card E := by
    rw [hn.2.2.2.2.2.2.2.1]
    let := D.elementary
    rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 2) V]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (D.sourceOrbit_mathieu_twoRank_ge_ten hV (.inl hm))
  have hcount := (E.subgroupOf U).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hEU).toEquiv] at hcount
  change Nat.card E * E.relIndex U = Nat.card U at hcount
  exact ⟨hElem,hupper,by nlinarith⟩

/-- The full original radical, before removing any covering center, has
commutator precisely V with the original intersection residual. -/
theorem sourceOrbit_pushingUp_small_radical_commutator
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    ⁅J.pCoreIn 2,(solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype⁆ = V := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := J.pCoreIn 2
  let Kg := K.map H.subtype
  let Z := (center K).map j
  let C := R ⊓ centralizer (Kg : Set G)
  have hjr : j.range = Kg := by rw [MonoidHom.range_comp,range_subtype]
  have hc := hw.2.2.2.2.2.2.1
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK' := hc.ordinary_component_contains_original K hK
  have hFK : F ≤ Kg := by
    intro f hf
    exact ⟨⟨f,hFH hf⟩,hFK' hf,rfl⟩
  have hVK := (D.sourceOrbit_pushingUp_module_disjoint_central_factor hfix hw K hK).1.trans inf_le_right
  have hFmap : (F.comap j).map j = F := map_comap_eq_self (hFK.trans_eq hjr.symm)
  have hVmap : (V.comap j).map j = V := map_comap_eq_self (hVK.trans_eq hjr.symm)
  have hRmap : (R.comap j).map j = R ⊓ Kg := by rw [map_comap_eq,hjr,inf_comm]
  have hk : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have he := @sourceOrbit_pushingUp_small_radical_displacement G instG finG T L V D
    h hV hfix hm A J H W hw K hK e
  have hpre : ⁅R ⊓ Kg,F⁆ ≤ V ⊔ Z := by
    have hh : ⁅R.comap j,F.comap j⁆ ≤ (V.comap j) ⊔ center K := by
      have hm : (⁅R.comap j,F.comap j⁆).map q ≤ (V.comap j).map q := by
        rw [map_commutator]
        exact he.le
      have hh := (map_le_iff_le_comap).mp hm
      rwa [comap_map_eq,hk] at hh
    have hh := map_mono (f := j) hh
    rwa [map_commutator,hRmap,hFmap,Subgroup.map_sup,hVmap] at hh
  have hZcentral (X : Subgroup G) (hX : X ≤ Kg) : Z ≤ centralizer (X : Set G) := by
    rintro z ⟨z,hz,rfl⟩ x hx
    obtain ⟨k,hk,rfl⟩ := hX hx
    exact congrArg j (mem_center_iff.mp hz ⟨k,hk⟩)
  have hFR : F ≤ normalizer (R : Set G) :=
    (le_conjugateSpanBy F (H ⊓ normalizer (L : Set G))).trans hc.span_normalizes_radical
  have hFV : F ≤ normalizer (V : Set G) := ((map_subtype_le _).trans inf_le_left).trans D.normalizes
  let : Group.IsPerfect F := Group.IsPerfect.map _
  have hpF : IsPPerfect 2 F := by
    intro N hN hp
    let := hN
    have hs : Subsingleton (F ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (F ⧸ N) hp.isNilpotent
    apply eq_top_iff.mpr
    intro f _
    exact (QuotientGroup.eq_one_iff f).mp (hs.elim _ _)
  have hfirst : ⁅R ⊓ Kg,F⁆ ≤ V := by
    rw [←commutator_isPPerfect_idempotent F (R ⊓ Kg) hpF
      ((isPGroup_pCoreIn 2 J).to_le inf_le_left)
      ((le_inf hFR (hFK.trans Kg.le_normalizer)).trans inf_normalizer_le_normalizer_inf)]
    exact commutator_le_of_le_sup_centralizing _ F V Z
      (hpre.trans (by rw [sup_comm])) (hZcentral V hVK) (hZcentral F hFK) hFV
  have hf := sourceOrbit_pushingUp_core_central_product hw K hK e
  have hRC : R ⊓ Kg ≤ centralizer (C : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hf.2.1
  have hCF : C ≤ centralizer (F : Set G) := inf_le_right.trans (centralizer_le hFK)
  have hupper : ⁅R,F⁆ ≤ V := by
    apply commutator_le.mpr
    intro r hr f hf'
    have hr' : r ∈ ((R ⊓ Kg : Subgroup G) : Set G) * (C : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ (hRC.trans (Subgroup.centralizer_le_normalizer _))]
      exact hf.1 ▸ hr
    obtain ⟨a,ha,c,hc,rfl⟩ := hr'
    have hcf : ⁅c,f⁆ = 1 := (show Commute c f from (hCF hc f hf').symm).commutator_eq
    rw [commutatorElement_mul_left_eq_conj_mul,hcf,mul_one,mul_inv_cancel,one_mul]
    exact hfirst (commutator_mem_commutator ha hf')
  exact le_antisymm hupper (hw.2.2.2.2.2.2.2.2.2.1.le.trans
    (commutator_mono hw.2.2.2.2.2.1 le_rfl))
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The literal Hall obstruction has full original radical commutator V.
Its native displacement uses the entire radical; in the M12 row that
radical is elementary and has index at most two over the original module. -/
theorem sourceOrbit_mathieu_hall_small_radical_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H₀ : Subgroup G} (hH : H₀ ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H₀)
    (B₀ : Subgroup H₀) (hBN : B₀ ≤ (normalizer (L : Set G)).subgroupOf H₀)
    (hHall : IsHallSubgroup oddPrimes
      (B₀.subgroupOf ((normalizer (L : Set G)).subgroupOf H₀)))
    (hker : B₀.map H₀.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H₀ ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
        Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22)) ∧
      MathieuPushingUpFactoredCase T L V A ∧
      ∃ J H W : Subgroup G, Witness L V A J H W ∧
        ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
          ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
          ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf H ≤ K ∧
          ∃ (e : (K ⧸ center K) ≃* Janko4.Model) (x : K) (r : G),
            orderOf x = 3 ∧ CubicPumpupFullResolution H K x r ∧
            ((T : Subgroup G) ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
              V ⊔ (center K).map (H.subtype.comp K.subtype) < J.pCoreIn 2 ⊓ K.map H.subtype) ∧
            ⁅J.pCoreIn 2,(solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype⁆ = V ∧
            let j := H.subtype.comp K.subtype
            let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
            let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
            let U := ((J.pCoreIn 2).comap j).map q
            let E := (V.comap j).map q
            let B := (F.comap j).map q
            q.ker ≤ (J.pCoreIn 2).comap j ∧ IsPRadical 2 U ∧
              normalizer (U : Set Janko4.Model) ≤ normalizer (B : Set Janko4.Model) ∧
              E ≤ U ∧ Nat.card E = Nat.card V ∧ U ≤ centralizer (E : Set Janko4.Model) ∧
              ⁅U,B⁆ = E ∧
              (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) →
                IsElementaryAbelian 2 U ∧ Nat.card U ≤ 2048 ∧ E.relIndex U ≤ 2 ∧
                  ¬ 2 ∣ Nat.card (centralizer (B : Set Janko4.Model))) ∧
              (Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22) →
                Nat.card U ≤ 16384 ∧ E.relIndex U ≤ 16) := by
  have hsource := @sourceOrbit_mathieu_hall_small_radical G instG finG T L V D
    h hmany hV hm hnon H₀ hH hlarge B₀ hBN hHall hker
  refine hsource.imp fun p hpA => hpA.imp fun A hA => ?_
  obtain ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,hsmall,hfact,hgap⟩ := hA
  obtain ⟨J,H,W,hw,K,hK,hn,hout,hFK,e,x,r,hx,hfull,hgap,hdata⟩ := hgap
  obtain ⟨hZ,hrad,hNB,hEU,hcard,hcent,h12,h22⟩ := hdata
  have hfix := (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1
  have hcomm := @sourceOrbit_pushingUp_small_radical_commutator G instG finG T L V D
    h.toHypothesis1221 hV hfix hsmall A J H W hw K hK e
  have hdisp := @sourceOrbit_pushingUp_small_radical_displacement G instG finG T L V D
    h.toHypothesis1221 hV hfix hsmall A J H W hw K hK e
  refine ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,hsmall,hfact,
    J,H,W,hw,K,hK,hn,hout,hFK,e,x,r,hx,hfull,hgap,hcomm,
    hZ,hrad,hNB,hEU,hcard,hcent,hdisp,?_,h22⟩
  intro hm12
  have hb := @sourceOrbit_pushingUp_m12_radical_elementary G instG finG T L V D
    h.toHypothesis1221 hV hfix hm12 A J H W hw K hK e
  exact ⟨hb.1,hb.2.1,hb.2.2,(h12 hm12).2.2⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
