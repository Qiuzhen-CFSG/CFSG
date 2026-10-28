module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.AlternatingHeadBudget
public import Theory.Representation.BinaryAlternatingSixModels.PairedNormalizer
public import Theory.Representation.NormalElementaryQuotient.Thompson
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure

/-!
# Ordinary Thompson normality in the selected alternating amalgam

The original two fixed-line orbit groups supply both inequivalent natural
A₆ quotient maps. Their additive displacement bound holds on the whole
omega span. Pass through the literal two-core quotient of the original
join: its selected component is A₆ and is the generalized Fitting subgroup,
so it is self-centralizing. The paired movement obstruction excludes every
FF offender in the full quotient, including actors outside the component.

B.2.4 then puts every maximum elementary subgroup of the original Sylow
in the two-core. Thompson heredity gives J(T)=J(O₂(A join B)) and normality
in A join B. All quotient maps, their entire kernels and the original
relative-centralizer/prime-to-three residual premise are retained.

This establishes the ordinary Thompson step under the selected A₆ case.
It does not select that case or establish J₁(T) normality. The two universal
13.4.7 interfaces and the other model branches remain source obligations.
Source: Aschbacher--Smith 13.4.7, printed pp.900--901.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Theory.SpecificGroups.SymmetricSix BinaryDuadModule BinaryAlternatingSix
open Representation Representation.BinaryOffender
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The full original two-core quotient action has no FF offender. -/
theorem original_pair_alternating_action_nonFF
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      A6) :
    let X := A ⊔ B
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    let E := U.subgroupOf X
    ∃ hN : E.Normal, ∃ he : IsElementaryAbelian 2 E,
      let := hN
      let := he
      ∃ hk : (QuotientGroup.mk' (pCore 2 X)).ker = centralizer (E : Set X),
        ¬ IsFFModule (Representation.NormalElementaryQuotient.representation E
          (QuotientGroup.mk' (pCore 2 X)) (QuotientGroup.mk'_surjective _) hk) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  let E := U.subgroupOf X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hUX : U ≤ X := conjugateSpanBy_le (fun z hz =>
    hTX ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hred := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  let : E.Normal := hred.normal
  let : IsElementaryAbelian 2 E := hred.elementary
  obtain ⟨heU,e,_,hbudget⟩ := original_pair_alternating_paired_budget h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  let := heU
  let ρ := Representation.elementaryRepresentation (p := 2)
    (U.normalizerMonoidHom.comp (inclusion
      ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X))))
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hns : ¬ Group.IsSolvable X := by
    intro hh
    let := hh
    exact hK.not_isSolvable inferInstance
  have hfull := original_pair_full_action_kernel h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB hres hns
  have hcent : centralizer (E : Set X) = pCore 2 X := by
    apply map_injective X.subtype_injective
    have hh := map_inf_centralizer_of_injective X.subtype X.subtype_injective
      (⊤ : Subgroup X) E
    have heq : (centralizer (E : Set X)).map X.subtype = X ⊓ centralizer (U : Set G) := by
      simpa only [top_inf_eq,←MonoidHom.range_eq_map,range_subtype,
        E,map_subgroupOf_eq_of_le hUX] using hh.symm
    exact heq.trans hfull
  let q := QuotientGroup.mk' (pCore 2 X)
  have hk : q.ker = centralizer (E : Set X) := (QuotientGroup.ker_mk' _).trans hcent.symm
  let τ := Representation.NormalElementaryQuotient.representation E q
    (QuotientGroup.mk'_surjective _) hk
  let Kb := K.map q
  obtain ⟨_,hcomp,hKb,⟨eqK,heqK⟩,_,hfit⟩ := original_pair_component_twoCore_image h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  change generalizedFitting (X ⧸ pCore 2 X) = Kb at hfit
  let : Kb.Normal := hKb
  let j : K ≃* C := K.equivMapOfInjective X.subtype X.subtype_injective
  let jq := QuotientGroup.congr (pCore 2 K) (pCore 2 C) j (pCore_map_iso 2 j)
  let eb : Kb ≃* A6 := (eqK.symm.trans jq).trans e
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup Kb := eb.isSimpleGroup
  have hc : centralizer (Kb : Set (X ⧸ pCore 2 X)) = ⊥ := by
    let : IsSimpleGroup (generalizedFitting (X ⧸ pCore 2 X)) := hfit.symm ▸ inferInstance
    let : IsQuasisimple Kb := hcomp.2
    have hnon : ¬ IsMulCommutative (generalizedFitting (X ⧸ pCore 2 X)) := by
      rw [hfit]
      exact Group.IsPerfect.not_isMulCommutative Kb
    simpa only [hfit] using (SimpleSocle.centralizer_eq_bot hnon)
  let a : Additive U ≃ₗ[ZMod 2] Additive E :=
    LinearEquiv.ofBijective
      ((subgroupOfEquivOfLe hUX).symm.toMonoidHom.toAdditive.toZModLinearMap 2)
      (subgroupOfEquivOfLe hUX).symm.bijective
  let g : C →* (X ⧸ pCore 2 X) := (q.comp K.subtype).comp j.symm.toMonoidHom
  have hact (c : C) (v : Additive U) : a (ρ c v) = τ (g c) (a v) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    have hh := Representation.NormalElementaryQuotient.representation_apply E q
      (QuotientGroup.mk'_surjective _) hk (j.symm c).val (a v)
    apply Subtype.ext
    have hjc : ((j.symm c).val : G) = c.val :=
      congrArg Subtype.val (j.apply_symm_apply c)
    have hh' := (congrArg (fun x : X => x.val) hh).symm
    change ((j.symm c).val : G) * v.toMul.val * ((j.symm c).val : G)⁻¹ = _ at hh'
    change c.val * v.toMul.val * c.val⁻¹ = _
    rw [hjc] at hh'
    exact hh'
  have heb (k : K) : eb (q.subgroupMap K k) = f (j k) := by
    change e (jq (eqK.symm (q.subgroupMap K k))) = _
    rw [←heqK k,eqK.symm_apply_apply]
    rfl
  refine ⟨inferInstance,inferInstance,hk,?_⟩
  apply not_ff_of_component_movement τ Kb eb hc
  intro b hb
  obtain ⟨x,hx,hxb⟩ := b.property
  let k : K := ⟨x,hx⟩
  have heqb : q.subgroupMap K k = b := Subtype.ext hxb
  have hfc : f (j k) ≠ 1 := by
    rw [←heb,heqb]
    exact fun he => hb (eb.injective (he.trans (map_one _).symm))
  have hl := paired_natural_movement (f (j k)) hfc
  have hu := (hbudget (zpowers (j k))).1
  rw [MonoidHom.map_zpowers] at hu
  have ht := fixedCodim_map_equivariant ρ τ g a hact (zpowers (j k))
  rw [MonoidHom.map_zpowers] at ht
  have hg : g (j k) = b.val := by
    change q ((j.symm (j k)).val) = _
    rw [j.symm_apply_apply]
    exact hxb
  rw [hg] at ht
  change fixedCodim firstAlternating (zpowers (f (j k))) +
    fixedCodim secondAlternating (zpowers (f (j k))) ≤ fixedCodim ρ (zpowers (j k)) at hu
  omega

/-- The original ordinary Thompson subgroup lies in the actual two-core
and equals the Thompson subgroup of that core. -/
theorem original_pair_alternating_thompson_core
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      A6) :
    let Q := (A ⊔ B).pCoreIn 2
    elementaryAbelianMaxJ (T : Subgroup G) ≤ Q ∧
      elementaryAbelianMaxJ (T : Subgroup G) = elementaryAbelianMaxJ Q := by
  let X := A ⊔ B
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  let E := U.subgroupOf X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  let S := T.subtype hTX
  let q := QuotientGroup.mk' (pCore 2 X)
  obtain ⟨hN,he,hk,hn⟩ := original_pair_alternating_action_nonFF h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  let := hN
  let := he
  have hES : E ≤ (S : Subgroup X) := (IsElementaryAbelian.isPGroup 2 E).le_sylow_of_normal S
  have hJ : elementaryAbelianMaxJ (S : Subgroup X) ≤ pCore 2 X := by
    rw [←QuotientGroup.ker_mk' (pCore 2 X)]
    apply sSup_le
    intro R hR
    apply (map_eq_bot_iff R).mp
    by_contra hneR
    exact hn ⟨R.map q,(Representation.NormalElementaryQuotient.maxElementary_isBestOffender
      E q (QuotientGroup.mk'_surjective _) hk (S : Subgroup X) R hES hR hneR).isOffender _⟩
  have hJQ : elementaryAbelianMaxJ (T : Subgroup G) ≤ X.pCoreIn 2 := by
    have hm := map_mono (f := X.subtype) hJ
    rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX] at hm
    exact hm
  have hQT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
    rintro x ⟨y,hy,rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal S hy
  exact ⟨hJQ,(elementaryAbelianMaxJ_eq_of_intermediate _ _ hJQ hQT).symm⟩

/-- The original join normalizes J(T) in the selected ordinary A₆ case. -/
theorem original_pair_alternating_thompson_normal
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      A6) :
    A ⊔ B ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let X := A ⊔ B
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  let E := U.subgroupOf X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  let S := T.subtype hTX
  obtain ⟨hN,he,hk,hn⟩ := original_pair_alternating_action_nonFF h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  let := hN
  let := he
  have hES : E ≤ (S : Subgroup X) := (IsElementaryAbelian.isPGroup 2 E).le_sylow_of_normal S
  have hk2 : IsPGroup 2 (QuotientGroup.mk' (pCore 2 X)).ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let hnormal := Representation.NormalElementaryQuotient.thompson_normal_of_nonFF
    S E (QuotientGroup.mk' (pCore 2 X)) (QuotientGroup.mk'_surjective _) hk hk2 hES hn
  let := hnormal
  have hnorm := (elementaryAbelianMaxJ (S : Subgroup X)).le_normalizer_map X.subtype
  rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,
    ←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX] at hnorm
  exact hnorm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
