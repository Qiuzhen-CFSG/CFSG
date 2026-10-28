module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.AlternatingThompson
public import Theory.Representation.BinaryAlternatingSixModels.PairedNearMaximum
public import CFSG.Quasithin.ChapterB.Section02.Thompson.NearMaximumAction
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Embedding

/-!
# Near-maximum Thompson normality in the selected alternating amalgam

Transport the original pair of natural heads through the literal full
two-core quotient of X = A join B. Its selected A₆ component is the
self-centralizing generalized Fitting subgroup. The paired-head bound now
exceeds rank plus one for every nontrivial elementary actor, including
outer actors. B.2.4 therefore puts every near-maximum elementary subgroup
of the original Sylow in O₂(X). Thompson-family heredity identifies
J₁(T) with J₁(O₂(X)), and hence X normalizes J₁(T).

The full action kernel, original five-dimensional marking and preceding
Chapter 12/13.3 hypotheses are retained. This finishes the J₁ assertion in
the selected ordinary A₆ branch of 13.4.7(1iv). Component/model selection,
the other alternatives, and both universal 13.4.7 source interfaces remain
assembly obligations; no marked-plane hypothesis is imposed on this pair.

Source: Aschbacher--Smith 13.4.7(1iv), printed pp.900--901.
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

/-- The full original two-core quotient action exceeds every nontrivial
near-maximum actor budget. -/
theorem original_pair_alternating_action_near_maximum
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
        ∀ R : Subgroup (X ⧸ pCore 2 X), IsElementaryTwo R →
          rank R + 1 < fixedCodim (Representation.NormalElementaryQuotient.representation E
            (QuotientGroup.mk' (pCore 2 X)) (QuotientGroup.mk'_surjective _) hk) R := by
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
  intro R hR
  apply paired_heads_exceed_full_near_maximum_budget τ Kb eb hc _ R hR
  intro I
  let d : C →* Kb := (q.subgroupMap K).comp j.symm.toMonoidHom
  have hd : Function.Surjective d := (q.subgroupMap_surjective K).comp j.symm.surjective
  have hdf : eb.toMonoidHom.comp d = f := by
    apply MonoidHom.ext
    intro c
    change eb (q.subgroupMap K (j.symm c)) = f c
    rw [heb,j.apply_symm_apply]
  have hdg : Kb.subtype.comp d = g := rfl
  let P := I.comap d
  have hPI : P.map d = I := map_comap_eq_self_of_surjective hd I
  have hPf : P.map f = I.map eb.toMonoidHom := by
    rw [←hdf,←map_map,hPI]
  have hPg : P.map g = I.map Kb.subtype := by
    rw [←hdg,←map_map,hPI]
  have hu := (hbudget P).1
  have ht := fixedCodim_map_equivariant ρ τ g a hact P
  rw [hPg] at ht
  rw [hPf,ht] at hu
  exact hu

/-- Every original near-maximum elementary subgroup lies in the full two-core;
J₁(T) equals J₁ of that core. -/
theorem original_pair_alternating_near_thompson_core
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
    ChapterB.thompsonJ (T : Subgroup G) 1 ≤ Q ∧
      ChapterB.thompsonJ (T : Subgroup G) 1 = ChapterB.thompsonJ Q 1 := by
  let X := A ⊔ B
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  let E := U.subgroupOf X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  let S := T.subtype hTX
  let q := QuotientGroup.mk' (pCore 2 X)
  obtain ⟨hN,he,hk,hn⟩ := original_pair_alternating_action_near_maximum h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  let := hN
  let := he
  have hES : E ≤ (S : Subgroup X) := (IsElementaryAbelian.isPGroup 2 E).le_sylow_of_normal S
  have hJ : ChapterB.thompsonJ (S : Subgroup X) 1 ≤ pCore 2 X := by
    rw [←QuotientGroup.ker_mk' (pCore 2 X)]
    apply sSup_le
    intro R hR
    apply (map_eq_bot_iff R).mp
    by_contra hneR
    let : IsElementaryAbelian 2 R := hR.2.1
    let : IsElementaryAbelian 2 (R.map q) := IsElementaryAbelian.map q
    exact (not_lt_of_ge (ChapterB.near_maximum_action_codimension
      (S : Subgroup X) E hES q (QuotientGroup.mk'_surjective _) hk hR hneR))
      (hn (R.map q) ⟨hneR,inferInstance⟩)
  have hJQ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ X.pCoreIn 2 := by
    have hm := map_mono (f := X.subtype) hJ
    rw [←ChapterB.thompsonJ_map_injective X.subtype X.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX] at hm
    exact hm
  have hQT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
    rintro x ⟨y,hy,rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal S hy
  have hJ0 := (original_pair_alternating_thompson_core h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK).1
  have hr := ChapterB.twoRank_eq_of_intermediate (T : Subgroup G) (X.pCoreIn 2) hJ0 hQT
  have hfamily : ChapterB.thompsonFamily (T : Subgroup G) 1 =
      ChapterB.thompsonFamily (X.pCoreIn 2) 1 := by
    ext R
    constructor
    · intro hR
      exact ⟨(le_sSup hR).trans hJQ,hR.2.1,hr ▸ hR.2.2⟩
    · intro hR
      exact ⟨hR.1.trans hQT,hR.2.1,hr ▸ hR.2.2⟩
  refine ⟨hJQ,?_⟩
  rw [ChapterB.thompsonJ,hfamily,ChapterB.thompsonJ]

/-- The original join normalizes J₁(T) in the selected ordinary A₆ case. -/
theorem original_pair_alternating_near_thompson_normal
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
    A ⊔ B ≤ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) := by
  let X := A ⊔ B
  obtain ⟨_,he⟩ := original_pair_alternating_near_thompson_core h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  rw [he]
  have hnorm : X ≤ normalizer (X.pCoreIn 2 : Set G) := by
    have hh := (pCore 2 X).le_normalizer_map X.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (ChapterB.thompsonJ (X.pCoreIn 2) 1).map (MulAut.conj x).toMonoidHom = _
  rw [←ChapterB.thompsonJ_map_equiv]
  exact congrArg (fun R => ChapterB.thompsonJ R 1)
    (mem_normalizer_iff_map_conj_eq.mp (hnorm hx))

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
