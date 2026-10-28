module
public import CFSG.Quasithin.Chapter10.SourceA5PointA7Transfer
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerCompletion
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.NaturalSource
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.BlockTyping
public import Stellmacher.ElementaryAbelianMaxJFixedCenter
/-!
# The original head in the deleted-seven point action

The literal full point action gives a symmetric-seven quotient with alternating
component image. First the SQTK component theorem makes the original two-core
quotient quasisimple, retaining any possible central odd kernel. The source
Baumann equality then excludes the characteristic-subgroup alternative in
C.1.24. Its remaining block structure and the fully moved original module
identify the actual action kernel with the two-core, giving the original
alternating-seven head.

Source: Aschbacher–Smith 10.2.9, printed pp.751–753, using C.1.24.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem point_baumann_eq {v : G} (hvT : v ∈ (T : Subgroup G))
    (hv2 : v ^ 2 = 1)
    (hJP : elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
      elementaryAbelianMaxJ (T : Subgroup G)) :
    ChapterB.baumann ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
      ChapterB.baumann (T : Subgroup G) := by
  let : IsElementaryAbelian 2 (zpowers v) := IsElementaryAbelian.zpowers_of_pow_eq_one hv2
  have hvC : v ∈ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    intro j hj
    have hJle : elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) ≤
        (T : Subgroup G) ⊓ centralizer ({v} : Set G) := sSup_le fun _ hA => hA.1
    have hjP := hJle (hJP.symm ▸ hj)
    exact (mem_centralizer_singleton_iff.mp hjP.2)
  have hvZ := elementary_centralizer_maxJ_le_omegaCenter (T : Subgroup G) (zpowers v)
    (zpowers_le.mpr hvT) (zpowers_le.mpr hvC) (mem_zpowers v)
  have hBC : ChapterB.baumann (T : Subgroup G) ≤ centralizer ({v} : Set G) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr ((show b ∈ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup G)) : Set G) from hb.2) v hvZ).symm
  exact baumann_eq_of_intermediate _ _ (le_inf inf_le_left hBC) inf_le_left

private theorem no_point_characteristic
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (I H : Subgroup G) (hLI : L ≤ I) (hIH : I ≤ H) (hout : ¬ I ≤ D.maximalLocal)
    (P : Sylow 2 H)
    (hb : (ChapterB.baumann (P : Subgroup H)).map H.subtype = ChapterB.baumann (T : Subgroup G))
    (R : Subgroup (ChapterB.baumann (P : Subgroup H)))
    (hchar : R.Characteristic) (hne : R ≠ ⊥)
    (hn : (R.map (ChapterB.baumann (P : Subgroup H)).subtype).Normal) : False := by
  let B := ChapterB.baumann (P : Subgroup H)
  let B0 := ChapterB.baumann (T : Subgroup G)
  let e : B ≃* B0 := (B.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hb)
  let R0 := R.map e.toMonoidHom
  let : R0.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨(MulAut.congr e.symm a) y,
      characteristic_iff_le_comap.mp hchar (MulAut.congr e.symm a) hy, ?_⟩
    exact e.apply_symm_apply (a (e y))
  have he : R0.map B0.subtype = (R.map B.subtype).map H.subtype := by
    rw [map_map,map_map]
    rfl
  have hN : I ≤ normalizer (R0.map B0.subtype : Set G) := by
    rw [he]
    have hN := (R.map B.subtype).le_normalizer_map H.subtype
    have hn' : normalizer (R.map B.subtype : Set H) = ⊤ := @normalizer_eq_top _ _ _ hn
    rw [hn',←MonoidHom.range_eq_map,range_subtype] at hN
    exact hIH.trans hN
  have hz := source_overgroup_characteristic_baumann_eq_bot D I hLI hout R0 hN
  exact hne ((map_eq_bot_iff_of_injective R e.injective).mp hz)

/-- The full deleted action reconstructs the original head quotient through C.1.24. -/
theorem source_a5_point_deleted_quotient
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {v : G} (hv : v ∈ D.fullModule) (hvne : v ≠ 1)
    (hvL : v ∈ centralizer (L : Set G))
    (I : Subgroup G) (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hnot : ¬ IsQuasisimple I) (hout : ¬ I ≤ D.maximalLocal)
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    (hJP : elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
      elementaryAbelianMaxJ (T : Subgroup G))
    (hspan : ⁅D.fullModule,L⁆ ≤ conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I)
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)))))
    (q : (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Subgroup G) →*
      Equiv.Perm (Fin 7))
    (hq : Function.Surjective q)
    (hk : q.ker = centralizer
      (((conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)))) : Set _))
    (hIq : (I.subgroupOf (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)))).map q =
      alternatingGroup (Fin 7))
    (E :
      let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
      ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
        (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)))
      letI := hr.elementary
      Additive U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 7))
    (he :
      let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
      ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
        (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)))
      letI := hr.normal
      letI := hr.elementary
      ∀ g w, E (NormalElementaryQuotient.representation U q hq hk g w) =
        BinaryPermutation.naturalRepresentation (Fin 7) g (E w)) :
    Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) := by
  let S := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let H := I ⊔ S
  let K := I.subgroupOf H
  let V := conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (S : Set G)) I
  let U := V.subgroupOf H
  let := hr.normal
  let := hr.elementary
  have hHX : H ≤ centralizer ({v} : Set G) := sup_le hIX inf_le_right
  have hK : K.IsCComponent := hI.subgroupOf_of_le le_sup_left hHX
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hHX.trans hNI)
  let d : K ≃* I := subgroupOfEquivOfLe le_sup_left
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  have hvT : v ∈ (T : Subgroup G) := D.fullModule_le_sylow hu hv
  have hv2 : v ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian v hv
  let dQ : ActionQuotient U ≃* Equiv.Perm (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have hdQ : dQ.toMonoidHom.comp (actionMk U) = q := by
    ext x
    rfl
  have hAmap : (K.map (actionMk U)).map dQ.toMonoidHom = alternatingGroup (Fin 7) := by
    rw [map_map,hdQ]
    exact hIq
  let eA := (dQ.subgroupMap (K.map (actionMk U))).trans (MulEquiv.subgroupCongr hAmap)
  let : IsQuasisimple (I ⧸ pCore 2 I) := source_a5_point_a7_head_quasisimple D
    (orderOf_eq_prime hv2 hvne) I hIX hI hr eA
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm
  have hf := source_a5_point_component_characteristicTwo D hv hvne hvL hCW I hIX hI hnot
  have ho := source_a5_point_centralizer_oddCore_eq_bot D hv hvne hvL hCW
  have hfI : generalizedFitting I = pCore 2 I := by
    let dX := subgroupOfEquivOfLe hIX
    rcases hI.component_or_generalizedFitting_eq_pCore ho with h | h
    · let := h.2
      exact (hnot (IsQuasisimple.of_mulEquiv dX)).elim
    · have hh := congrArg (Subgroup.map dX.toMonoidHom) h
      rwa [map_generalizedFitting_equiv,pCore_map_iso] at hh
  have hfK : generalizedFitting K = pCore 2 K := by
    have hh := congrArg (Subgroup.map d.symm.toMonoidHom) hfI
    rwa [map_generalizedFitting_equiv,pCore_map_iso] at hh
  obtain ⟨P,hP⟩ := hs.restrict (show S ≤ H from le_sup_right) hHX
  have hP' : (P : Subgroup H) = S.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show S ≤ H from le_sup_right)]
  have hKP : K ⊔ (P : Subgroup H) = ⊤ := by
    rw [hP',←subgroupOf_sup (show I ≤ H from le_sup_left) (show S ≤ H from le_sup_right)]
    exact subgroupOf_self H
  have hprod : ∀ g : H, ∃ k ∈ K, ∃ t ∈ (P : Subgroup H), k*t=g := by
    intro g
    exact mem_sup_of_normal_left.mp (hKP.symm ▸ mem_top g)
  have hb : (ChapterB.baumann (P : Subgroup H)).map H.subtype = ChapterB.baumann (T : Subgroup G) := by
    have hh := baumann_map_injective H.subtype H.subtype_injective (P : Subgroup H)
    change (ChapterB.baumann (P : Subgroup H)).map H.subtype =
      ChapterB.baumann ((P : Subgroup H).map H.subtype) at hh
    rw [hP] at hh
    exact hh.trans (point_baumann_eq hvT hv2 hJP)
  have hVH : V ≤ H := (conjugateSpanBy_le_self
    (inf_le_left.trans ((source_full_moved_le_component D).trans hLI))).trans le_sup_left
  have hmV : ⁅V,I⁆ = V := (source_a5_point_action_marking D I hLI hout hCW hspan hr).1
  have hm : ⁅U,K⁆ = U := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVH,
      map_subgroupOf_eq_of_le (show I ≤ H from le_sup_left)]
    exact hmV
  have hne : U ≠ ⊥ := by
    intro hz
    have hzV : V = ⊥ := by
      have hh := congrArg (Subgroup.map H.subtype) hz
      simpa only [U,map_subgroupOf_eq_of_le hVH,Subgroup.map_bot] using hh
    exact source_full_moved_ne_bot D (le_bot_iff.mp (hspan.trans_eq hzV))
  have hc : ∀ A, fixedCodim (NormalElementaryQuotient.representation U q hq hk) A =
      fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7)) A := by
    intro A
    simpa only [map_id] using fixedCodim_map_equivariant
      (NormalElementaryQuotient.representation U q hq hk)
      (BinaryPermutation.naturalRepresentation (Fin 7)) (MonoidHom.id _) E he A
  have he' : ∀ g w, E.symm (BinaryPermutation.naturalRepresentation (Fin 7) g w) =
      NormalElementaryQuotient.representation U q hq hk g (E.symm w) := by
    intro g w
    apply E.injective
    rw [E.apply_symm_apply]
    obtain ⟨x,rfl⟩ := hq g
    have hh := (he (q x) (E.symm w)).symm
    rw [E.apply_symm_apply] at hh
    refine hh.trans (congrArg E ?_)
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    exact (NormalElementaryQuotient.representation_apply U q hq hk x (E.symm w)).symm
  have hblock : ChapterC.IsBlock K :=
    (ChapterC.RankOne.SevenSource.Natural.normal_characteristic_or_block_of_natural_seven_linear
      K U hK hf hfK P hprod q hq hk hIq hc E.symm.toLinearMap E.symm.injective he'
      (hm.symm ▸ hne)).resolve_left (by
        rintro ⟨R,hchar,hneR,hn⟩
        exact no_point_characteristic D I H hLI le_sup_left hout P hb R hchar hneR hn)
  let eqK := (ChapterC.RankOne.SevenSource.coreQuotientEquiv_of_full_moved K U hblock hne hm q hk).trans
    (MulEquiv.subgroupCongr hIq)
  exact ⟨(QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans eqK⟩

end CFSG.Quasithin.Chapter10
