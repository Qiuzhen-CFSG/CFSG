module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.SolvableSeed

/-!
# The original Goldschmidt contradiction at G,T

Construct the shifted normal closure and both actual S3 vertices. Their
action on the original orbit has a two-group kernel and distinct cores.
F.6.11 and F.6.18 identify the faithful action quotient as L3(2), retaining
its 3-prime core and residual. The compatible parabolic markings let H.5.5
give an orbit of order eight; the original tilded action forces larger
order. This proves centerlessness in the solvable alternative.
Source: Aschbacher--Smith 14.3.31, p.1003, F.6.11, F.6.18 and H.5.5.

The universal APIs are preserved. The proofs below specialize their
source arguments without promoting a local earlier implication to a
universal statement. This extension remains above Section04.
-/

public noncomputable section

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableShiftedRow.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne
omit d earlier hq chosen structural alternatives hne in
private theorem solvableShiftedRow_shifted_normal_closure_image_at
    (g : G) (hgH : conjugate F.ZU g ≤ F.H) (row : SolvableSeedRow F L g)
    (a : F.H) (ha : (a:G) ∈ conjugate F.ZU g) (ha2 : a^2=1)
    (haf : F.uhatAction a ≠ 1) :
    (conjugateSpanBy (zpowers a) ⊤).map (QuotientGroup.mk' F.uhatAction.ker) =
      (solvableSeedActor F g).map (QuotientGroup.mk' F.uhatAction.ker) := by
  let q := QuotientGroup.mk' F.uhatAction.ker
  let A := dotImage F F.uhatAction (conjugate F.ZU g)
  have hqa : q a ≠ 1 := fun hh => haf ((QuotientGroup.eq_one_iff a).mp hh)
  have hca : Nat.card (zpowers (q a)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [←map_pow,ha2,map_one]) hqa
  have hA : zpowers (q a) = A := eq_of_le_of_card_ge
    (zpowers_le.mpr (mem_map_of_mem q ha)) (by rw [hca]; exact row.marked_order.le)
  have hK : solvableSeedActor F g =
      conjugateSpanBy ((conjugate F.ZU g).subgroupOf F.H) ⊤ := by
    apply map_injective F.H.subtype_injective
    rw [show (solvableSeedActor F g).map F.H.subtype = conjugateSpanBy (conjugate F.ZU g) F.H from
      map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hgH),
      map_conjugateSpanBy,map_subgroupOf_eq_of_le hgH,←MonoidHom.range_eq_map,range_subtype]
  rw [hK,map_conjugateSpanBy,map_conjugateSpanBy,MonoidHom.map_zpowers,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective _),hA]
  rfl
theorem source_shifted_solvable_actor_at
    [IsElementaryAbelian 2 F.Uhat]
    (g : G) (hgP : g ∈ F.P L) (row : SolvableSeedRow F L g)
    (a : F.H) (ha : (a:G) ∈ conjugate F.ZU g) (ha2 : a^2=1)
    (haf : F.uhatAction a ≠ 1)
    (haZ : (a:G) ∈ centralizer (F.ZU : Set G)) :
    let K := conjugateSpanBy (zpowers a) (⊤ : Subgroup F.H)
    (F.uhatAction.comp K.subtype).ker = pCore 2 K ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) ∧
      ¬ K.map F.H.subtype ≤ normalizer (L : Set G) := by
  let K := conjugateSpanBy (zpowers a) (⊤ : Subgroup F.H)
  let : K.Normal := normalizer_eq_top_iff.mp
    (top_unique (le_normalizer_conjugateSpanBy _ _))
  let q := QuotientGroup.mk' F.uhatAction.ker
  have hgH : conjugate F.ZU g ≤ F.H := fun x hx =>
    (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP ⟨x,hx⟩).property
  have hm := solvableShiftedRow_shifted_normal_closure_image_at F g hgH row a ha ha2 haf
  change K.map q = (solvableSeedActor F g).map q at hm
  obtain ⟨e⟩ := row.model
  let eK : K.map q ≃* Equiv.Perm (Fin 3) := (MulEquiv.subgroupCongr hm).trans e
  let f := eK.toMonoidHom.comp (q.subgroupMap K)
  have hf : Function.Surjective f := eK.surjective.comp (q.subgroupMap_surjective K)
  have hKC : K ≤ (centralizer (F.ZU : Set G)).subgroupOf F.H := by
    apply conjugateSpanBy_le (zpowers_le.mpr (show a ∈ (centralizer (F.ZU : Set G)).subgroupOf F.H from haZ))
    have hn : ((centralizer (F.ZU : Set G)).subgroupOf F.H).Normal :=
      normal_subgroupOf_of_le_normalizer
        (F.H_normalizes_ZU.trans (normalizer_le_normalizer_centralizer F.ZU))
    let := hn
    rw [normalizer_eq_top]
  have hfk : f.ker = (F.uhatAction.comp K.subtype).ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,ker_subgroupMap]
    ext x
    exact QuotientGroup.eq_one_iff _
  have hp : IsPGroup 2 f.ker := by
    apply (pCore_isPGroup.comap_subtype : IsPGroup 2 ((pCore 2 F.H).subgroupOf K)).to_le
    intro x hx
    apply source_center_centralizing_kernel_le_core_at d earlier hq chosen structural alternatives F hne
    exact ⟨hKC x.property,(show x ∈ (F.uhatAction.comp K.subtype).ker from hfk ▸ hx)⟩
  have hk := ker_eq_twoCore_of_surjective_perm_three f hf hp
  refine ⟨hfk.symm.trans hk,⟨(QuotientGroup.quotientMulEquivOfEq hk).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩,?_⟩
  intro hKM
  apply source_dotted_intersection_ne_top_at d earlier hq chosen structural alternatives F hne
  apply top_unique
  change (⊤ : Subgroup (Hdot F F.uhatAction)) ≤ dotImage F F.uhatAction (F.H ⊓ normalizer (L:Set G))
  rw [←row.supplement]
  apply sup_le (sup_le ?_ ?_) ?_
  · rw [←hm]
    apply map_mono
    intro x hx
    exact ⟨x.property,hKM (mem_map_of_mem F.H.subtype hx)⟩
  · exact map_mono (comap_mono (le_inf ((F.Li_le L 1).trans inf_le_right)
      ((F.Li_le L 1).trans (inf_le_left.trans L.le_normalizer))))
  · exact map_mono (comap_mono (le_inf (F.invariant 1)
      ((SourceAssembly.At.higherRankHypothesis d earlier hq chosen).sylow_normalizes_at structural)))
omit d earlier hq chosen structural alternatives hne in
private theorem solvableShiftedRow_normal_s3_sylow_join_at (K : Subgroup G)
    (hKN : F.H ≤ normalizer (K : Set G))
    (model : Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3))) :
    Nonempty (((K ⊔ (T:Subgroup G) : Subgroup G) ⧸ pCore 2 (K ⊔ (T:Subgroup G):Subgroup G)) ≃*
      Equiv.Perm (Fin 3)) := by
  let A := K ⊔ (T:Subgroup G)
  let N := K.subgroupOf A
  let P := (T:Subgroup G).subgroupOf A
  have hNA : A ≤ normalizer (K : Set G) := sup_le K.le_normalizer ((F.invariant 1).trans hKN)
  let : N.Normal := normal_subgroupOf_of_le_normalizer hNA
  obtain ⟨e⟩ := model
  let en : N ≃* K := subgroupOfEquivOfLe le_sup_left
  let eqv := (QuotientGroup.congr _ _ en (pCore_map_iso 2 en)).trans e
  apply NormalSymmetricThree.quotient_symmetricThree_of_normal_twoGroup_supplement N P eqv
    T.isPGroup'.comap_subtype
  rw [←subgroupOf_sup (show K ≤ A from le_sup_left) (show (T:Subgroup G) ≤ A from le_sup_right)]
  exact subgroupOf_self _
theorem source_contrary_thompson_escape_at
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥)
    (K : Subgroup G) (hout : ¬ K ≤ normalizer (L : Set G)) :
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      (K ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      (F.I₂ L ⊔ (T : Subgroup G)).pCoreIn 2 ≠ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)
  let A := K ⊔ (T : Subgroup G)
  have hJT : J ≤ (T : Subgroup G) := sSup_le fun _ hA => hA.1
  have hJne : J ≠ ⊥ := Stellmacher.elementaryAbelianMaxJ_ne_bot_of_finite_pGroup
    (T : Subgroup G) T.isPGroup' (fun hT => chosen.ne_bot (bot_unique (hT ▸ chosen.le_sylow)))
  have hJn := source_contrary_thompson_normal_at d earlier hq chosen structural alternatives F hne hseed hI
  have hNJ : normalizer (J : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
    · intro N hN hLN
      exact Set.mem_singleton_iff.mp
        (((SourceAssembly.At.higherRankHypothesis d earlier hq chosen).maximal_unique_at structural).2 ▸
          show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
            from ⟨hN,hLN⟩)
    · exact T.isPGroup'.to_le hJT
    · exact hJne
    · exact (normal_subgroupOf_iff_le_normalizer (hJT.trans le_sup_right)).mp hJn
  have hAQ : A ≤ normalizer (A.pCoreIn 2 : Set G) :=
    A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hQT : A.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 A).le_sylow_of_normalized T (le_sup_right.trans hAQ)
  have hnot : ¬ J ≤ A.pCoreIn 2 := by
    intro hJQ
    have hJQeq := Stellmacher.elementaryAbelianMaxJ_eq_of_intermediate_finite
      (T : Subgroup G) (A.pCoreIn 2) hJQ hQT
    apply hout
    apply le_sup_left.trans (hAQ.trans (?_ : normalizer (A.pCoreIn 2 : Set G) ≤ normalizer (L : Set G)))
    have hnorm := Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ (A.pCoreIn 2)
    rw [hJQeq] at hnorm
    exact hnorm.trans hNJ
  exact ⟨hnot,fun heq => hnot (heq ▸
    source_contrary_thompson_le_plane_core_at d earlier hq chosen structural alternatives F hne hseed hI)⟩
theorem source_solvable_shifted_quotients_at
    (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ g l e : G, g ∈ F.P L ∧ g ∉ F.H ∧ l ∈ L ∧
      orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧ e ∈ sylowOmega T ∧
      let a := l⁻¹*e*l
      let K := conjugateSpanBy (zpowers a) F.H
      orderOf a = 2 ∧ K ≤ F.H ∧ F.H ≤ normalizer (K : Set G) ∧
      K ≤ centralizer (F.ZU : Set G) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (((K ⊔ (T:Subgroup G) : Subgroup G) ⧸ pCore 2 (K ⊔ (T:Subgroup G):Subgroup G)) ≃*
        Equiv.Perm (Fin 3)) ∧
      ¬ K ≤ normalizer (L : Set G) ∧
      amalgamGroup F L K ≤ centralizer ({e} : Set G) ∧
      IsPReduced 2 ((amalgamModule F L K).subgroupOf (amalgamGroup F L K)) ∧
      pCore 2 (AmalgamQuotient F L K) = ⊥ ∧
      ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      (F.I₂ L ⊔ (T : Subgroup G)).pCoreIn 2 ≠ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hseed := source_seed_exclusion_of_solvable_model_at d earlier hq chosen structural alternatives F hne model
  obtain ⟨g,l,e,hgL,hgP,hgH,hlL,hl,hspace,hgen,he,heI,heT,heU,heV,
    haH,ha,hfaith,_,hNC,hKe,hr,hcore⟩ :=
    source_shifted_amalgam_faithful_at d earlier hq chosen structural alternatives F hne hseed hI
  let a : F.H := ⟨l⁻¹*e*l,haH⟩
  let N := conjugateSpanBy (zpowers a) (⊤ : Subgroup F.H)
  let K := conjugateSpanBy (zpowers (a:G)) F.H
  have hm : N.map F.H.subtype = K := by
    rw [map_conjugateSpanBy,MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype]
    rfl
  have haI : (a:G) ∈ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) := by
    rw [centerIn_conjugate]
    simpa only [a,conjugate,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using
      mem_map_of_mem (MulAut.conj l⁻¹).toMonoidHom heI
  have hag : (a:G) ∈ conjugate F.ZU g :=
    (source_shifted_center_intersection_at d earlier hq chosen structural alternatives F hne
      g hgP hgH l hl ▸ haI).1
  let := chosen.elementary
  obtain ⟨htwo,hphi,_⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  have row := source_solvable_seed_row_at d earlier hq chosen structural alternatives F hne hZ model g hgP hgH
  obtain ⟨_,hN,hout⟩ := source_shifted_solvable_actor_at d earlier hq chosen structural alternatives F hne
    g hgP row a hag (Subtype.ext (ha ▸ pow_orderOf_eq_one (a:G))) hfaith
    (hNC (le_conjugateSpanBy _ _ (mem_zpowers _)))
  obtain ⟨eN⟩ := hN
  let en : N ≃* K := (N.equivMapOfInjective F.H.subtype F.H.subtype_injective).trans
    (MulEquiv.subgroupCongr hm)
  have hk : Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) :=
    ⟨(QuotientGroup.congr _ _ en (pCore_map_iso 2 en)).symm.trans eN⟩
  have hKH : K ≤ F.H := conjugateSpanBy_le_self (zpowers_le.mpr haH)
  have hKN : F.H ≤ normalizer (K:Set G) := le_normalizer_conjugateSpanBy _ _
  refine ⟨g,l,e,hgP,hgH,hlL,he,heI,heT,ha,hKH,hKN,hNC,hk,
    solvableShiftedRow_normal_s3_sylow_join_at F K hKN hk,?_,hKe,hr,hcore,?_⟩
  · change ¬ N.map F.H.subtype ≤ normalizer (L:Set G) at hout
    rwa [hm] at hout
  · apply source_contrary_thompson_escape_at d earlier hq chosen structural alternatives F hne hseed hI K
    change ¬ N.map F.H.subtype ≤ normalizer (L:Set G) at hout
    rwa [hm] at hout
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableAmalgam.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne
omit alternatives hne in
theorem source_parabolic_quotient_and_intersection_at :
    Nonempty ((F.P L ⧸ pCore 2 (F.P L)) ≃* Equiv.Perm (Fin 3)) ∧
      F.P L ⊓ F.H = (T : Subgroup G) := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  let f := F.binaryPermutationAction (by decide) L chosen.normalizes
  have hf : Function.Surjective f := F.binaryPermutationAction_surjective
    (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
  have hk : f.ker = pCore 2 (F.P L) :=
    (F.binaryPermutationAction_ker (by decide) L chosen.normalizes).trans
      (F.binaryPlaneAction_ker_eq_twoCore (by decide) L chosen.normalizes
        (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural))
  let e : (F.P L ⧸ pCore 2 (F.P L)) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.quotientMulEquivOfEq hk).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  refine ⟨⟨e⟩,?_⟩
  have hTP := F.binary_sylow_le_P L
  have hi : (T : Subgroup G).relIndex (F.P L) = 3 :=
    SymmetricThreeTwoCore.sylow_index_three e (T.subtype hTP)
  have hTC : (T : Subgroup G) ≤ F.P L ⊓ F.H := le_inf hTP (F.invariant 1)
  have hprod := relIndex_mul_relIndex (T : Subgroup G) (F.P L ⊓ F.H) (F.P L) hTC inf_le_left
  rw [hi] at hprod
  have hproper : (F.P L ⊓ F.H).relIndex (F.P L) ≠ 1 := by
    intro hh
    obtain ⟨g,hgP,hgH⟩ := source_conjugator_at d earlier hq chosen structural F
    exact hgH (((relIndex_eq_one.mp hh) hgP).2)
  have hone : (T : Subgroup G).relIndex (F.P L ⊓ F.H) = 1 := by
    rcases (Nat.prime_mul_iff.mp (hprod ▸ Nat.prime_three)) with hh | hh
    · exact (hproper hh.2).elim
    · exact hh.2
  exact le_antisymm (relIndex_eq_one.mp hone) hTC
omit [Finite G] d earlier hq chosen structural alternatives F hne in
private theorem solvableAmalgam_relative_core_quotient_at {A E : Subgroup G} (hAE : A ≤ E)
    (model : Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))) :
    Nonempty (((A.subgroupOf E) ⧸ pCore 2 (A.subgroupOf E)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := model
  let j : A.subgroupOf E ≃* A := subgroupOfEquivOfLe hAE
  exact ⟨(QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).trans e⟩
theorem source_solvable_ambient_goldschmidt_at (K : Subgroup G) (hKH : K ≤ F.H)
    (model : Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    ChapterF.IsGoldschmidtTriple
      ((K ⊔ (T : Subgroup G)).subgroupOf (amalgamGroup F L K))
      ((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf (amalgamGroup F L K)) := by
  let A := K ⊔ (T : Subgroup G)
  let B := F.I₂ L ⊔ (T : Subgroup G)
  let E := amalgamGroup F L K
  have hAE : A ≤ E := le_sup_left
  have hBE : B ≤ E := le_sup_right
  obtain ⟨hP,hPH⟩ := source_parabolic_quotient_and_intersection_at d earlier hq chosen structural F
  have hBP : B = F.P L := (source_parabolic_eq_I₂_sylow_at d earlier hq chosen structural alternatives F hne).symm
  have hAB : A ⊓ B = (T : Subgroup G) := by
    apply le_antisymm
    · have hh : A ⊓ B ≤ F.P L ⊓ F.H :=
        le_inf (inf_le_right.trans hBP.le) (inf_le_left.trans (sup_le hKH (F.invariant 1)))
      exact hPH ▸ hh
    · exact le_inf le_sup_right le_sup_right
  have hBmodel : Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) := hBP ▸ hP
  refine ⟨?_,solvableAmalgam_relative_core_quotient_at hAE model,solvableAmalgam_relative_core_quotient_at hBE hBmodel,?_⟩
  · rw [←subgroupOf_sup hAE hBE]
    exact subgroupOf_self E
  · refine ⟨T.subtype (sylow_le_amalgamGroup F L K),?_⟩
    ext x
    change (x:G) ∈ A ⊓ B ↔ (x:G) ∈ (T : Subgroup G)
    rw [hAB]
theorem source_amalgam_plane_image_and_overlap_at (K : Subgroup G) (hKH : K ≤ F.H) :
    let E := amalgamGroup F L K
    let q := QuotientGroup.mk' (amalgamKernel F L K)
    let A := (K ⊔ (T : Subgroup G)).subgroupOf E
    let B := (F.P L).subgroupOf E
    F.Vi 2 ≤ amalgamModule F L K ∧ IsPGroup 2 (q.subgroupMap B).ker ∧
      Nonempty (((B.map q) ⧸ pCore 2 (B.map q)) ≃* Equiv.Perm (Fin 3)) ∧
      A.map q ⊓ B.map q = ((T : Subgroup G).subgroupOf E).map q := by
  let := chosen.elementary
  let E := amalgamGroup F L K
  let Ue := amalgamModule F L K
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  let A := (K ⊔ (T : Subgroup G)).subgroupOf E
  let B := (F.P L).subgroupOf E
  have hPE : F.P L ≤ E := by
    rw [source_parabolic_eq_I₂_sylow_at d earlier hq chosen structural alternatives F hne]
    exact le_sup_right
  have h1E : F.Vi 1 ≤ E := (F.le_seed 1).trans (chosen.le_sylow.trans (sylow_le_amalgamGroup F L K))
  have hUE : Ue ≤ E := conjugateSpanBy_le_self h1E
  have h1U : F.Vi 1 ≤ Ue := le_conjugateSpanBy _ _
  have hPU : F.Vi 2 ≤ Ue := by
    obtain ⟨g,hgP,hgH⟩ := source_conjugator_at d earlier hq chosen structural F
    rw [←F.binary_plane_point_span (by decide) L chosen.normalizes g hgP hgH]
    exact sup_le h1U (conjugate_le_of_normalizes h1U g
      (le_normalizer_conjugateSpanBy _ _ (hPE hgP)))
  have hkerC : q.ker ≤ (centralizer (Ue : Set G)).subgroupOf E := by
    rw [QuotientGroup.ker_mk']
    intro x hx v hv
    exact congrArg Subtype.val (hx ⟨v,hUE hv⟩ hv)
  have hkerH : q.ker ≤ F.H.subgroupOf E :=
    hkerC.trans (comap_mono ((centralizer_le h1U).trans (Subgroup.centralizer_le_normalizer _)))
  let r := q.subgroupMap B
  have hkr : IsPGroup 2 r.ker := by
    let j := E.subtype.comp B.subtype
    have hj : Function.Injective j := E.subtype_injective.comp B.subtype_injective
    apply ((isPGroup_pCoreIn 2 (F.P L)).comap_of_injective j hj).to_le
    intro x hx
    change ((x : E) : G) ∈ (F.P L).pCoreIn 2
    let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
    rw [←(F.binary_parabolic_core (by decide) L chosen.normalizes
      (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural)).1]
    have hxq : q (x:E) = 1 := congrArg Subtype.val hx
    exact ⟨x.property,fun v hv => hkerC hxq v (hPU hv)⟩
  obtain ⟨hP,hPH⟩ := source_parabolic_quotient_and_intersection_at d earlier hq chosen structural F
  obtain ⟨eB⟩ := solvableAmalgam_relative_core_quotient_at hPE hP
  refine ⟨hPU,hkr,⟨(r.pCoreQuotientEquiv (q.subgroupMap_surjective B) hkr).symm.trans eB⟩,?_⟩
  apply le_antisymm
  · rintro x ⟨⟨a,ha,rfl⟩,b,hb,hba⟩
    have hab : a⁻¹ * b ∈ q.ker := by
      change q (a⁻¹*b) = 1
      rw [map_mul,map_inv,hba,inv_mul_cancel]
    have haH : (a:G) ∈ F.H := (sup_le hKH (F.invariant 1)) ha
    have hbH : (b:G) ∈ F.H := by
      have hh := F.H.mul_mem haH (hkerH hab)
      change (a:G) * ((a:G)⁻¹ * (b:G)) ∈ F.H at hh
      simpa only [mul_inv_cancel_left] using hh
    refine ⟨b,?_,hba⟩
    change (b:G) ∈ (T : Subgroup G)
    exact hPH ▸ (show (b:G) ∈ F.P L ⊓ F.H from ⟨hb,hbH⟩)
  · exact le_inf (map_mono (comap_mono le_sup_right))
      (map_mono (comap_mono (F.binary_sylow_le_P L)))
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableCharacteristic.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne
theorem source_amalgam_actor_structure_at (K : Subgroup G)
    (hKH : K ≤ F.H) (hKN : F.H ≤ normalizer (K : Set G))
    (hKC : K ≤ centralizer (F.ZU : Set G))
    (model : Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3))) :
    let E := amalgamGroup F L K
    let q := QuotientGroup.mk' (amalgamKernel F L K)
    let Kplus := (K.subgroupOf E).map q
    IsPGroup 2 (q.subgroupMap (K.subgroupOf E)).ker ∧
      generalizedFitting Kplus = pCore 2 Kplus ∧
      Nonempty ((Kplus ⧸ pCore 2 Kplus) ≃* Equiv.Perm (Fin 3)) := by
  let := chosen.elementary
  let E := amalgamGroup F L K
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  have hKE : K ≤ E := le_sup_left.trans le_sup_left
  let j : K ≃* K.subgroupOf E := (subgroupOfEquivOfLe hKE).symm
  let f := (q.subgroupMap (K.subgroupOf E)).comp j.toMonoidHom
  have hfaith : IsPGroup 2 ((centralizer (F.U : Set G)).subgroupOf K) := by
    let i := inclusion hKH
    apply (pCore_isPGroup.comap_of_injective i (inclusion_injective hKH)).to_le
    intro k hk
    apply source_center_centralizing_kernel_le_core_at d earlier hq chosen structural alternatives F hne
    refine ⟨hKC k.property,?_⟩
    apply (F.mem_uhatAction_ker_iff _).mpr
    intro v hv
    have hc : v * (k:G) = (k:G) * v := hk v hv
    change (k:G)*v*(k:G)⁻¹*v⁻¹ ∈ F.ZU
    rw [←hc]
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,one_mul] using F.ZU.one_mem
  have hs := SymmetricThreeTwoCore.orbit_action_structure
    F.H F.U (F.Vi 2) K F.U_le_H hKH (le_normalizer_conjugateSpanBy V F.H) hKN
    (source_closure_at d earlier hq chosen structural alternatives F hne).1
    (source_seed_geometry_at d earlier hq chosen F).2.1 hKC hfaith model.some f
    ((q.subgroupMap_surjective _).comp j.surjective) (by
    intro k hk v hv
    have hqk : q (j k : E) = 1 := congrArg Subtype.val hk
    have hcentral : (j k : E) ∈ amalgamKernel F L K := (QuotientGroup.eq_one_iff _).mp hqk
    have hplane : F.Vi 2 ≤ amalgamModule F L K :=
      (source_amalgam_plane_image_and_overlap_at d earlier hq chosen structural alternatives F hne K hKH).1
    have hUE : amalgamModule F L K ≤ E := conjugateSpanBy_le_self
      ((F.le_seed 1).trans (chosen.le_sylow.trans (sylow_le_amalgamGroup F L K)))
    exact congrArg Subtype.val (hcentral ⟨v,hUE (hplane hv)⟩ (hplane hv))
    )
  refine ⟨?_,hs.2⟩
  let r : f.ker →* (q.subgroupMap (K.subgroupOf E)).ker :=
    j.toMonoidHom.subgroupComap (q.subgroupMap (K.subgroupOf E)).ker
  exact hs.1.of_surjective r
    (j.toMonoidHom.subgroupComap_surjective_of_surjective
      (q.subgroupMap (K.subgroupOf E)).ker j.surjective)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableQuotient.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne
theorem source_amalgam_actor_kernel_at (K : Subgroup G) (hKH : K ≤ F.H)
    (hKN : F.H ≤ normalizer (K : Set G))
    (hout : ¬ K ≤ normalizer (L : Set G))
    (model : Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let E := amalgamGroup F L K
    let q := QuotientGroup.mk' (amalgamKernel F L K)
    let A := (K ⊔ (T : Subgroup G)).subgroupOf E
    IsPGroup 2 (q.subgroupMap A).ker := by
  let E := amalgamGroup F L K
  let Ue := amalgamModule F L K
  let A0 := K ⊔ (T : Subgroup G)
  let A := A0.subgroupOf E
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  let f := q.subgroupMap A
  obtain ⟨em⟩ := model
  let j : A ≃* A0 := subgroupOfEquivOfLe le_sup_left
  let emA := (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).trans em
  rcases SymmetricThreeTwoCore.normal_twoGroup_or_residual_le emA f.ker with hp | hr
  · exact hp
  · exfalso
    let R := (pResidual 2 K).map K.subtype
    have hRH : R ≤ F.H := (map_subtype_le _).trans hKH
    have hRN : F.H ≤ normalizer (R : Set G) :=
      hKN.trans (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))
    have hKE : K ≤ E := le_sup_left.trans le_sup_left
    let i : K →* A := {
      toFun := fun k => ⟨⟨k,hKE k.property⟩,(show K ≤ A0 from le_sup_left) k.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have h1E : F.Vi 1 ≤ E := (F.le_seed 1).trans
      (chosen.le_sylow.trans (sylow_le_amalgamGroup F L K))
    have hUE : Ue ≤ E := conjugateSpanBy_le_self h1E
    have hplane : F.Vi 2 ≤ Ue :=
      (source_amalgam_plane_image_and_overlap_at d earlier hq chosen structural alternatives F hne K hKH).1
    have hRC : R ≤ centralizer (F.Vi 2 : Set G) := by
      rintro r ⟨k,hk,rfl⟩ v hv
      have hri : i k ∈ pResidual 2 A := map_pResidual_le 2 i (mem_map_of_mem i hk)
      have hq : q ((i k : A) : E) = 1 := congrArg Subtype.val (hr hri)
      have hc : ((i k : A) : E) ∈ amalgamKernel F L K := (QuotientGroup.eq_one_iff _).mp hq
      exact congrArg Subtype.val (hc ⟨v,hUE (hplane hv)⟩ (hplane hv))
    have hRU : R ≤ centralizer (F.U : Set G) := by
      rw [(source_seed_geometry_at d earlier hq chosen F).2.1]
      exact le_centralizer_conjugateSpanBy_of_normalizes R (F.Vi 2) F.H hRN hRC
    have hRp : IsPGroup 2 R := by
      apply ((pCore_isPGroup (p := 2) (G := F.H)).map F.H.subtype).to_le
      intro r hr
      apply mem_map.mpr
      refine ⟨⟨r,hRH hr⟩,?_,rfl⟩
      apply source_center_centralizing_kernel_le_core_at d earlier hq chosen structural alternatives F hne
      refine ⟨(centralizer_le (map_subtype_le (center F.U))) (hRU hr),?_⟩
      apply (F.mem_uhatAction_ker_iff _).mpr
      intro v hv
      have hc := (hRU hr) v hv
      change r*v*r⁻¹*v⁻¹ ∈ F.ZU
      rw [←hc]
      simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,one_mul] using F.ZU.one_mem
    have hpr : IsPGroup 2 (pResidual 2 K) := hRp.of_equiv
      ((pResidual 2 K).equivMapOfInjective K.subtype K.subtype_injective).symm
    have hkp : IsPGroup 2 K := isPGroup_of_residual_isPGroup 2 hpr
    have hKT : K ≤ (T : Subgroup G) :=
      hkp.le_sylow_of_normalized T ((F.invariant 1).trans hKN)
    exact hout (hKT.trans ((SourceAssembly.At.higherRankHypothesis d earlier hq chosen).sylow_normalizes_at structural))
theorem source_amalgam_quotient_goldschmidt_at (K : Subgroup G) (hKH : K ≤ F.H)
    (hKN : F.H ≤ normalizer (K : Set G))
    (hout : ¬ K ≤ normalizer (L : Set G))
    (model : Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (hneq : (F.I₂ L ⊔ (T : Subgroup G)).pCoreIn 2 ≠ (K ⊔ (T : Subgroup G)).pCoreIn 2) :
    let E := amalgamGroup F L K
    let q := QuotientGroup.mk' (amalgamKernel F L K)
    let A := (K ⊔ (T : Subgroup G)).subgroupOf E
    let B := (F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E
    ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) ∧
      (B.map q).pCoreIn 2 ≠ (A.map q).pCoreIn 2 := by
  let E := amalgamGroup F L K
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  let A := (K ⊔ (T : Subgroup G)).subgroupOf E
  let B := (F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E
  have hG := source_solvable_ambient_goldschmidt_at d earlier hq chosen structural alternatives F hne K hKH model
  have hBP : B = (F.P L).subgroupOf E := by
    change (F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E = _
    rw [←source_parabolic_eq_I₂_sylow_at d earlier hq chosen structural alternatives F hne]
  obtain ⟨_,hB,_,hinter⟩ := source_amalgam_plane_image_and_overlap_at d earlier hq chosen structural alternatives F hne K hKH
  have hA := source_amalgam_actor_kernel_at d earlier hq chosen structural alternatives F hne K hKH hKN hout model
  rw [←hBP] at hB hinter
  have model_image (C : Subgroup E) (hc : IsPGroup 2 (q.subgroupMap C).ker)
      (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3))) :
      Nonempty (((C.map q) ⧸ pCore 2 (C.map q)) ≃* Equiv.Perm (Fin 3)) := by
    obtain ⟨ec⟩ := hm
    exact ⟨((q.subgroupMap C).pCoreQuotientEquiv (q.subgroupMap_surjective C) hc).symm.trans ec⟩
  refine ⟨⟨?_,model_image A hA hG.quotient_left,model_image B hB hG.quotient_right,?_⟩,?_⟩
  · rw [←Subgroup.map_sup,hG.generated,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  · exact ⟨(T.subtype (sylow_le_amalgamGroup F L K)).mapSurjective
      (QuotientGroup.mk'_surjective _),hinter⟩
  · apply pCoreIn_image_ne_of_local_kernels 2 q B A hB hA
      (hG.symm.local_twoCore_le_intersection.trans inf_le_right)
      (hG.local_twoCore_le_intersection.trans inf_le_right)
    intro he
    apply hneq
    have hh := congrArg (map E.subtype) he
    rwa [pCoreIn_subgroupOf 2 _ E le_sup_right,pCoreIn_subgroupOf 2 _ E le_sup_left,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans (show F.I₂ L ⊔ (T : Subgroup G) ≤ E from le_sup_right)),
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans (show K ⊔ (T : Subgroup G) ≤ E from le_sup_left))] at hh
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableSourceQuotient.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne
theorem source_solvable_source_classification_with_actor_at
    (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      let E := amalgamGroup F L K
      let q := QuotientGroup.mk' (amalgamKernel F L K)
      let p := QuotientGroup.mk' (pPrimeCore 3 E)
      let A := ((K ⊔ (T : Subgroup G)).subgroupOf E).map p
      let B := ((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E).map p
      let C := (K.subgroupOf E).map p
      K ≤ F.H ∧ F.H ≤ normalizer (K : Set G) ∧
      K ≤ centralizer (F.ZU : Set G) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      ¬ K ≤ normalizer (L : Set G) ∧
      E ≤ centralizer ({e} : Set G) ∧
      IsPReduced 2 ((amalgamModule F L K).subgroupOf E) ∧
      IsSQTK KnownSimple.IsKnownSimple E ∧
      Group.IsSolvable (amalgamKernel F L K) ∧
      Nonempty ((K.subgroupOf E).map q ≃* C) ∧
      ChapterF.IsGoldschmidtTriple A B ∧
      generalizedFitting C = pCore 2 C ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3)) ∧
      ¬ Nonempty ((A ⊓ B : Subgroup (E ⧸ pPrimeCore 3 E)) ≃* Multiplicative (ZMod 2)) ∧
      (∃ S : Sylow 2 (E ⧸ pPrimeCore 3 E), A ⊓ B = (S : Subgroup _) ∧
        (FSource.SourceAlternative A B S ∨ FSource.SourceAlternative B A S)) ∧
      ¬ Group.IsSolvable (E ⧸ pPrimeCore 3 E) ∧
      ¬ Group.IsSolvable (AmalgamQuotient F L K) := by
  obtain ⟨g,l,e,_,_,hl,he,heI,heT,_,hKH,hKN,hKC,hK,hKT,hout,hE,hr,hcore,_,hneq⟩ :=
    source_solvable_shifted_quotients_at d earlier hq chosen structural alternatives F hne hZ model hI
  let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
  let E := amalgamGroup F L K
  let A₀ := (K ⊔ (T : Subgroup G)).subgroupOf E
  let B₀ := (F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E
  let C₀ := K.subgroupOf E
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  let p := QuotientGroup.mk' (pPrimeCore 3 E)
  have hg := source_solvable_ambient_goldschmidt_at d earlier hq chosen structural alternatives F hne K hKH hKT
  have ha := source_amalgam_actor_kernel_at d earlier hq chosen structural alternatives F hne K hKH hKN hout hKT
  have hb : IsPGroup 2 (q.subgroupMap B₀).ker := by
    have ht := (source_amalgam_plane_image_and_overlap_at d earlier hq chosen structural alternatives F hne K hKH).2.1
    rwa [source_parabolic_eq_I₂_sylow_at d earlier hq chosen structural alternatives F hne] at ht
  have hneq₀ : B₀.pCoreIn 2 ≠ A₀.pCoreIn 2 := by
    intro heq
    apply hneq
    have hh := congrArg (map E.subtype) heq
    rwa [pCoreIn_subgroupOf 2 _ E le_sup_right,pCoreIn_subgroupOf 2 _ E le_sup_left,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans (show F.I₂ L ⊔ (T : Subgroup G) ≤ E from le_sup_right)),
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans (show K ⊔ (T : Subgroup G) ≤ E from le_sup_left))] at hh
  let j : C₀.map q ≃* C₀.map p := hg.action_prime_local_equiv q
    (QuotientGroup.mk'_surjective _) hcore ha hb C₀ (comap_mono le_sup_left)
  obtain ⟨_,hf,hm⟩ := source_amalgam_actor_structure_at d earlier hq chosen structural alternatives F hne
    K hKH hKN hKC hK
  have hfit : generalizedFitting (C₀.map p) = pCore 2 (C₀.map p) := by
    have hmap := congrArg (fun N : Subgroup (C₀.map q) => N.map j.toMonoidHom) hf
    rwa [map_generalizedFitting_equiv,pCore_map_iso] at hmap
  have hmodel : Nonempty (((C₀.map p) ⧸ pCore 2 (C₀.map p)) ≃* Equiv.Perm (Fin 3)) :=
    ⟨(QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).symm.trans hm.some⟩
  have hsq : IsSQTK KnownSimple.IsKnownSimple E := by
    have hc := (d.qtke.involution_centralizer_sqtk he).subgroup (E.subgroupOf (centralizer ({e} : Set G)))
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hE)).mp hc
  have hsolv : Group.IsSolvable (amalgamKernel F L K) := by
    have hs := hg.action_kernel_solvable q ha hb
    rwa [QuotientGroup.ker_mk'] at hs
  have hgold := hg.quotient_primeToThreeCore_of_distinct_cores (Ne.symm hneq₀)
  have h1 := hg.primeToThreeCore_intersection_not_cyclic_two (Ne.symm hneq₀)
  have h2 : ¬ (Nonempty ((E ⧸ pPrimeCore 3 E) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ N : Subgroup (E ⧸ pPrimeCore 3 E), ∃ _ : N.Normal,
        IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
        Nonempty (((E ⧸ pPrimeCore 3 E) ⧸ N) ≃* FSource.E4)) := by
    rintro (hp | ⟨N,hN,_,hc,_,⟨eN⟩⟩)
    · exact SymmetricThreeTwoCore.characteristic_two_not_symmetric_three_product _ hfit hmodel.some hp
    · let := hN
      have hN3 : IsPGroup 3 N := IsPGroup.of_card (n := 3) hc
      have hQ2 : IsPGroup 2 (_ ⧸ N) := by
        apply (IsPGroup.of_card (n := 2) (G := FSource.E4) ?_).of_equiv eN.symm
        simp [FSource.E4,FSource.C]
      exact SymmetricThreeTwoCore.characteristic_two_not_three_by_two _ hfit hmodel.some N hN3 hQ2
  let cover : ThreePrimeSQTKQuotient KnownSimple.IsKnownSimple (E ⧸ pPrimeCore 3 E) :=
    { Cover := E, sqtk := hsq, equiv := MulEquiv.refl _ }
  obtain ⟨S,hS,hrows⟩ := FSource.sourceClassification_knownSimple_complete _ _ _ hgold cover
  have hS1 : ¬ Nonempty (S ≃* FSource.C 2) := by
    rintro ⟨jS⟩
    exact h1 ⟨(MulEquiv.subgroupCongr hS).trans jS⟩
  have hnsolv : ¬ Group.IsSolvable (E ⧸ pPrimeCore 3 E) :=
    hrows.elim (fun h => FSource.source_alternative_nonsolvable h hS1 h2)
      (fun h => FSource.source_alternative_nonsolvable h hS1 h2)
  refine ⟨l,e,hl,he,heI,heT,hKH,hKN,hKC,hK,hKT,hout,hE,hr,hsq,hsolv,⟨j⟩,hgold,hfit,hmodel,h1,⟨S,hS,hrows⟩,hnsolv,?_⟩
  intro hs
  let : Group.IsSolvable (amalgamKernel F L K) := hsolv
  let : Group.IsSolvable E := (Group.isSolvable_iff_subgroup_quotient (amalgamKernel F L K)).mpr ⟨hsolv,hs⟩
  exact hnsolv inferInstance
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableRecognition.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open FSource
open Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable
private theorem solvableRecognition_small_fitting_top_at {D : Type*} [Group D] [Finite D]
    (N : Subgroup D) (hN : N.IsSubnormal) (hm : SmallModel N)
    (hq : IsQuasisimple (generalizedFitting D)) (ht : generalizedFitting D = ⊤)
    (S : Sylow 2 D) (hS : Nat.card S ≠ 4) :
    N = ⊤ ∧ Nonempty (N ≃* Matrix.PSL3Two.PSL) := by
  obtain ⟨he,hs⟩ := fitting_eq_small N hN hm hq
  have htop := he.symm.trans ht
  refine ⟨htop,?_⟩
  rcases hs with hs | hs <;> obtain ⟨e⟩ := hs
  · exact ⟨e.trans Matrix.PSL3Two.equiv⟩
  · have hc : Nat.card D = 60 := by
      let a : D ≃* alternatingGroup (Fin 5) :=
        topEquiv.symm.trans ((MulEquiv.subgroupCongr htop).symm.trans e)
      rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    exact (hS (by rw [S.card_eq_multiplicity,hc]; decide +kernel)).elim
private theorem solvableRecognition_source_small_image_top_at {D : Type*} [Group D] [Finite D]
    (N : Subgroup D) (hN : N.IsSubnormal) (hm : SmallModel N)
    {A B : Subgroup D} {S : Sylow 2 D} (ha : SourceAlternative A B S)
    (h1 : ¬ Nonempty (S ≃* C 2))
    (h2 : ¬ (Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ M : Subgroup D, ∃ _ : M.Normal,
        IsExtraspecial 3 M ∧ Nat.card M = 27 ∧ Monoid.exponent M = 3 ∧
        Nonempty ((D ⧸ M) ≃* E4))) :
    N = ⊤ ∧ Nonempty (N ≃* Matrix.PSL3Two.PSL) := by
  have hd (hq : IsQuasisimple (generalizedFitting D)) (ht : generalizedFitting D = ⊤)
      (hs : Nonempty (S ≃* DihedralGroup 4)) :
      N = ⊤ ∧ Nonempty (N ≃* Matrix.PSL3Two.PSL) := by
    obtain ⟨e⟩ := hs
    apply solvableRecognition_small_fitting_top_at N hN hm hq ht S
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
    decide
  rcases ha with (ha | ⟨r⟩) | ⟨r⟩
  · cases ha with
    | one hs _ _ _ => exact (h1 hs).elim
    | two hs => exact (h2 hs).elim
    | three r hs _ _ =>
      obtain ⟨e⟩ := hs
      exact (not_product_row S (by rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]) r N hN hm).elim
    | four f hd hc e ht hq _ _ _ =>
      let a : generalizedFitting D ≃* D := (MulEquiv.subgroupCongr ht).trans topEquiv
      exact (not_prime_linear_component N hN hm hq f hd hc (a.trans e)).elim
    | five f hd hc _ e hq _ _ _ =>
      exact (not_prime_linear_component N hN hm hq f hd hc e).elim
    | six _ ht hq hs _ _ => exact hd hq ht hs
    | seven hs hq _ _ _ =>
      apply (not_exceptional_model N hN hm hq _).elim
      exact hs.elim Or.inl (fun h => Or.inr (Or.inl h))
    | eight hs hq _ _ _ =>
      rcases hs with hs | ⟨r⟩
      · exact (not_exceptional_model N hN hm hq (Or.inr (Or.inr (Or.inl hs)))).elim
      · exact (not_field_extension N hN hm hq r.some).elim
    | nine hs hq _ _ _ =>
      apply (not_exceptional_model N hN hm hq _).elim
      exact hs.elim (fun h => Or.inr (Or.inr (Or.inr (Or.inl h))))
        (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    | ten _ _ _ _ ht hq hs _ _ =>
      obtain ⟨e⟩ := hs
      have h32 : Nat.card S = 32 := by
        rw [Nat.card_congr e.toEquiv,RegularWreathProduct.card]
        norm_num [C]
      obtain ⟨he,hm'⟩ := fitting_eq_small N hN hm hq
      let a : D ≃* N := topEquiv.symm.trans (MulEquiv.subgroupCongr (he.symm.trans ht)).symm
      have hdvd := (S : Subgroup D).card_subgroup_dvd_card
      rcases hm' with hh | hh <;> obtain ⟨j⟩ := hh
      · rw [h32,Nat.card_congr (a.trans j).toEquiv,Matrix.PSL3Two.card_SL] at hdvd
        norm_num at hdvd
      · rw [h32,Nat.card_congr (a.trans j).toEquiv,nat_card_alternatingGroup] at hdvd
        norm_num [Nat.factorial] at hdvd
    | eleven r hq _ _ _ =>
      exact (not_degreeThree_component N hN hm hq r.prime_isPrime r.congruence r.model.model).elim
    | twelve e hq _ _ _ =>
      exact (not_exceptional_model N hN hm hq (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))))).elim
    | thirteen _ e hq _ _ _ => exact (not_mathieu_component N hN hm hq e).elim
  · exact hd r.some.quasisimple r.some.component r.some.sylow
  · exact (not_square_field_extension N hN hm r.some).elim
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_solvable_quotient_recognition_with_actor_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      let E := amalgamGroup F L K
      K ≤ F.H ∧ F.H ≤ normalizer (K : Set G) ∧
      K ≤ centralizer (F.ZU : Set G) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      ¬ K ≤ normalizer (L : Set G) ∧
      E ≤ centralizer ({e} : Set G) ∧
      IsPReduced 2 ((amalgamModule F L K).subgroupOf E) ∧
      Nonempty ((E ⧸ pPrimeCore 3 E) ≃* Matrix.PSL3Two.PSL) ∧
      ∃ C : Subgroup G, C ∈ Chapter1.cComponentsIn E ∧
        C ∈ MainForward.faithfulLocalComponents T ∧
        ⁅amalgamModule F L K,C⁆ ≠ ⊥ ∧
        (C.subgroupOf (C ⊔ (T : Subgroup G))).Normal ∧ C ∈ Chapter1.LStar G T ∧
        (C.subgroupOf E).map (QuotientGroup.mk' (pPrimeCore 3 E)) = ⊤ := by
  obtain ⟨l,e,hl,he,heI,heT,hKH,hKN,hKC,hK,hKT,hout,hE,hr,_,_,_,_,hf,hm,h1,⟨S,hS,hrows⟩,_,hn⟩ :=
    source_solvable_source_classification_with_actor_at d earlier hq chosen structural alternatives F hne hZ model hI
  let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
  let E := amalgamGroup F L K
  let p := QuotientGroup.mk' (pPrimeCore 3 E)
  obtain ⟨C,hC,hfaith,hmove,_,hnormal,hmax,hsub,hsmall⟩ :=
    source_amalgam_classified_component d chosen F K classification hr hn
  let N := (C.subgroupOf E).map p
  have hsmall' : SmallModel N := by
    rcases hsmall with ha | ha <;> obtain ⟨a⟩ := ha
    · exact Or.inr (Or.inr ⟨a⟩)
    · exact Or.inr (Or.inl ⟨a.trans Matrix.PSL3Two.equiv.symm⟩)
  have hS1 : ¬ Nonempty (S ≃* FSource.C 2) := by
    rintro ⟨j⟩
    exact h1 ⟨(MulEquiv.subgroupCongr hS).trans j⟩
  have h2 : ¬ (Nonempty ((E ⧸ pPrimeCore 3 E) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ M : Subgroup (E ⧸ pPrimeCore 3 E), ∃ _ : M.Normal,
        IsExtraspecial 3 M ∧ Nat.card M = 27 ∧ Monoid.exponent M = 3 ∧
        Nonempty (((E ⧸ pPrimeCore 3 E) ⧸ M) ≃* E4)) := by
    rintro (hp | ⟨M,hM,_,hc,_,⟨eM⟩⟩)
    · exact SymmetricThreeTwoCore.characteristic_two_not_symmetric_three_product _ hf hm.some hp
    · let := hM
      have hM3 : IsPGroup 3 M := IsPGroup.of_card (n := 3) hc
      have hQ2 : IsPGroup 2 (_ ⧸ M) := by
        apply (IsPGroup.of_card (n := 2) (G := E4) ?_).of_equiv eM.symm
        simp [E4,FSource.C]
      exact SymmetricThreeTwoCore.characteristic_two_not_three_by_two _ hf hm.some M hM3 hQ2
  obtain ⟨ht,⟨a⟩⟩ := hrows.elim
    (fun h => solvableRecognition_source_small_image_top_at N hsub hsmall' h hS1 h2)
    (fun h => solvableRecognition_source_small_image_top_at N hsub hsmall' h hS1 h2)
  let j : (E ⧸ pPrimeCore 3 E) ≃* N :=
    topEquiv.symm.trans (MulEquiv.subgroupCongr ht).symm
  exact ⟨l,e,hl,he,heI,heT,hKH,hKN,hKC,hK,hKT,hout,hE,hr,⟨j.trans a⟩,C,hC,hfaith,hmove,hnormal,hmax,ht⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableActionQuotient.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison
private theorem solvableActionQuotient_action_equiv_of_prime_and_component_at
    {E D : Type*} [Group E] [Finite E] [Group D] [Finite D]
    {A B : Subgroup E} (h : ChapterF.IsGoldschmidtTriple A B)
    (f : E →* D) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (hD : ChapterF.IsGoldschmidtTriple (A.map f) (B.map f)) (hc : pCore 2 D = ⊥)
    (e : (E ⧸ pPrimeCore 3 E) ≃* Matrix.PSL3Two.PSL)
    (C : Subgroup E) (hC : C.IsSubnormal) [Group.IsPerfect C]
    [IsSimpleGroup (C ⧸ pCore 2 C)]
    (ht : C.map (QuotientGroup.mk' (pPrimeCore 3 E)) = ⊤) :
    f.ker = pPrimeCore 3 E ∧ Nonempty (D ≃* Matrix.PSL3Two.PSL) ∧
      C = solvableResidual E := by
  let R := pPrimeCore 3 E
  let p := QuotientGroup.mk' R
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect Matrix.PSL3Two.PSL := Atlas.psl_perfect (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup (E ⧸ R) := e.isSimpleGroup
  let : Group.IsPerfect (E ⧸ R) := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hker : f.ker ≤ R := by
    have hh := solvable_normal_le_simple_ker p (QuotientGroup.mk'_surjective _)
      (Group.IsPerfect.not_isSolvable _) f.ker
    rwa [QuotientGroup.ker_mk'] at hh
  let π : D →* E ⧸ R := f.liftOfSurjective hf ⟨p,by simpa only [p,QuotientGroup.ker_mk'] using hker⟩
  have hπf (x : E) : π (f x) = p x :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective R y
    exact ⟨f x,hπf x⟩
  have hπker : π.ker.comap f = R := by
    ext x
    change π (f x) = 1 ↔ x ∈ R
    rw [hπf]
    exact QuotientGroup.eq_one_iff _
  have hmap : R.map f = π.ker := by
    exact (congrArg (map f) hπker).symm.trans (map_comap_eq_self_of_surjective hf _)
  have hcop : Nat.Coprime 3 (Nat.card π.ker) := by
    rw [←hmap]
    exact pPrimeCore_coprime_card.of_dvd_right (card_map_dvd _ _)
  have hpbot : pPrimeCore 3 (E ⧸ R) = ⊥ :=
    pPrimeCore_eq_bot_of_equiv e (pPrimeCore_eq_bot_of_simple
      (by rw [Matrix.PSL3Two.card_PSL]; decide))
  have hkπ : π.ker = pPrimeCore 3 D := by
    have hh := pPrimeCore_comap_eq_of_surjective_coprime 3 π hπ hcop
    rwa [hpbot] at hh
  let ep : (D ⧸ pPrimeCore 3 D) ≃* Matrix.PSL3Two.PSL :=
    (QuotientGroup.quotientMulEquivOfEq hkπ.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective π hπ).trans e)
  let : Group.IsSolvable p.ker := by
    rw [QuotientGroup.ker_mk']
    exact h.primeToThreeCore_solvable
  let j := hC.simpleCoreImageEquiv C p (QuotientGroup.mk'_surjective _)
    h.primeToThreeCore_quotient_twoCore_eq_bot
  let k := hC.simpleCoreImageEquiv C f hf hc
  let eC : C.map f ≃* Matrix.PSL3Two.PSL :=
    k.symm.trans (j.trans ((MulEquiv.subgroupCongr ht).trans (topEquiv.trans e)))
  obtain ⟨hzero,hmodel⟩ := plus_equiv_of_subnormal_and_bang hD hc ep (C.map f) (hC.map hf) eC
  have hfker : f.ker = R := by
    have hh := pPrimeCore_comap_eq_of_surjective_coprime 3 f hf
      (pPrimeCore_coprime_card.of_dvd_right (card_dvd_of_le hker))
    rwa [hzero] at hh
  have hsup : C ⊔ R = ⊤ := by
    change C.map p = ⊤ at ht
    have hh := congrArg (comap p) ht
    simpa only [comap_map_eq,p,QuotientGroup.ker_mk',comap_top] using hh
  let : Group.IsSolvable R := h.primeToThreeCore_solvable
  exact ⟨hfker,hmodel,hC.eq_solvableResidual_of_sup_eq_top R hsup⟩
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_solvable_action_recognition_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      let E := amalgamGroup F L K
      K ≤ F.H ∧ F.H ≤ normalizer (K : Set G) ∧ K ≤ centralizer (F.ZU : Set G) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) ∧
      E ≤ centralizer ({e} : Set G) ∧
      IsPReduced 2 ((amalgamModule F L K).subgroupOf E) ∧
      amalgamKernel F L K = pPrimeCore 3 E ∧
      Nonempty (AmalgamQuotient F L K ≃* Matrix.PSL3Two.PSL) ∧
      ChapterF.IsGoldschmidtTriple
        (((K ⊔ (T : Subgroup G)).subgroupOf E).map (QuotientGroup.mk' (amalgamKernel F L K)))
        (((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E).map (QuotientGroup.mk' (amalgamKernel F L K))) ∧
      ∃ C : Subgroup G, C ∈ Chapter1.cComponentsIn E ∧
        C ∈ MainForward.faithfulLocalComponents T ∧
        C.subgroupOf E = solvableResidual E := by
  obtain ⟨l,e,hl,he,heI,heT,hKH,hKN,hKC,hK,hKT,hout,hE,hr,⟨ep⟩,
      C,hC,hfaith,_,_,_,ht⟩ :=
    source_solvable_quotient_recognition_with_actor_at d earlier hq chosen structural alternatives
      classification F hne hZ model hI
  let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
  let E := amalgamGroup F L K
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  have hs := source_seed_exclusion_of_solvable_model_at d earlier hq chosen structural alternatives F hne model
  have hneq := (source_contrary_thompson_escape_at d earlier hq chosen structural alternatives F hne hs hI K hout).2
  have hg := source_solvable_ambient_goldschmidt_at d earlier hq chosen structural alternatives F hne K hKH hKT
  have hqg := (source_amalgam_quotient_goldschmidt_at d earlier hq chosen structural alternatives F hne
    K hKH hKN hout hKT hneq).1
  have ha := source_amalgam_actor_kernel_at d earlier hq chosen structural alternatives F hne K hKH hKN hout hKT
  have hb : IsPGroup 2 (q.subgroupMap ((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E)).ker := by
    have hh := (source_amalgam_plane_image_and_overlap_at d earlier hq chosen structural alternatives F hne K hKH).2.1
    rwa [source_parabolic_eq_I₂_sylow_at d earlier hq chosen structural alternatives F hne] at hh
  let : Group.IsSolvable q.ker := hg.action_kernel_solvable q ha hb
  have hh := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T C).mp hfaith
  have hm := (classification C hh.1 hh.2).1
  let j : C.subgroupOf E ≃* C := subgroupOfEquivOfLe hC.1
  let jq := QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  let : IsSimpleGroup ((C.subgroupOf E) ⧸ pCore 2 (C.subgroupOf E)) := by
    rcases hm with ha | ha <;> obtain ⟨a⟩ := ha
    · let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact (jq.trans a).isSimpleGroup
    · let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
      exact (jq.trans a).isSimpleGroup
  let := hC.2.perfect
  obtain ⟨hk,hmodel,hres⟩ := solvableActionQuotient_action_equiv_of_prime_and_component_at hg q (QuotientGroup.mk'_surjective _)
    hqg hr.quotient_pCore_eq_bot ep (C.subgroupOf E) hC.2.subnormal ht
  rw [QuotientGroup.ker_mk'] at hk
  exact ⟨l,e,hl,he,heI,heT,hKH,hKN,hKC,hK,hE,hr,hk,hmodel,hqg,C,hC,hfaith,hres⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableNatural.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_amalgam_natural_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (K : Subgroup G) (hKH : K ≤ F.H)
    (hr : IsPReduced 2 ((amalgamModule F L K).subgroupOf (amalgamGroup F L K)))
    (hg : ChapterF.IsGoldschmidtTriple
      (((K ⊔ (T : Subgroup G)).subgroupOf (amalgamGroup F L K)).map (QuotientGroup.mk' (amalgamKernel F L K)))
      (((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf (amalgamGroup F L K)).map (QuotientGroup.mk' (amalgamKernel F L K))))
    (model : Nonempty (AmalgamQuotient F L K ≃* Matrix.PSL3Two.PSL)) :
    let E := amalgamGroup F L K
    let W := amalgamModule F L K
    ∃ π : E →* Matrix.PSL3Two.SL, Function.Surjective π ∧
      π.ker = amalgamKernel F L K ∧
      ((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E).map π = Matrix.PSL3Two.lineParabolicSL ∧
      ((K ⊔ (T : Subgroup G)).subgroupOf E).map π = Matrix.PSL3Two.pointParabolicSL ∧
      ∃ c : W ≃* Multiplicative BinaryLinearThree.Vector,
        (∀ (a : E) (w : W),
          (c (W.normalizerMonoidHom (inclusion (le_normalizer_conjugateSpanBy _ _) a) w)).toAdd =
            BinaryLinearThree.W (π a) (c w).toAdd) ∧ Nat.card W = 8 := by
  let := chosen.elementary
  let E := amalgamGroup F L K
  let W := amalgamModule F L K
  let A := K ⊔ (T : Subgroup G)
  let B := F.I₂ L ⊔ (T : Subgroup G)
  let D := AmalgamQuotient F L K
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  let q₀ := QuotientGroup.mk' (pCore 2 D)
  have hcore : pCore 2 D = ⊥ := hr.quotient_pCore_eq_bot
  have hq₀ : Function.Injective q₀ := q₀.ker_eq_bot_iff.mp (by rw [QuotientGroup.ker_mk',hcore])
  let j : D ≃* D ⧸ pCore 2 D := MulEquiv.ofBijective q₀ ⟨hq₀,QuotientGroup.mk'_surjective _⟩
  obtain ⟨_,m,_,_,hline,hpoint⟩ := mark_goldschmidt_quotient
    ((B.subgroupOf E).map q) ((A.subgroupOf E).map q) hg.symm (j.symm.trans model.some)
  let π : E →* Matrix.PSL3Two.SL := m.toMonoidHom.comp (q₀.comp q)
  have hπ : Function.Surjective π := m.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hker : π.ker = amalgamKernel F L K := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.injective,
      MonoidHom.ker_comp_of_injective _ _ hq₀,QuotientGroup.ker_mk']
  have hline' : (B.subgroupOf E).map π = Matrix.PSL3Two.lineParabolicSL := by
    simpa only [map_map] using hline
  have hpoint' : (A.subgroupOf E).map π = Matrix.PSL3Two.pointParabolicSL := by
    simpa only [map_map] using hpoint
  have hWE : W ≤ E := conjugateSpanBy_le_self
    ((F.le_seed 1).trans (chosen.le_sylow.trans (sylow_le_amalgamGroup F L K)))
  let := hr.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_surjective
    (subgroupOfEquivOfLe hWE).toMonoidHom (subgroupOfEquivOfLe hWE).surjective
  obtain ⟨z,hz,hzpoint⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hBC : A ≤ centralizer (F.Vi 1 : Set G) :=
    (sup_le hKH (F.invariant 1)).trans (normalizer_le_centralizer_of_card_two _
      (by simpa using F.card 1 (by decide)))
  have hBP : B = F.P L := (source_parabolic_eq_I₂_sylow_at d earlier hq chosen structural alternatives F hne).symm
  have hplane : conjugateSpanBy (F.Vi 1) B = F.Vi 2 := by
    rw [hBP]
    apply le_antisymm (conjugateSpanBy_le (F.monotone (by decide))
      (F.P_le_G₂ (by decide) L chosen.normalizes))
    obtain ⟨g,hgP,hgH⟩ := source_conjugator_at d earlier hq chosen structural F
    rw [←F.binary_plane_point_span (by decide) L chosen.normalizes g hgP hgH]
    exact sup_le (le_conjugateSpanBy _ _)
      (conjugate_le_of_normalizes (le_conjugateSpanBy _ _) g (le_normalizer_conjugateSpanBy _ _ hgP))
  obtain ⟨c,hc⟩ := Representation.ConjugatePointNatural.exists_natural_coordinates
    E W (F.Vi 1) B A (le_normalizer_conjugateSpanBy _ _) (le_conjugateSpanBy _ _)
    z hzpoint hz π hπ (by
      rw [hker]
      intro x hx w hw
      exact congrArg Subtype.val (hx ⟨w,hWE hw⟩ hw))
    le_sup_right hline' hpoint' hBC rfl (by rw [hplane]; simpa using F.card 2 (by decide))
  refine ⟨π,hπ,hker,hline',hpoint',c,hc,?_⟩
  rw [Nat.card_congr c.toEquiv]
  simp [BinaryLinearThree.Vector]
theorem source_solvable_orbit_card_eight_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : Chapter14.Section04.LargerDimension.LocalAction.Components.EarlierFaithfulClassification
      G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      let E := amalgamGroup F L K
      K ≤ F.H ∧ F.H ≤ normalizer (K : Set G) ∧ K ≤ centralizer (F.ZU : Set G) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) ∧
      E ≤ centralizer ({e} : Set G) ∧
      IsPReduced 2 ((amalgamModule F L K).subgroupOf E) ∧
      amalgamKernel F L K = pPrimeCore 3 E ∧
      Nonempty (AmalgamQuotient F L K ≃* Matrix.PSL3Two.PSL) ∧
      Nat.card (amalgamModule F L K) = 8 := by
  obtain ⟨l,e,hl,he,heI,heT,hKH,hKN,hKC,hK,hE,hr,hker,hm,hg,_⟩ :=
    source_solvable_action_recognition_at d earlier hq chosen structural alternatives
      classification F hne hZ model hI
  obtain ⟨_,_,_,_,_,_,_,hc⟩ := source_amalgam_natural_at d earlier hq chosen structural alternatives
    F hne _ hKH hr hg hm
  exact ⟨l,e,hl,he,heI,heT,hKH,hKN,hKC,hK,hE,hr,hker,hm,hc⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableOrbitBound.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne
theorem source_solvable_tilde_actor_model_at (K : Subgroup G) (hKH : K ≤ F.H)
    (hKN : F.H ≤ normalizer (K : Set G))
    (model : Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3))) :
    let C := centralizer (F.tilde F.U : Set F.G₁tilde)
    ∃ hn : (F.tilde F.U).Normal, letI := hn
      Nonempty (((F.tilde K) ⧸ C.comap (F.tilde K).subtype) ≃* Equiv.Perm (Fin 3)) := by
  let := chosen.elementary
  let A := K.subgroupOf F.H
  let q := F.tildeProjection
  let B := F.tilde K
  let Z := F.tilde F.U
  let C := centralizer (Z : Set F.G₁tilde)
  let : A.Normal := normal_subgroupOf_of_le_normalizer hKN
  let : (F.U.subgroupOf F.H).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy V F.H)
  let hZ : Z.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := hZ
  refine ⟨hZ,?_⟩
  let f : A →* B ⧸ C.comap B.subtype :=
    (QuotientGroup.mk' (C.comap B.subtype)).comp (q.subgroupMap A)
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
    (q.subgroupMap_surjective A)
  have hact : (F.localTildeAction F.H le_rfl).ker = C.comap q := by
    change (F.tildeAction F.H F.U le_rfl (le_normalizer_conjugateSpanBy V F.H)).ker = _
    exact F.tildeAction_ker F.H F.U le_rfl (le_normalizer_conjugateSpanBy V F.H)
  have hk : f.ker = pCore 2 A := by
    have hh : f.ker = (pCore 2 F.H).comap A.subtype := by
      rw [←(CaseOneLarge.source_closure_geometry_at F d earlier hq chosen structural alternatives hne).tilde_kernel,
        hact]
      ext k
      change QuotientGroup.mk' (C.comap B.subtype) (q.subgroupMap A k) = 1 ↔ q (k:F.H) ∈ C
      exact QuotientGroup.eq_one_iff _
    rw [hh]
    apply le_antisymm
    · exact le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
    · apply map_le_iff_le_comap.mp
      exact le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,pCore_isPGroup.map A.subtype⟩
  let j : A ≃* K := subgroupOfEquivOfLe hKH
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      ((QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).trans model.some))⟩
omit [Finite G] d earlier hq chosen structural alternatives hne in
private theorem solvableOrbitBound_tilde_span_at (A B : Subgroup G) (hAH : A ≤ F.H) (hBH : B ≤ F.H) :
    F.tilde (conjugateSpanBy A B) = conjugateSpanBy (F.tilde A) (F.tilde B) := by
  have hSH : conjugateSpanBy A B ≤ F.H := conjugateSpanBy_le hAH (hBH.trans F.H.le_normalizer)
  have hs : (conjugateSpanBy A B).subgroupOf F.H =
      conjugateSpanBy (A.subgroupOf F.H) (B.subgroupOf F.H) := by
    apply Subgroup.map_injective F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hSH,map_conjugateSpanBy,
      map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hBH]
  change ((conjugateSpanBy A B).subgroupOf F.H).map F.tildeProjection = _
  rw [hs,map_conjugateSpanBy]
  rfl
theorem source_solvable_orbit_card_gt_eight_at (K : Subgroup G)
    (hKH : K ≤ F.H) (hKN : F.H ≤ normalizer (K : Set G))
    (hKC : K ≤ centralizer (F.ZU : Set G))
    (model : Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)))
    (hZ : F.ZU ≠ F.Vi 1) : 8 < Nat.card (amalgamModule F L K) := by
  by_contra hbig
  have hsmall : Nat.card (amalgamModule F L K) ≤ 8 := by omega
  let := chosen.elementary
  let c := CaseOneLarge.source_closure_geometry_at F d earlier hq chosen structural alternatives hne
  let := F.tilde_elementary_of_point c.two c.frattini_point
  let W := conjugateSpanBy (F.Vi 2) K
  let q := F.tildeProjection
  have hWU : W ≤ F.U := conjugateSpanBy_le
    ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))
    (hKH.trans (le_normalizer_conjugateSpanBy V F.H))
  have hWH : W ≤ F.H := hWU.trans F.U_le_H
  have hWe : W ≤ amalgamModule F L K := conjugateSpanBy_le
    (source_amalgam_plane_image_and_overlap_at d earlier hq chosen structural alternatives F hne K hKH).1
    ((show K ≤ amalgamGroup F L K from le_sup_left.trans le_sup_left).trans
      (le_normalizer_conjugateSpanBy _ _))
  have h1W : F.Vi 1 ≤ W := (F.monotone (by decide : 1 ≤ 2)).trans (le_conjugateSpanBy _ _)
  have hWcard : Nat.card W ≤ 8 :=
    (Nat.card_le_card_of_injective (inclusion hWe) (inclusion_injective hWe)).trans hsmall
  have hWtcard : Nat.card (F.tilde W) ≤ 4 := by
    let f := F.tildeMap W hWH
    have hk : f.ker = (F.Vi 1).subgroupOf W := by
      ext w
      change f w = 1 ↔ (w:G) ∈ F.Vi 1
      constructor
      · intro hh
        exact (QuotientGroup.eq_one_iff (N := (F.Vi 1).subgroupOf F.H)
          (⟨w,hWH w.property⟩ : F.H)).mp (congrArg Subtype.val hh)
      · intro hh
        apply Subtype.ext
        exact (QuotientGroup.eq_one_iff (N := (F.Vi 1).subgroupOf F.H)
          (⟨w,hWH w.property⟩ : F.H)).mpr hh
    have hkc : Nat.card f.ker = 2 := by
      rw [hk,Nat.card_congr (subgroupOfEquivOfLe h1W).toEquiv]
      simpa using F.card 1 (by decide)
    have hh := f.ker.card_mul_index
    rw [index_ker,f.range_eq_top_of_surjective (F.tildeMap_surjective W hWH),card_top,hkc] at hh
    omega
  have hH : F.tilde F.H = ⊤ := by
    change (F.H.subgroupOf F.H).map q = ⊤
    rw [subgroupOf_self,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hgen : conjugateSpanBy W F.H = F.U := by
    apply le_antisymm (conjugateSpanBy_le hWU (le_normalizer_conjugateSpanBy V F.H))
    rw [(source_seed_geometry_at d earlier hq chosen F).2.1]
    exact conjugateSpanBy_mono (le_conjugateSpanBy _ _) le_rfl
  have hgent : conjugateSpanBy (F.tilde W) ⊤ = F.tilde F.U := by
    rw [←hH,←solvableOrbitBound_tilde_span_at F W F.H hWH le_rfl,hgen]
  obtain ⟨hn,hm⟩ := source_solvable_tilde_actor_model_at d earlier hq chosen structural alternatives F hne K hKH hKN model
  let := hn
  let : (F.tilde K).Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←hH]
    exact F.tilde_normalizes F.H K hKN))
  have hfix := fixed_eq_bot_of_symmetricThree_small_orbit (F.tilde F.U) (F.tilde K) (F.tilde W)
    (IsElementaryAbelian.isPGroup 2 _) (map_mono (comap_mono hWU))
    (F.tilde_normalizes K W (le_normalizer_conjugateSpanBy _ _)) hWtcard hgent hm
  have hZt : F.tilde F.ZU = ⊥ := by
    apply bot_unique
    rw [←hfix]
    refine le_inf (map_mono (comap_mono (map_subtype_le (center F.U)))) ?_
    rintro x ⟨z,hz,rfl⟩ y ⟨k,hk,rfl⟩
    have he : k*z=z*k := Subtype.ext ((hKC hk) z hz).symm
    exact (map_mul q k z).symm.trans ((congrArg q he).trans (map_mul q z k))
  apply hZ
  apply le_antisymm _ (F.point_le_ZU (by decide))
  intro z hz
  have hzq : q ⟨z,(map_subtype_le (center F.U)).trans F.U_le_H hz⟩ = 1 := by
    have hh := mem_map_of_mem q (show (⟨z,(map_subtype_le (center F.U)).trans F.U_le_H hz⟩ : F.H) ∈
      F.ZU.subgroupOf F.H from hz)
    change q _ ∈ F.tilde F.ZU at hh
    simpa only [hZt,mem_bot] using hh
  exact (QuotientGroup.eq_one_iff (N := (F.Vi 1).subgroupOf F.H)
    (⟨z,(map_subtype_le (center F.U)).trans F.U_le_H hz⟩ : F.H)).mp hzq
theorem source_centerless_of_solvable_model_at
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  by_contra hI
  obtain ⟨l,e,hl,he,heI,heT,hKH,hKN,hKC,hK,hE,hr,hker,hm,hcard⟩ :=
    source_solvable_orbit_card_eight_at d earlier hq chosen structural alternatives
      classification F hne hZ model hI
  have hlarge := source_solvable_orbit_card_gt_eight_at d earlier hq chosen structural alternatives
    F hne _ hKH hKN hKC hK hZ
  omega
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end
