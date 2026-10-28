module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableRow
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.ShiftedType
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.PointRanks
public import Theory.GroupTheory.NormalSymmetricThreeSupplement
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# The original solvable shifted actor and Thompson escape

The shifted involution has nontrivial hatted image inside the marked
order-two conjugate center. Its H-normal closure therefore has exactly
the same dotted image as the original solvable seed actor. The kernel on
this center-centralizing subgroup lies in O₂(H); restriction identifies
its own two-core and constructs its actual S₃ quotient. Adjoining T
preserves that quotient, and the marked supplement forces escape from M.

The already proved Thompson normality gives N_G(J(T)) ≤ M by the actual
unique maximal two-local property. If J(T) lay in O₂(KT), Thompson heredity
would force KT to normalize J(T), contradicting escape. Thus the original
KT and I₂T have distinct embedded two-cores. The final application constructs
the same g,l,e,K from the source S₃×S₃ model and retains Ke/C_Ke(Ue), its
trivial two-core, and the reduced orbit module.

These are inputs to the Goldschmidt paragraph of 14.3.31, not its conclusion.
The local image quotients, overlap and unequal-core transport through the
literal centralizer quotient, the F.6.18 contradiction, and final centerlessness
assembly remain with qt-d-hs-centerless-source. The separately proved earlier
structural inputs retain their original producers. Source: Aschbacher--Smith,
14.3.29--31, printed pp.1002--1003, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne

omit d earlier hq chosen structural alternatives hne in
private theorem shifted_normal_closure_image
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

/-- The source shifted normal closure has the literal S₃ quotient, its
hatted action kernel is its own two-core, and it escapes the original M. -/
theorem source_shifted_solvable_actor
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
  have hm := shifted_normal_closure_image F g hgH row a ha ha2 haf
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
    apply source_center_centralizing_kernel_le_core d earlier hq chosen structural alternatives F hne
    exact ⟨hKC x.property,(show x ∈ (F.uhatAction.comp K.subtype).ker from hfk ▸ hx)⟩
  have hk := ker_eq_twoCore_of_surjective_perm_three f hf hp
  refine ⟨hfk.symm.trans hk,⟨(QuotientGroup.quotientMulEquivOfEq hk).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩,?_⟩
  intro hKM
  apply source_dotted_intersection_ne_top d earlier hq chosen structural alternatives F hne
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
      ((higherRankHypothesis d earlier hq chosen).sylow_normalizes structural)))

omit d earlier hq chosen structural alternatives hne in
private theorem normal_s3_sylow_join (K : Subgroup G)
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

/-- The Thompson subgroup cannot lie in the core of an escaping Sylow
supplement; consequently its two-core differs from the plane parabolic core. -/
theorem source_contrary_thompson_escape
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
  have hJn := source_contrary_thompson_normal d earlier hq chosen structural alternatives F hne hseed hI
  have hNJ : normalizer (J : Set G) ≤ normalizer (L : Set G) := by
    have unique : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
      intro X _ _ hX S B hB
      exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hB
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
    · intro N hN hLN
      exact Set.mem_singleton_iff.mp
        (((higherRankHypothesis d earlier hq chosen).maximal_unique structural unique).2 ▸
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
    source_contrary_thompson_le_plane_core d earlier hq chosen structural alternatives F hne hseed hI)⟩

/-- Construct the original shifted actor and both S₃ two-core quotients from
the actual S₃×S₃ model, along with the faithful centralizer quotient and escape. -/
theorem source_solvable_shifted_quotients
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
  have hseed := source_seed_exclusion_of_solvable_model d earlier hq chosen structural alternatives F hne model
  obtain ⟨g,l,e,hgL,hgP,hgH,hlL,hl,hspace,hgen,he,heI,heT,heU,heV,
    haH,ha,hfaith,_,hNC,hKe,hr,hcore⟩ :=
    source_shifted_amalgam_faithful d earlier hq chosen structural alternatives F hne hseed hI
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
    (source_shifted_center_intersection d earlier hq chosen structural alternatives F hne
      g hgP hgH l hl ▸ haI).1
  let := chosen.elementary
  obtain ⟨htwo,hphi,_⟩ := source_closure d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  have row := source_solvable_seed_row d earlier hq chosen structural alternatives F hne hZ model g hgP hgH
  obtain ⟨_,hN,hout⟩ := source_shifted_solvable_actor d earlier hq chosen structural alternatives F hne
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
    normal_s3_sylow_join F K hKN hk,?_,hKe,hr,hcore,?_⟩
  · change ¬ N.map F.H.subtype ≤ normalizer (L:Set G) at hout
    rwa [hm] at hout
  · apply source_contrary_thompson_escape d earlier hq chosen structural alternatives F hne hseed hI K
    change ¬ N.map F.H.subtype ≤ normalizer (L:Set G) at hout
    rwa [hm] at hout

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
