module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.ShiftedGeometry

/-!
# Faithful rows and Thompson containment at G,T

The actual moving component belongs to the faithful local family. Its
earlier classification excludes the nonsolvable central seed using the
marked transvection action. The shifted central involution has a dual
natural quotient, so B.5.6 gives Thompson normality in LT and containment
in the original second parabolic core.
Source: Aschbacher--Smith 14.3.25 and 14.3.29--31, pp.1001--1003.

The universal APIs are preserved. The proofs below specialize their
source arguments without promoting a local earlier implication to a
universal statement. This extension remains above Section04.
-/

public noncomputable section

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/PlaneCentralizer.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_point_residual_uhat_nontrivial_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    ∃ k : F.Li L 1, F.uhatAction ⟨k, (F.Li_le L 1 k.property).2⟩ ≠ 1 := by
  let := chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient (by decide) L chosen.normalizes h.naturalMarking
  have hvz := (CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne).2.2
  by_contra hall
  have hk (k : F.Li L 1) : k ∈ pCore 2 (F.Li L 1) := by
    rw [← D.seedAction_ker]
    apply (F.mem_tildeAction_ker_iff _ _ _
      ((le_conjugateSpanBy V F.H).trans F.U_le_H) _ k).mpr
    intro v hv
    rw [← hvz]
    constructor
    · have hn := chosen.normalizes (F.Li_le L 1 k.property).1
      change (k : G) * v * (k : G)⁻¹ * v⁻¹ ∈ V
      exact V.mul_mem
        ((mem_normalizer_iff.mp hn v).mp hv) (V.inv_mem hv)
    · have he : F.uhatAction ⟨k, (F.Li_le L 1 k.property).2⟩ = 1 := by
        by_contra hn
        exact hall ⟨k, hn⟩
      exact (F.mem_uhatAction_ker_iff _).mp he v (le_conjugateSpanBy V F.H hv)
  obtain ⟨c, hc⟩ := BinaryLinear.OuterCyclic.BinaryTwo.derived_transitive_nonzero
    (by decide : (![1,0] : Fin 2 → ZMod 2) ≠ 0)
    (by decide : (![0,1] : Fin 2 → ZMod 2) ≠ 0)
  obtain ⟨q, hq⟩ := D.quotientEquiv.surjective c
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.Li L 1)) q
  have he : QuotientGroup.mk' (pCore 2 (F.Li L 1)) k = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (hk k)
  rw [he, map_one] at hq
  rw [← hq] at hc
  have hf := congrFun hc 0
  norm_num at hf
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_involution_large_centralizer_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥)
    {D : Type*} [Group D] [Finite D] (e : (F.H ⧸ F.uhatAction.ker) ≃* D) :
    ∃ a : D, orderOf a = 2 ∧ ∃ P : Sylow 2 D,
      (P : Subgroup D) ≤ centralizer ({a} : Set D) ∧
      ¬ IsPGroup 2 (centralizer ({a} : Set D)) := by
  obtain ⟨_, g, l, z, _, _, _, _, _, _, _, _, _, _, _, _, haH, ha, hfaith,
    ⟨helem, B, hAlt, hND, hi, hmove, halt⟩, _⟩ :=
    source_shifted_amalgam_type_at d earlier hq chosen structural alternatives F hne hseed hI
  let := helem
  let a : F.H := ⟨l⁻¹ * z * l, haH⟩
  let := chosen.elementary
  let q := e.toMonoidHom.comp (QuotientGroup.mk' F.uhatAction.ker)
  have hqs : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqa : q a ≠ 1 := by
    intro hh
    have hh' : QuotientGroup.mk' F.uhatAction.ker a = 1 :=
      e.injective (hh.trans e.map_one.symm)
    exact hfaith ((QuotientGroup.eq_one_iff _).mp hh')
  have hq2 : orderOf (q a) = 2 := by
    apply orderOf_eq_prime_iff.mpr
    refine ⟨?_, hqa⟩
    rw [← map_pow]
    have hh : a ^ 2 = 1 := Subtype.ext (orderOf_eq_prime_iff.mp ha).1
    rw [hh, map_one]
  have hcomm (b : F.H) (hb : (b : G) ∈ normalizer (V : Set G)) :
      Commute (q a) (q b) := by
    have hdim := CaseOneGeometry.seed_hat_dimension F
      (CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne).2.2
    have hc := uhat_commute_of_alternating_plane F B hND hi hdim a hfaith
      (fun x => hAlt.eq_iff.mp (halt x)) hmove.le b hb
    have hqcomm : Commute (QuotientGroup.mk' F.uhatAction.ker a)
        (QuotientGroup.mk' F.uhatAction.ker b) := by
      apply (QuotientGroup.kerLift_injective F.uhatAction)
      simpa only [map_mul, QuotientGroup.mk'_apply, QuotientGroup.kerLift_mk] using hc.eq
    exact hqcomm.map e.toMonoidHom
  let P := (T.subtype (F.invariant 1)).mapSurjective hqs
  have hPC : (P : Subgroup _) ≤ centralizer ({q a} : Set _) := by
    rintro y hy
    obtain ⟨b, hb, rfl⟩ := hy
    have hn : (b : G) ∈ normalizer (F.Vi 3 : Set G) := F.invariant 3 hb
    rw [F.last] at hn
    exact mem_centralizer_singleton_iff.mpr (hcomm b hn).symm.eq
  let f := q.comp (inclusion (show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right))
  have hp : IsPPerfect 2 (F.Li L 1) := by
    change IsPPerfect 2 ((pResidual 2 (↥(L ⊓ F.Gi 1))).map (L ⊓ F.Gi 1).subtype)
    exact isPPerfect_embedded_pResidual 2 _
  refine ⟨q a, hq2, P, hPC, ?_⟩
  intro htwo
  let f' := f.codRestrict (centralizer ({q a} : Set D)) (fun k =>
    mem_centralizer_singleton_iff.mpr
      (hcomm _ (chosen.normalizes (F.Li_le L 1 k.property).1)).symm.eq)
  have hf' := hp.hom_eq_one_of_isPGroup htwo f'
  have hf : f = 1 := by
    apply MonoidHom.ext
    intro k
    exact congrArg Subtype.val (congrArg (fun f => f k) hf')
  obtain ⟨k, hk⟩ := source_point_residual_uhat_nontrivial_at d earlier hq chosen structural alternatives F hne
  have hh : q ⟨k, (F.Li_le L 1 k.property).2⟩ = 1 := congrArg (fun f => f k) hf
  have hh' : QuotientGroup.mk' F.uhatAction.ker ⟨k, (F.Li_le L 1 k.property).2⟩ = 1 :=
    e.injective (hh.trans e.map_one.symm)
  exact hk ((QuotientGroup.eq_one_iff _).mp hh')
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SymmetricFive.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_centerless_of_symmetricFive_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (he : Nonempty ((F.H ⧸ F.uhatAction.ker) ≃* Equiv.Perm (Fin 5))) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  by_contra hI
  obtain ⟨e⟩ := he
  obtain ⟨a, ha, P, hPC, hnot⟩ := source_involution_large_centralizer_at d earlier hq chosen
    structural alternatives F hne hseed hI e
  exact hnot (Theory.SpecificGroups.SymmetricFive.involution_centralizer_isTwoGroup_of_sylow
    P a ha hPC)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/FaithfulExclusion.lean. -/
section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_seed_exclusion_of_alternatingFive_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (K : Subgroup F.H) [K.Normal]
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hout : ¬ K.map F.H.subtype ≤ normalizer (L : Set G))
    (hk : (F.uhatAction.comp K.subtype).ker = pCore 2 K)
    (hinner : (F.uhatAction.comp
      (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range ≤ K.map F.uhatAction)
    (hcard : Nat.card (F.uhatAction.comp
      (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range = 2) :
    centralLTSeed F L = ⊥ := by
  let := chosen.elementary
  by_contra hz
  obtain ⟨hWZ,hr⟩ := source_faithful_test_reduced_at d earlier hq chosen structural alternatives F
  let W := (faithfulTestModule F L).subgroupOf F.H
  let := hr.normal
  let := hr.elementary
  have hWH : faithfulTestModule F L ≤ F.H :=
    hWZ.trans ((map_subtype_le (center F.U)).trans F.U_le_H)
  have hWmap : W.map F.H.subtype = faithfulTestModule F L := map_subgroupOf_eq_of_le hWH
  have hm : ¬ K ≤ centralizer (W : Set F.H) := by
    intro hC
    apply hout
    apply le_trans ?_ (source_faithful_test_centralizer_at d earlier hq chosen structural alternatives F hz)
    rintro x ⟨k,hk,rfl⟩ z hz
    have hc := hC hk ⟨z,hWH hz⟩ hz
    exact congrArg (fun y : F.H => (y:G)) hc
  let f := F.uhatAction.comp (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)
  have hkill (z : conjugate F.ZU g) : f z = 1 := by
    let a : F.H := F.conjugateCenterActor (by decide) L chosen.normalizes g hgP z
    have hi : ∃ c : K, F.uhatAction c = F.uhatAction a := by
      obtain ⟨c,hc,hce⟩ := hinner (show f z ∈ f.range from ⟨z,rfl⟩)
      exact ⟨⟨c,hc⟩,hce⟩
    have hs : F.uhatAction a ^ 2 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨f z,⟨z,rfl⟩⟩ : f.range))
      rw [hcard] at hh
      exact congrArg Subtype.val hh
    exact reduced_alternatingFive_inner_actor_trivial W K hr hm e F.uhatAction hk a hi hs
      (source_seed_center_displacement_at d earlier hq chosen structural alternatives F hne g hgP hgH hcard
        W (hWmap ▸ hWZ) a z.property)
  have hf : f.range = ⊥ := by
    apply le_bot_iff.mp
    rintro a ⟨z,rfl⟩
    exact hkill z
  change Nat.card f.range = 2 at hcard
  rw [hf,card_bot] at hcard
  omega
theorem source_irreducible_actor_escapes_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (K : Subgroup F.H)
    (hirr : IsIrreducible ((elementaryRepresentation (p := 2) F.uhatAction).comp K.subtype)) :
    ¬ K.map F.H.subtype ≤ normalizer (L : Set G) := by
  let := chosen.elementary
  let ρ := (elementaryRepresentation (p := 2) F.uhatAction).comp K.subtype
  intro hloc
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hm := intersection_normalizer_at d earlier hq chosen structural
    (F.Vi 1) F.H hpoint (F.le_seed 1) le_rfl
  let P : Subrepresentation ρ := {
    toSubmodule := Symplectic.hatSpace F V
    apply_mem_toSubmodule k w hw := by
      have hn : ((k:F.H):G) ∈ normalizer (V : Set G) :=
        (hm ▸ (show ((k:F.H):G) ∈ F.H ⊓ normalizer (L : Set G) from
          ⟨k.val.property, hloc (mem_map_of_mem F.H.subtype k.property)⟩)).2
      obtain ⟨v,hv,he⟩ := (show w.toMul ∈ Symplectic.hatImage F V from hw)
      refine ⟨F.uAction k v,(mem_normalizer_iff.mp hn (v:G)).mp hv,?_⟩
      change QuotientGroup.mk' (center F.U) (F.uAction k v) = F.uhatAction k w.toMul
      rw [← F.uhatAction_apply_mk,he] }
  obtain ⟨htwo,hphi,hvc⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  have hp : Module.finrank (ZMod 2) P.toSubmodule = 2 := seed_hat_dimension F hvc
  have hd := (quotient_dimension F htwo hphi hvc).1
  rcases hirr.eq_bot_or_eq_top P with hb | ht
  · have hzero : Module.finrank (ZMod 2) P.toSubmodule = 0 := by
      rw [hb]
      exact finrank_bot _ _
    omega
  · have he : Module.finrank (ZMod 2) P.toSubmodule = Module.finrank (ZMod 2) (Additive F.Uhat) := by
      rw [ht]
      exact finrank_top _ _
    omega
theorem source_seed_exclusion_of_nonsolvable_rows_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat] (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (K : Subgroup F.H) [K.Normal]
    (hK : K.map F.H.subtype ∈ Chapter1.cComponentsIn F.H)
    (hirr : IsIrreducible ((elementaryRepresentation (p := 2) F.uhatAction).comp K.subtype))
    (hrows : Nat.card (K.map F.uhatAction) = 60 ∨
      Nat.card (K.map F.uhatAction) = 360 ∨ Nat.card (K.map F.uhatAction) = 6048)
    (hmark : Nat.card (K.map F.uhatAction) = 60 →
      (F.uhatAction.comp (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range ≤
        K.map F.uhatAction ∧
      Nat.card (F.uhatAction.comp
        (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range = 2) :
    centralLTSeed F L = ⊥ := by
  let := chosen.elementary
  by_contra hz
  have hout := source_irreducible_actor_escapes_at d earlier hq chosen structural alternatives F hne K hirr
  have ht := source_action_kernel_at d earlier hq chosen structural alternatives F
  have hcoreH := F.pCore_le_uhatAction_ker_of_tilde_kernel (by decide) ht
  let f := F.uhatAction.subgroupMap K
  have hcore : pCore 2 K ≤ f.ker := by
    have hp : (pCore 2 K).map K.subtype ≤ pCore 2 F.H :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map K.subtype⟩
    intro k hk
    apply Subtype.ext
    exact hcoreH (hp (mem_map_of_mem K.subtype hk))
  let q := QuotientGroup.mk' (pCore 2 K)
  let β := QuotientGroup.lift (pCore 2 K) f hcore
  have hsur : Function.Surjective β := by
    intro z
    obtain ⟨k,rfl⟩ := F.uhatAction.subgroupMap_surjective K z
    exact ⟨q k,rfl⟩
  have hdvd := card_dvd_of_surjective β hsur
  let i := K.equivMapOfInjective F.H.subtype F.H.subtype_injective
  let iq := QuotientGroup.congr (pCore 2 K) (pCore 2 (K.map F.H.subtype)) i
    (pCore_map_iso 2 i)
  obtain ⟨hc,_,_⟩ := source_faithful_component_classification_at d earlier hq chosen structural
    alternatives classification F hz hK hout
  have he : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) := by
    rcases hc with ha | hp
    · obtain ⟨e⟩ := ha
      exact ⟨iq.trans e⟩
    · obtain ⟨e⟩ := hp
      have hn : Nat.card (K ⧸ pCore 2 K) = 168 :=
        (Nat.card_congr (iq.trans e).toEquiv).trans Matrix.PSL3Two.card_PSL
      rw [hn] at hdvd
      rcases hrows with hh | hh | hh <;> rw [hh] at hdvd <;> norm_num at hdvd
  obtain ⟨e⟩ := he
  have hn : Nat.card (K ⧸ pCore 2 K) = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have h60 : Nat.card (K.map F.uhatAction) = 60 := by
    rw [hn] at hdvd
    rcases hrows with hh | hh | hh
    · exact hh
    · rw [hh] at hdvd; norm_num at hdvd
    · rw [hh] at hdvd; norm_num at hdvd
  have hinj : Function.Injective β :=
    (hsur.bijective_of_nat_card_le (by rw [hn,h60])).1
  have hk : (F.uhatAction.comp K.subtype).ker = pCore 2 K := by
    apply le_antisymm
    · intro k hk
      have he : β (q k) = 1 := Subtype.ext hk
      exact (QuotientGroup.eq_one_iff _).mp (hinj (he.trans β.map_one.symm))
    · intro k hk
      exact congrArg Subtype.val (hcore hk)
  exact hz (source_seed_exclusion_of_alternatingFive_at d earlier hq chosen structural alternatives
    F hne g hgP hgH K e hout hk (hmark h60).1 (hmark h60).2)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/AlternatingSix.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_centerless_of_alternatingSix_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (he : Nonempty ((F.H ⧸ F.uhatAction.ker) ≃* alternatingGroup (Fin 6))) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  by_contra hI
  obtain ⟨e⟩ := he
  obtain ⟨a, ha, _, _, hnot⟩ := source_involution_large_centralizer_at d earlier hq chosen
    structural alternatives F hne hseed hI e
  exact hnot (IsPGroup.of_card (n := 3) (AlternatingSix.GoldenClassGeometry.centralizer_two a ha))
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/ComponentLift.lean. -/
section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_seed_exclusion_of_dotted_row_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat] (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (row : NonsolvableSeedRow F g) : centralLTSeed F L = ⊥ := by
  obtain ⟨K,hn,hK,hi,ho,hm⟩ := source_marked_component_of_dotted_row d chosen F g hgP row
  let := hn
  exact source_seed_exclusion_of_nonsolvable_rows_at d earlier hq chosen structural alternatives
    classification F hne g hgP hgH K hK hi ho hm
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/Orbit.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_plane_parabolic_index_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) :
    (F.P L).relIndex (L ⊔ (T : Subgroup G)) = 7 := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  let β := F.naturalFlagCoordinates
  let e := naturalFlagActorEquiv β
  let f := F.naturalFlagAction L chosen.normalizes
  have hf : Function.Surjective f := F.naturalFlagAction_surjective L chosen.normalizes h.full_L_action
  have hp : (F.P L).subgroupOf (L ⊔ (T : Subgroup G)) =
      (F.naturalFlagStabilizer 2).comap f := by
    ext x
    simp only [mem_comap, f, naturalFlagAction_mem_stabilizer, mem_subgroupOf,
      P, mem_inf, mem_iInf]
    exact ⟨fun hx => hx.2 2 ⟨by decide, by decide⟩,
      fun hx => ⟨x.property, fun i hi => by
        have hi2 : i = 2 := by omega
        simpa only [hi2] using hx⟩⟩
  change ((F.P L).subgroupOf (L ⊔ (T : Subgroup G))).index = 7
  rw [hp, index_comap_of_surjective _ hf]
  rw [← index_map_of_bijective (f := e.toMonoidHom) e.bijective (F.naturalFlagStabilizer 2),
    F.naturalFlagStabilizer_map β 2]
  exact BinaryLinear.FourParabolicAction.threeSpace_hyperplane_index _
    (Module.finrank_fin_fun (ZMod 2)) (F.naturalFlagSpace_finrank β 2 (by decide))
theorem source_parabolic_eq_I₂_sylow_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    F.P L = F.I₂ L ⊔ (T : Subgroup G) := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨g, hgP, hgH⟩ := source_conjugator_at d earlier hq chosen structural F
  obtain ⟨hc, hs⟩ := F.localKernel_commutator_squares d.qtke L
    (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
    (h.sylow_normalizes_at structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape_at F alternatives)
  obtain ⟨_, _, _, _, _, _, _, _, hfactor, _⟩ := F.binary_generation (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural) hc hs
    (source_seed_geometry_at d earlier hq chosen F).2.1 hne g hgP hgH
  have hcore : (F.P L).pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 (F.P L)).le_sylow_of_normalized T
      ((F.binary_sylow_le_P L).trans ((F.P L).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (F.P L)))))
  apply le_antisymm
  · rw [hfactor]
    exact sup_le (hcore.trans le_sup_right) le_sup_left
  · exact sup_le (le_sup_right.trans hfactor.ge) (F.binary_sylow_le_P L)
theorem source_involution_stabilizer_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (e : G) (he : orderOf e = 2)
    (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L)) (heT : e ∈ sylowOmega T) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer ({e} : Set G) = F.P L := by
  let A := L ⊔ (T : Subgroup G)
  let C := A ⊓ centralizer ({e} : Set G)
  have hPC : F.P L ≤ C := by
    apply le_inf inf_le_left
    change F.P L ≤ centralizer ({e} : Set G)
    rw [source_parabolic_eq_I₂_sylow_at d earlier hq chosen structural alternatives F hne]
    apply sup_le
    · obtain ⟨z, hz, rfl⟩ := heI
      intro x hx
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hx⟩))
    · intro t ht
      exact mem_centralizer_singleton_iff.mpr (omega_centralizes_sylow heT t ht)
  have hind := relIndex_mul_relIndex (F.P L) C A hPC inf_le_left
  rw [source_plane_parabolic_index_at d earlier hq chosen F] at hind
  rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp
    (dvd_of_mul_left_eq ((F.P L).relIndex C) hind) with hindex | hindex
  · have hAC : A ≤ C := relIndex_eq_one.mp hindex
    have heU : e ∈ F.U := (map_subtype_le (center F.U))
      ((source_center_location_at d earlier hq chosen structural alternatives F hne).1 heI)
    have heZ : e ∈ centralLTSeed F L := by
      refine ⟨?_, heU⟩
      rw [centerIn_eq_inf_centralizer]
      refine ⟨mem_sup_right ((source_center_location_at d earlier hq chosen structural alternatives F hne).2.1 heI), ?_⟩
      intro x hx
      exact mem_centralizer_singleton_iff.mp (hAC hx).2
    have he1 : e = 1 := by simpa [hseed] using heZ
    simp [he1] at he
  · have hrel : (F.P L).relIndex C = 1 := by rw [hindex] at hind; omega
    exact le_antisymm (relIndex_eq_one.mp hrel) hPC
theorem source_involution_orbit_centralizer_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (e : G) (he : orderOf e = 2)
    (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L)) (heT : e ∈ sylowOmega T) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer (conjugateSpanBy (zpowers e) L : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  let A := L ⊔ (T : Subgroup G)
  let W := conjugateSpanBy (zpowers e) L
  have hr := source_involution_orbit_reduced_at d earlier hq chosen structural F e he heT
  let : (W.subgroupOf A).Normal := hr.normal
  let N := centralizer (W.subgroupOf A : Set A)
  have hWA : W ≤ A := conjugateSpanBy_le
    (zpowers_le.mpr (mem_sup_right
      ((source_center_location_at d earlier hq chosen structural alternatives F hne).2.1 heI)))
    (le_sup_left.trans A.le_normalizer)
  have heW : e ∈ W := le_conjugateSpanBy (zpowers e) L (mem_zpowers e)
  have hNmap : N.map A.subtype = A ⊓ centralizer (W : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.property, fun w hw => ?_⟩
      exact congrArg Subtype.val (ha ⟨w, hWA hw⟩ hw)
    · intro hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      intro w hw
      exact Subtype.ext (hx.2 w hw)
  have hcore : pCore 2 A ≤ N := le_centralizer_iff.mp hr.le_centralizer_pCore
  let f := F.naturalFlagAction L chosen.normalizes
  have hf : Function.Surjective f := F.naturalFlagAction_surjective L chosen.normalizes h.full_L_action
  have hk : f.ker = pCore 2 A := by
    apply map_injective A.subtype_injective
    have hfk : f.ker = (centralizer (V : Set G)).subgroupOf A := by
      exact setupSeedAction_ker A V (sup_le chosen.normalizes (h.sylow_normalizes_seed_at structural))
    rw [hfk, subgroupOf_map_subtype, inf_comm]
    exact h.centralizer_LT_at structural
  obtain ⟨c⟩ := MulAut.elementaryEight_equiv_PSL3 (show Nat.card V = 8 by simpa [F.last] using F.card 3 (by decide))
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup (MulAut V) := c.isSimpleGroup
  have hnormal : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hN : N = pCore 2 A := by
    rcases hnormal.eq_bot_or_eq_top with hbot | htop
    · exact le_antisymm (hk ▸ (map_eq_bot_iff N).mp hbot) hcore
    · have hh := congrArg (comap f) htop
      rw [comap_map_eq, comap_top, hk, sup_eq_left.mpr hcore] at hh
      have hAC : A ≤ centralizer ({e} : Set G) := by
        intro a ha
        have ham : (⟨a, ha⟩ : A) ∈ N := hh.symm ▸ mem_top _
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (ham ⟨e, hWA heW⟩ heW)).symm
      have hP : F.P L = A := by
        rw [← source_involution_stabilizer_at d earlier hq chosen structural alternatives F hne hseed e he heI heT]
        exact inf_eq_left.mpr hAC
      have hi := source_plane_parabolic_index_at d earlier hq chosen F
      rw [hP, relIndex_self] at hi
      norm_num at hi
  rw [← hNmap, hN]
  rfl
open Representation.BinaryConjugacyOrbit
theorem source_involution_span_eq_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : G) (heT : e ∈ sylowOmega T) :
    Span (L ⊔ (T : Subgroup G)) e = conjugateSpanBy (zpowers e) L := by
  exact conjugateSpanBy_sup_of_normalizes_seed _ _ _
    ((le_centralizer_iff.mp (zpowers_le.mpr (omega_centralizes_sylow heT))).trans
      (Subgroup.centralizer_le_normalizer _))
    ((SourceAssembly.At.higherRankHypothesis d earlier hq chosen).sylow_normalizes_at structural)
theorem source_involution_permutation_quotient_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (e : G) (he : orderOf e = 2)
    (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L)) (heT : e ∈ sylowOmega T) :
    Nat.card (Orbit (L ⊔ (T : Subgroup G)) e) = 7 ∧
    ∃ hE : IsElementaryAbelian 2 (Span (L ⊔ (T : Subgroup G)) e), letI := hE
      Function.Surjective (quotient (L ⊔ (T : Subgroup G)) e) ∧
      3 ≤ Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) ∧
      Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) ≤ 7 ∧
      (representation (L ⊔ (T : Subgroup G)) e).ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) ∧
      Span (L ⊔ (T : Subgroup G)) e = conjugateSpanBy (zpowers e) L ∧
      (L ⊔ (T : Subgroup G)) ⊓ centralizer (Span (L ⊔ (T : Subgroup G)) e : Set G) =
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let A := L ⊔ (T : Subgroup G)
  have hspan := source_involution_span_eq_at d earlier hq chosen structural e heT
  have hr : IsPReduced 2 ((Span A e).subgroupOf A) := by
    rw [hspan]
    exact source_involution_orbit_reduced_at d earlier hq chosen structural F e he heT
  have hWA : Span A e ≤ A := conjugateSpanBy_le_self (zpowers_le.mpr
    (mem_sup_right ((source_center_location_at d earlier hq chosen structural alternatives F hne).2.1 heI)))
  let := hr.elementary
  have hE : IsElementaryAbelian 2 (Span A e) := by
    rw [← map_subgroupOf_eq_of_le hWA]
    exact IsElementaryAbelian.map_subtype
  let := hE
  have hc : Nat.card (Orbit A e) = 7 := by
    rw [orbit_card, ← inf_relIndex_right,
      inf_comm (centralizer ({e} : Set G)),
      source_involution_stabilizer_at d earlier hq chosen structural alternatives F hne hseed e he heI heT]
    exact source_plane_parabolic_index_at d earlier hq chosen F
  refine ⟨hc, hE, quotient_surjective A e, ?_, ?_, ?_, hspan, ?_⟩
  · have hinj := Nat.card_le_card_of_injective _ (element_injective A e)
    rw [hc, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hinj
    by_contra hsmall
    change ¬ 3 ≤ Module.finrank (ZMod 2) (Additive (Span A e)) at hsmall
    have hd : Module.finrank (ZMod 2) (Additive (Span A e)) ≤ 2 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd
    omega
  · exact (dimension_le_orbit_card A e).trans hc.le
  · apply map_injective A.subtype_injective
    rw [representation_ker, subgroupOf_map_subtype, inf_comm, hspan]
    exact source_involution_orbit_centralizer_at d earlier hq chosen structural alternatives F hne hseed e he heI heT
  · rw [hspan]
    exact source_involution_orbit_centralizer_at d earlier hq chosen structural alternatives F hne hseed e he heI heT
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/FanoGeometry.lean. -/
section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open BinaryLinearThree BinaryLinearThree.FanoDecomposition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_marked_plane_action_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) :
    let := chosen.elementary
    ∃ β : Additive V ≃ₗ[ZMod 2] Vector,
    ∃ f : (L ⊔ (T : Subgroup G) : Subgroup G) →* BinaryLinearThree.Group,
      Function.Surjective f ∧
      (∀ a v, W (f a) (β v) = β (elementaryRepresentation (p := 2) (F.naturalFlagAction L chosen.normalizes) a v)) ∧
      (∀ v : V, β (Additive.ofMul v) 2 = 0 ↔ (v : G) ∈ F.Vi 2) ∧
      (F.P L).subgroupOf (L ⊔ (T : Subgroup G)) = Matrix.PSL3Two.lineParabolicSL.comap f := by
  let := chosen.elementary
  let b := F.naturalFlagCoordinates
  obtain ⟨s, hs⟩ := NaturalPlaneStabilizer.exists_matrix (F.naturalFlagSpace b 2)
    (F.naturalFlagSpace_finrank b 2 (by decide))
  let t := BinaryLinear.OuterCyclic.slEquivLinear 3 s
  let β := b.trans t.symm
  let c := (naturalFlagActorEquiv β).trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  let f := c.toMonoidHom.comp (F.naturalFlagAction L chosen.normalizes)
  have hc (a : MulAut V) (v : V) :
      W (c a) (β (Additive.ofMul v)) = β (Additive.ofMul (a v)) := by
    have he : BinaryLinear.OuterCyclic.slEquivLinear 3 (c a) = naturalFlagActorEquiv β a :=
      (BinaryLinear.OuterCyclic.slEquivLinear 3).apply_symm_apply _
    change BinaryLinear.OuterCyclic.slEquivLinear 3 (c a) (β (Additive.ofMul v)) = _
    rw [he, naturalFlagActorEquiv_intertwines]
  have hfc (a : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V) :
      W (f a) (β (Additive.ofMul v)) = β (Additive.ofMul ((F.naturalFlagAction L chosen.normalizes a) v)) := hc _ _
  have hβ (v : V) : β (Additive.ofMul v) 2 = 0 ↔ (v : G) ∈ F.Vi 2 := by
    have hh := hs (t.symm (b (Additive.ofMul v)))
    change t (t.symm (b (Additive.ofMul v))) ∈ F.naturalFlagSpace b 2 ↔
      t.symm (b (Additive.ofMul v)) ∈ NaturalPlaneStabilizer.standard at hh
    rw [LinearEquiv.apply_symm_apply, mem_naturalFlagSpace, NaturalPlaneStabilizer.mem_standard] at hh
    exact hh.symm
  refine ⟨β, f, c.surjective.comp (F.naturalFlagAction_surjective L chosen.normalizes
    (SourceAssembly.At.higherRankHypothesis d earlier hq chosen).full_L_action), fun a v => hc _ v.toMul, hβ, ?_⟩
  ext a
  have hp : (a : G) ∈ F.P L ↔ (a : G) ∈ F.Gi 2 := by
    simp only [P, mem_inf, mem_iInf]
    exact ⟨fun ha => ha.2 2 ⟨by decide, by decide⟩,
      fun ha => ⟨a.property, fun i hi => by
        have hi2 : i = 2 := by omega
        simpa only [hi2] using ha⟩⟩
  rw [mem_subgroupOf, hp, mem_comap]
  rw [← F.naturalFlagAction_mem_stabilizer L chosen.normalizes 2 a]
  rw [← NaturalPlaneStabilizer.stabilizer_standard, NaturalPlaneStabilizer.mem_stabilizer]
  change (∀ v : V, ((F.naturalFlagAction L chosen.normalizes a) v : G) ∈ F.Vi 2 ↔
    (v : G) ∈ F.Vi 2) ↔ _
  constructor
  · intro ha w
    obtain ⟨v, rfl⟩ := β.surjective w
    change W (f a) (β (Additive.ofMul v.toMul)) ∈ NaturalPlaneStabilizer.standard ↔
      β (Additive.ofMul v.toMul) ∈ NaturalPlaneStabilizer.standard
    rw [hfc, NaturalPlaneStabilizer.mem_standard, NaturalPlaneStabilizer.mem_standard, hβ, hβ]
    exact ha v.toMul
  · intro ha v
    have hh := ha (β (Additive.ofMul v))
    rw [hfc, NaturalPlaneStabilizer.mem_standard, NaturalPlaneStabilizer.mem_standard, hβ, hβ] at hh
    exact hh
local instance conjugation_at (A : Subgroup G) : MulAction A G :=
  MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp A.subtype)
local instance lineAction_at : MulAction BinaryLinearThree.Group Line := MulAction.compHom Line linePerm
local instance lineTransitive_at : MulAction.IsPretransitive BinaryLinearThree.Group Line where
  exists_smul_eq x y := by
    obtain ⟨a, ha⟩ := FanoLocalStructure.line_reachable x
    obtain ⟨b, hb⟩ := FanoLocalStructure.line_reachable y
    refine ⟨b * a⁻¹, ?_⟩
    change linePerm (b * a⁻¹) x = y
    rw [map_mul, Equiv.Perm.mul_apply, ← ha, map_inv, Equiv.Perm.inv_def,
      Equiv.symm_apply_apply, hb]
theorem source_involution_fano_lines_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (e : G) (he : orderOf e = 2)
    (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L)) (heT : e ∈ sylowOmega T) :
    letI := chosen.elementary
    ∃ β : Additive V ≃ₗ[ZMod 2] Vector,
    ∃ f : (L ⊔ (T : Subgroup G) : Subgroup G) →* BinaryLinearThree.Group,
      Function.Surjective f ∧
      (∀ a v, W (f a) (β v) = β (elementaryRepresentation (p := 2)
        (F.naturalFlagAction L chosen.normalizes) a v)) ∧
      (∀ v : V, β (Additive.ofMul v) 2 = 0 ↔ (v : G) ∈ F.Vi 2) ∧
      ∃ E : Representation.BinaryConjugacyOrbit.Orbit (L ⊔ (T : Subgroup G)) e ≃ Line,
        (∀ a x, E (Representation.BinaryConjugacyOrbit.permutation
          (L ⊔ (T : Subgroup G)) e a x) = linePerm (f a) (E x)) ∧
        E ⟨e, MulAction.mem_orbit_self e⟩ = Matrix.PSL3Two.flagLine := by
  let := chosen.elementary
  obtain ⟨β, f, hf, hβ, hplane, hP⟩ := source_marked_plane_action_at d earlier hq chosen F
  let A := L ⊔ (T : Subgroup G)
  have hs : MulAction.stabilizer A e = (F.P L).subgroupOf A := by
    ext a
    have hc := source_involution_stabilizer_at d earlier hq chosen structural alternatives F hne hseed e he heI heT
    rw [← hc]
    simp only [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    rw [and_iff_right a.property]
    change (a : G) * e * (a : G)⁻¹ = e ↔ (a : G) * e = e * (a : G)
    exact mul_inv_eq_iff_eq_mul
  have hfix : MulAction.stabilizer BinaryLinearThree.Group Matrix.PSL3Two.flagLine =
      Matrix.PSL3Two.lineParabolicSL := by
    ext g
    exact (FanoLocalStructure.ParabolicSpaces.mem_lineParabolic_iff_fixes_line g).symm
  have hs' : MulAction.stabilizer A e = Matrix.PSL3Two.lineParabolicSL.comap f := hs.trans hP
  have hm : (MulAction.stabilizer A e).map f =
      MulAction.stabilizer BinaryLinearThree.Group Matrix.PSL3Two.flagLine := by
    rw [hs', map_comap_eq_self_of_surjective hf, hfix]
  have hk : f.ker ≤ MulAction.stabilizer A e := by
    rw [hs']
    exact ker_le_comap f _
  let E₀ := MulAction.markedOrbitEquiv (MulEquiv.refl A) e (MulAction.stabilizer A e) (by simp)
  let E₁ := MulAction.surjectiveCosetEquiv (MulAction.stabilizer A e) f hf hk Matrix.PSL3Two.flagLine hm
  let E := E₀.trans E₁
  refine ⟨β, f, hf, hβ, hplane, E, ?_, ?_⟩
  · intro a x
    change E₁ (E₀ (a • x)) = f a • E₁ (E₀ x)
    rw [MulAction.markedOrbitEquiv_smul]
    exact MulAction.surjectiveCosetEquiv_smul _ _ _ _ _ _ _ _
  · change E₁ (E₀ ⟨e, MulAction.mem_orbit_self e⟩) = _
    rw [MulAction.markedOrbitEquiv_base]
    change linePerm (f 1) Matrix.PSL3Two.flagLine = Matrix.PSL3Two.flagLine
    rw [map_one, map_one, Equiv.Perm.one_apply]
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/DualQuotient.lean. -/
section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open BinaryLinearThree BinaryLinearThree.FanoDecomposition
open Representation.BinaryConjugacyOrbit
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_involution_dual_quotient_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (e : G) (he : orderOf e = 2)
    (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L)) (heT : e ∈ sylowOmega T) :
    letI := chosen.elementary
    ∃ hE : IsElementaryAbelian 2 (Span (L ⊔ (T : Subgroup G)) e), letI := hE
      (Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) = 3 ∨
       Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) = 4 ∨
       Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) = 6 ∨
       Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) = 7) ∧
      ∃ r : (representation (L ⊔ (T : Subgroup G)) e).IntertwiningMap
        (elementaryRepresentation (p := 2) (F.naturalFlagAction L chosen.normalizes)).dual,
        Function.Surjective r := by
  let := chosen.elementary
  obtain ⟨_, hE, _, hdim, _, _, _, _⟩ :=
    source_involution_permutation_quotient_at d earlier hq chosen structural alternatives F hne hseed e he heI heT
  let := hE
  obtain ⟨β, f, hf, hβ, _, E, hEq, _⟩ :=
    source_involution_fano_lines_at d earlier hq chosen structural alternatives F hne hseed e he heI heT
  let A := L ⊔ (T : Subgroup G)
  let R : Representation.Equiv (FanoLineQuotients.lineRepresentation.comp f)
      ((BinaryPermutation.representation (Orbit A e)).comp (permutation A e)) :=
    .mk (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) E) (by
      intro a
      apply LinearMap.ext
      intro c
      funext x
      change c ((linePerm (f a)).symm (E x)) = c (E ((permutation A e a).symm x))
      have hh := hEq a⁻¹ x
      simp only [map_inv, Equiv.Perm.inv_def] at hh
      exact congrArg c hh.symm)
  let q := (quotient A e).comp R.toIntertwiningMap
  have hq' : Function.Surjective q := (quotient_surjective A e).comp R.toLinearEquiv.surjective
  have hd : 1 < Module.finrank (ZMod 2) (Additive (Span A e)) := lt_of_lt_of_le (by decide : 1 < 3) hdim
  obtain ⟨r, hr⟩ := FanoLineQuotients.dual_quotient f hf (representation A e) q hq' hd
  let σ := elementaryRepresentation (p := 2) (F.naturalFlagAction L chosen.normalizes)
  let D : Representation.Equiv (W.dual.comp f) σ.dual :=
    .mk β.dualMap (by
      intro a
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro v
      change φ (W (f a)⁻¹ (β v)) = φ (β (σ a⁻¹ v))
      rw [← map_inv, hβ])
  exact ⟨hE, FanoLineQuotients.quotient_dimensions f hf (representation A e) q hq' hd,
    D.toIntertwiningMap.comp r, D.toLinearEquiv.surjective.comp hr⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/Thompson.lean. -/
section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open BinaryLinearThree Representation.BinaryConjugacyOrbit
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_involution_thompson_normal_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (e : G) (he : orderOf e = 2)
    (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L)) (heT : e ∈ sylowOmega T) :
    ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf
      (L ⊔ (T : Subgroup G))).Normal := by
  let := chosen.elementary
  let A := L ⊔ (T : Subgroup G)
  let S : Sylow 2 A := T.subtype le_sup_right
  let X := Span A e
  let E := (V ⊔ X).subgroupOf A
  let D := X.subgroupOf A
  have hXA : X ≤ A := conjugateSpanBy_le_self (zpowers_le.mpr
    (mem_sup_right ((source_center_location_at d earlier hq chosen structural alternatives F hne).2.1 heI)))
  have hVA : V ≤ A := chosen.le_sylow.trans le_sup_right
  have hEA : V ⊔ X ≤ A := sup_le hVA hXA
  have hspan := source_involution_span_eq_at d earlier hq chosen structural e heT
  have hE : IsPReduced 2 E := by
    change IsPReduced 2 ((V ⊔ Span A e).subgroupOf A)
    rw [hspan]
    exact source_seed_sup_involution_orbit_reduced_at d earlier hq chosen structural F e he heT
  have hD : IsPReduced 2 D := by
    change IsPReduced 2 ((Span A e).subgroupOf A)
    rw [hspan]
    exact source_involution_orbit_reduced_at d earlier hq chosen structural F e he heT
  let := hE.normal
  let := hE.elementary
  let := hD.normal
  let := hD.elementary
  obtain ⟨hX, _, r, hr⟩ := source_involution_dual_quotient_at d earlier hq chosen structural alternatives F hne hseed e he heI heT
  let := hX
  obtain ⟨β,f,hf,hβ,_,_⟩ := source_marked_plane_action_at d earlier hq chosen F
  let ν := elementaryRepresentation (p := 2) (F.naturalFlagAction L chosen.normalizes)
  have hfker : f.ker = (F.naturalFlagAction L chosen.normalizes).ker := by
    ext a
    change f a = 1 ↔ F.naturalFlagAction L chosen.normalizes a = 1
    constructor
    · intro ha
      apply MulEquiv.ext
      intro v
      apply Additive.ofMul.injective
      apply β.injective
      have hh := hβ a (Additive.ofMul v)
      rw [ha,map_one] at hh
      exact hh.symm
    · intro ha
      apply natural_injective
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := β.surjective v
      rw [hβ, map_one]
      change β (Additive.ofMul ((F.naturalFlagAction L chosen.normalizes a) w.toMul)) = β w
      rw [ha]
      rfl
  have hkV : f.ker = (centralizer (V : Set G)).subgroupOf A := by
    rw [hfker]
    exact setupSeedAction_ker A V (sup_le chosen.normalizes (by simpa only [F.last] using F.invariant 3))
  have hkcore : f.ker = pCore 2 A := by
    apply map_injective A.subtype_injective
    rw [hkV,subgroupOf_map_subtype,inf_comm]
    exact (SourceAssembly.At.higherRankHypothesis d earlier hq chosen).centralizer_LT_at structural
  have hkE : f.ker = centralizer (E : Set A) := by
    apply le_antisymm
    · rw [hkcore]
      exact le_centralizer_iff.mp hE.le_centralizer_pCore
    · intro a ha
      rw [hkV]
      intro v hv
      exact congrArg Subtype.val (ha ⟨v,hVA hv⟩ (mem_sup_left hv))
  have hkD : f.ker = centralizer (D : Set A) := by
    apply map_injective A.subtype_injective
    rw [hkcore, map_centralizer_subtype, map_subgroupOf_eq_of_le hXA]
    change A.pCoreIn 2 = A ⊓ centralizer (X : Set G)
    rw [show X = conjugateSpanBy (zpowers e) L from hspan]
    exact (source_involution_orbit_centralizer_at d earlier hq chosen structural alternatives F hne hseed e he heI heT).symm
  let σ := NormalElementaryQuotient.representation E f hf hkE
  let τ := NormalElementaryQuotient.representation D f hf hkD
  let b : Additive D ≃ₗ[ZMod 2] Additive X :=
    LinearEquiv.ofBijective ((subgroupOfEquivOfLe hXA).toMonoidHom.toAdditive.toZModLinearMap 2)
      (subgroupOfEquivOfLe hXA).toAdditive.bijective
  have hb (a : A) (w : Additive D) : b (τ (f a) w) = representation A e a (b w) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((τ (f a) w).toMul : A).val = (a : G) * ((w.toMul : A) : G) * (a : G)⁻¹
    exact congrArg Subtype.val (NormalElementaryQuotient.representation_apply D f hf hkD a w)
  let vmap : V →* E := (subgroupOfEquivOfLe hEA).symm.toMonoidHom.comp (inclusion le_sup_left)
  let vlin := vmap.toAdditive.toZModLinearMap 2
  let il := vlin.comp β.symm.toLinearMap
  have hi : Function.Injective il := by
    intro x y h
    apply β.symm.injective
    exact Additive.toMul.injective (Subtype.ext (congrArg (fun z : Additive E => (z.toMul : A).val) h))
  have hiv (a : A) (v : Additive V) : σ (f a) (vlin v) = vlin (ν a v) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val (NormalElementaryQuotient.representation_apply E f hf hkE a (vlin v))
  let i : W.IntertwiningMap σ := ⟨il, by
    intro g
    obtain ⟨a,rfl⟩ := hf g
    apply LinearMap.ext
    intro v
    change vlin (β.symm (W (f a) v)) = σ (f a) (vlin (β.symm v))
    rw [hiv]
    congr 1
    apply β.injective
    rw [β.apply_symm_apply, ←hβ, β.apply_symm_apply]⟩
  let jl := (inclusion (show D ≤ E from subgroupOf_mono A le_sup_right)).toAdditive.toZModLinearMap 2
  let j : τ.IntertwiningMap σ := ⟨jl, by
    intro g
    obtain ⟨a,rfl⟩ := hf g
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    change (τ (f a) w).toMul.val = (σ (f a) (jl w)).toMul.val
    rw [NormalElementaryQuotient.representation_apply,NormalElementaryQuotient.representation_apply]
    rfl⟩
  have hj : Function.Injective j := by
    intro x y h
    exact Additive.toMul.injective (Subtype.ext (congrArg (fun z : Additive E => (z.toMul : A)) h))
  let pl := β.symm.dualMap.toLinearMap.comp (r.toLinearMap.comp b.toLinearMap)
  let p : τ.IntertwiningMap W.dual := ⟨pl, by
    intro g
    obtain ⟨a,rfl⟩ := hf g
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro v
    change r (b (τ (f a) w)) (β.symm v) = r (b w) (β.symm (W (f a)⁻¹ v))
    rw [hb]
    have hrr := LinearMap.congr_fun (r.isIntertwining' a) (b w)
    have ht := congrArg (fun φ : Module.Dual (ZMod 2) (Additive V) => φ (β.symm v)) hrr
    change r (representation A e a (b w)) (β.symm v) = r (b w) (ν a⁻¹ (β.symm v)) at ht
    rw [ht]
    congr 1
    apply β.injective
    rw [β.apply_symm_apply, ←hβ, map_inv, β.apply_symm_apply]⟩
  have hp : Function.Surjective p := β.symm.dualMap.surjective.comp (hr.comp b.surjective)
  have hs : Function.Surjective (i.toLinearMap.coprod j.toLinearMap) := by
    intro x
    have hx : (x.toMul : A).val ∈ V ⊔ X := x.toMul.property
    let : IsElementaryAbelian 2 (V ⊔ X : Subgroup G) := by
      rw [←map_subgroupOf_eq_of_le hEA]
      exact IsElementaryAbelian.map_subtype
    have hc : X ≤ centralizer (V : Set G) := by
      intro w hw v hv
      exact congrArg Subtype.val (mul_comm (⟨v,mem_sup_left hv⟩ : ↥(V ⊔ X)) ⟨w,mem_sup_right hw⟩)
    change (x.toMul : A).val ∈ ((V ⊔ X : Subgroup G) : Set G) at hx
    rw [coe_mul_of_right_le_normalizer_left V X (hc.trans (Subgroup.centralizer_le_normalizer _))] at hx
    obtain ⟨v,hv,w,hw,heq⟩ := hx
    refine ⟨(β (Additive.ofMul ⟨v,hv⟩),Additive.ofMul ⟨⟨w,hXA hw⟩,hw⟩), ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (β.symm (β (Additive.ofMul ⟨v,hv⟩))).toMul.val * w = _
    rw [β.symm_apply_apply]
    exact heq
  have hn := NaturalDualSections.not_ff_of_spanning_sum σ τ i hi j hj p hp hs
  have hJ := NormalElementaryQuotient.thompson_normal_of_nonFF S E f hf hkE (hkcore ▸ pCore_isPGroup)
    (hE.le_pCore.trans ((pCore_isPGroup (p := 2) (G := A)).le_sylow_of_normal S)) hn
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) := sSup_le fun _ hA => hA.1
  have hjmap : (elementaryAbelianMaxJ (S : Subgroup A)).map A.subtype = elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective A.subtype A.subtype_injective]
    rw [show (S : Subgroup A).map A.subtype = (T : Subgroup G) from map_subgroupOf_eq_of_le le_sup_right]
  have hjeq : elementaryAbelianMaxJ (S : Subgroup A) = (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [hjmap,map_subgroupOf_eq_of_le (hJT.trans le_sup_right)]
  exact hjeq ▸ hJ
theorem source_contrary_thompson_normal_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf
      (L ⊔ (T : Subgroup G))).Normal := by
  obtain ⟨e,he,heI,heT,_,_⟩ :=
    source_center_involution_at d earlier hq chosen structural alternatives F hne hI
  exact source_involution_thompson_normal_at d earlier hq chosen structural alternatives F hne hseed e he heI heT
theorem source_contrary_thompson_le_plane_core_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ (F.I₂ L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hn := source_contrary_thompson_normal_at d earlier hq chosen structural alternatives F hne hseed hI
  have hnorm := (normal_subgroupOf_iff_le_normalizer (hJT.trans le_sup_right)).mp hn
  rw [←source_parabolic_eq_I₂_sylow_at d earlier hq chosen structural alternatives F hne]
  exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le hJT)
    (hJT.trans (F.binary_sylow_le_P L)) (inf_le_left.trans hnorm)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/NonsolvableRows.lean. -/
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
theorem source_seed_exclusion_of_six_model_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hc : Nat.card F.Uhat = 16)
    (model : Nonempty (Hdot F F.uhatAction ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 6))) : centralLTSeed F L = ⊥ := by
  let := chosen.elementary
  obtain ⟨htwo,hphi,_⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    change Nat.card F.Uhat = _ at hh
    rw [hc,Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (a := 2) (by decide)
      (show 2^4 = 2^finrank (ZMod 2) (Additive F.Uhat) from hh)).symm
  obtain ⟨g,hgP,hgH⟩ := source_conjugator_at d earlier hq chosen structural F
  exact source_seed_exclusion_of_dotted_row_at d earlier hq chosen structural alternatives
    classification F hne g hgP hgH (source_nonsolvable_six_seed_row F hd model g)
theorem source_centerless_of_alternatingSix_model_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hc : Nat.card F.Uhat = 16)
    (model : Nonempty (Hdot F F.uhatAction ≃* alternatingGroup (Fin 6))) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ :=
  source_centerless_of_alternatingSix_at d earlier hq chosen structural alternatives F hne
    (source_seed_exclusion_of_six_model_at d earlier hq chosen structural alternatives
      classification F hne hc (.inl model)) model
theorem source_seed_exclusion_of_g2_natural_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (model : ChapterG.Section11.CaseSix
      (elementaryRepresentation (p := 2) (faithfulAction F F.uhatAction))) :
    centralLTSeed F L = ⊥ := by
  obtain ⟨g,hgP,hgH⟩ := source_conjugator_at d earlier hq chosen structural F
  exact source_seed_exclusion_of_dotted_row_at d earlier hq chosen structural alternatives
    classification F hne g hgP hgH (source_nonsolvable_g2_seed_row F model g)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end
