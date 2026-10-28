module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SeedGeometry
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SymmetricFive
public import Theory.GroupTheory.ReducedNormal.AlternatingFiveInnerActor

/-!
# The faithful nonsolvable seed exclusion

The original marked plane is a nonzero proper subspace of U/Z(U), so an
irreducible normal component escapes M = N_G(L). If Z(LT) intersect U were
nontrivial, its reduced H-orbit would detect that component. The genuine
earlier faithful classifier restricts its two-core quotient to A₅ or PSL₃(2).
The literal action-image orders 60, 360 and 6048 eliminate PSL₃(2), A₆ and
G₂(2)′. The remaining quotient and its action kernel are constructed, not
assumed. The conjugate-center image of order two lies in this A₅ image;
the original central hyperplane bounds its displacement on the reduced
module by one. The quintic-commutator argument then makes its image trivial,
a contradiction.

The final theorems apply this seed exclusion to the existing S₅
centerlessness proof and literal LocalStructure assembly. These are
conditional on the marked earlier component: its existence, normality,
irreducibility, image order and conjugate-center marking still require
construction from 14.3.23--24. Their action alternatives belong to
qt-d-hs-action-source; component extraction and discharge remain with this
centerlessness owner. No later natural coordinates are used.
The solvable seed exclusion and remaining 14.3.31 contradictions remain
open. ActionStructure is the independent later input; its final discharge
and the whole LocalStructure theorem remain with qt-d-hs-local-structure.

Source: Aschbacher--Smith, 14.3.23--25 and 14.3.31, printed pp.999--1003,
refs/quasithin.pdf, especially the nonsolvable paragraph of p.1001.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The transvection contradiction on the actual reduced test module VH. -/
theorem source_seed_exclusion_of_alternatingFive (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
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
  obtain ⟨hWZ,hr⟩ := source_faithful_test_reduced d earlier hq chosen structural alternatives F
  let W := (faithfulTestModule F L).subgroupOf F.H
  let := hr.normal
  let := hr.elementary
  have hWH : faithfulTestModule F L ≤ F.H :=
    hWZ.trans ((map_subtype_le (center F.U)).trans F.U_le_H)
  have hWmap : W.map F.H.subtype = faithfulTestModule F L := map_subgroupOf_eq_of_le hWH
  have hm : ¬ K ≤ centralizer (W : Set F.H) := by
    intro hC
    apply hout
    apply le_trans ?_ (source_faithful_test_centralizer d earlier hq chosen structural alternatives F hz)
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
      (source_seed_center_displacement d earlier hq chosen structural alternatives F hne g hgP hgH hcard
        W (hWmap ▸ hWZ) a z.property)
  have hf : f.range = ⊥ := by
    apply le_bot_iff.mp
    rintro a ⟨z,rfl⟩
    exact hkill z
  change Nat.card f.range = 2 at hcard
  rw [hf,card_bot] at hcard
  omega

/-- An irreducible component of the original hatted action cannot lie in M:
the original marked plane would then be a nonzero proper invariant subspace. -/
theorem source_irreducible_actor_escapes (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (K : Subgroup F.H)
    (hirr : IsIrreducible ((elementaryRepresentation (p := 2) F.uhatAction).comp K.subtype)) :
    ¬ K.map F.H.subtype ≤ normalizer (L : Set G) := by
  let := chosen.elementary
  let ρ := (elementaryRepresentation (p := 2) F.uhatAction).comp K.subtype
  intro hloc
  have unique : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S A hA
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hA
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hm := intersection_normalizer d earlier hq chosen ⟨structural,unique,alternatives⟩
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
  obtain ⟨htwo,hphi,hvc⟩ := source_closure d earlier hq chosen structural alternatives F hne
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

/-- The genuine earlier faithful classifier eliminates the other two
nonsolvable component orders and supplies the actual A₅ quotient and kernel. -/
theorem source_seed_exclusion_of_nonsolvable_rows (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
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
  have hout := source_irreducible_actor_escapes d earlier hq chosen structural alternatives F hne K hirr
  have unique : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S A hA
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hA
  have ht := source_action_kernel d earlier hq chosen ⟨structural,unique,alternatives⟩ F
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
  obtain ⟨hc,_,_⟩ := source_faithful_component_classification d earlier hq chosen structural
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
  exact hz (source_seed_exclusion_of_alternatingFive d earlier hq chosen structural alternatives
    F hne g hgP hgH K e hout hk (hmark h60).1 (hmark h60).2)

/-- Feed the source nonsolvable-row exclusion to the actual S₅ centerlessness branch. -/
theorem source_centerless_of_nonsolvable_symmetricFive (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
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
        (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range = 2)
    (hsym : Nonempty ((F.H ⧸ F.uhatAction.ker) ≃* Equiv.Perm (Fin 5))) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ :=
  source_centerless_of_symmetricFive d earlier hq chosen structural alternatives F hne
    (source_seed_exclusion_of_nonsolvable_rows d earlier hq chosen structural alternatives
      classification F hne g hgP hgH K hK hirr hrows hmark) hsym

/-- The literal LocalStructure consumer of the nonsolvable seed argument. -/
theorem localStructure_of_nonsolvable_symmetricFive_action (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
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
        (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range = 2)
    (hsym : Nonempty ((F.H ⧸ F.uhatAction.ker) ≃* Equiv.Perm (Fin 5)))
    (action : ActionStructure F) :
    LocalStructure L F :=
  localStructure_of_centerless_action d earlier hq chosen structural alternatives F hne
    (source_centerless_of_nonsolvable_symmetricFive d earlier hq chosen structural alternatives
      classification F hne g hgP hgH K hK hirr hrows hmark hsym) action

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
