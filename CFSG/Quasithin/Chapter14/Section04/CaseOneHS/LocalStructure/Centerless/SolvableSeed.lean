module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SeedGeometry
public import Theory.SpecificGroups.SymmetricThree.NormalInProperSubgroup
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.Action

/-!
# The solvable seed actor on the original reduced central module

Let ZL = Z(LT) intersect U and VH = <ZL^H>. Under the contrary assumption
ZL is nontrivial, the source uniqueness theorem puts C_H(VH) in M = N_G(L),
hence in the stabilizer of the original marked plane V-hat. In the earlier
S3 x S3 row, K = <(Z(U)^g)^H> has dotted image S3. Its plane stabilizer is
proper: otherwise the supplement by L1 and T would make V-hat H-invariant,
contrary to the original conjugate generation and dimension bound. That
stabilizer contains the marked involution, so any normal subgroup it contains
is trivial. Applying this to the image of C_K(VH) proves
C_K(VH) <= C_K(U-hat).

The induced surjection from K/C_K(VH) to the literal dotted K is constructed
with its evaluation on every element. A marked conjugate-center element
survives on VH, and the original central-axis bound makes its displacement
rank exactly one. Its square lies in V1^g and acts trivially on VH. Reducedness
also gives O2(H/C_H(VH)) = 1.

SolvableSeedRow records only the marked earlier quotient clauses of
14.3.23(2)(i), to be supplied by qt-d-hs-action-source. It assumes no kernel
comparison, transvection classification, or seed exclusion. The reverse kernel
containment, the identification K/C_K(VH) = S3, central splitting, and the final
solvable contradiction of 14.3.25 remain with qt-d-hs-centerless-source, as do
the remaining S6/G2(2) and Goldschmidt branches of 14.3.31. Final discharge of
the independent action premise and LocalStructure stays with
qt-d-hs-local-structure. This module does not prove centerlessness.

Source: Aschbacher--Smith, 12.8.4, 14.3.23(2)(i), and the solvable paragraph
of 14.3.25, printed pp.850,1000--1001, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem seed_normalizer_stabilizes (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat] (A : Subgroup G)
    (hA : A ≤ normalizer (V : Set G)) :
    dotImage F F.uhatAction A ≤ subspaceStabilizer (elementaryRepresentation (p := 2) (faithfulAction F F.uhatAction)) (hatSpace F V) := by
  apply le_subspaceStabilizer
  rintro a ⟨b,hb,rfl⟩ w hw
  obtain ⟨v,hv,he⟩ := (show w.toMul ∈ hatImage F V from hw)
  refine ⟨F.uAction b v,(mem_normalizer_iff.mp (hA hb) (v:G)).mp hv,?_⟩
  change QuotientGroup.mk' (center F.U) (F.uAction b v) = F.uhatAction b w.toMul
  rw [← F.uhatAction_apply_mk,he]

private theorem whole_action_not_stable (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) :
    subspaceStabilizer (elementaryRepresentation (p := 2) (faithfulAction F F.uhatAction)) (hatSpace F V) ≠ ⊤ := by
  let := chosen.elementary
  intro hall
  have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
  have hSU : V ⊔ F.ZU ≤ F.U := sup_le hVU (map_subtype_le (center F.U))
  have hn : F.H ≤ normalizer ((V ⊔ F.ZU : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro h hh s hs
    let sU : F.U := ⟨s,hSU hs⟩
    let a : F.H := ⟨h,hh⟩
    have hw : Additive.ofMul (QuotientGroup.mk' (center F.U) sU) ∈ hatSpace F V :=
      (mem_hatImage_mk_iff F V hVU sU).mpr hs
    have hst : QuotientGroup.mk' F.uhatAction.ker a ∈
        subspaceStabilizer (elementaryRepresentation (p := 2) (faithfulAction F F.uhatAction)) (hatSpace F V) := hall ▸ mem_top _
    have hm := (hst _).mpr hw
    have hm' : QuotientGroup.mk' (center F.U) (F.uAction a sU) ∈ hatImage F V := by
      rw [← F.uhatAction_apply_mk]
      exact hm
    exact (mem_hatImage_mk_iff F V hVU (F.uAction a sU)).mp hm'
  have hUS : F.U ≤ V ⊔ F.ZU := conjugateSpanBy_le le_sup_left hn
  have htop : hatSpace F V = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨v,hv⟩ := QuotientGroup.mk'_surjective (center F.U) w.toMul
    change w.toMul ∈ hatImage F V
    rw [←hv]
    exact (mem_hatImage_mk_iff F V hVU v).mpr (hUS v.property)
  obtain ⟨htwo,hphi,hvc⟩ := source_closure d earlier hq chosen structural alternatives F hne
  have hp := seed_hat_dimension F hvc
  have hd := (quotient_dimension F htwo hphi hvc).1
  rw [htop,finrank_top] at hp
  omega

/-- The literal H-normal closure of the original conjugate center, inside H. -/
@[expose] def solvableSeedActor (F : InvariantFlag T V 3) (g : G) : Subgroup F.H :=
  (conjugateSpanBy (conjugate F.ZU g) F.H).subgroupOf F.H

instance solvableSeedActor_normal (F : InvariantFlag T V 3) (g : G) :
    (solvableSeedActor F g).Normal where
  conj_mem k hk h :=
    (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy (conjugate F.ZU g) F.H h.property)
      (k : G)).mp hk

omit [Finite G] in
/-- Embedding the relative normal closure gives exactly the source subgroup K. -/
theorem solvableSeedActor_map (F : InvariantFlag T V 3)
    (hLV : L ≤ normalizer (V : Set G)) (g : G) (hgP : g ∈ F.P L) :
    (solvableSeedActor F g).map F.H.subtype = conjugateSpanBy (conjugate F.ZU g) F.H := by
  apply map_subgroupOf_eq_of_le
  apply conjugateSpanBy_le_self
  intro z hz
  exact (F.conjugateCenterActor (by decide) L hLV g hgP ⟨z,hz⟩).property

/-- The marked clauses of original 14.3.23(2)(i) needed for the seed comparison.
All groups and maps are the original hatted quotient. -/
structure SolvableSeedRow (F : InvariantFlag T V 3) (L : Subgroup G) (g : G) : Prop where
  model : Nonempty (((solvableSeedActor F g).map (QuotientGroup.mk' F.uhatAction.ker)) ≃*
    Equiv.Perm (Fin 3))
  supplement : (solvableSeedActor F g).map (QuotientGroup.mk' F.uhatAction.ker) ⊔
    dotImage F F.uhatAction (F.Li L 1) ⊔ dotImage F F.uhatAction (T : Subgroup G) = ⊤
  marked_order : Nat.card (dotImage F F.uhatAction (conjugate F.ZU g)) = 2

/-- The central test-module kernel is contained in the original hatted kernel. -/
theorem source_solvable_seed_kernel_comparison (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (row : SolvableSeedRow F L g) :
    (centralizer ((faithfulTestModule F L).subgroupOf F.H : Set F.H)).comap
        (solvableSeedActor F g).subtype ≤
      (F.uhatAction.comp (solvableSeedActor F g).subtype).ker := by
  let := chosen.elementary
  let q := QuotientGroup.mk' F.uhatAction.ker
  let K := solvableSeedActor F g
  let D := K.map q
  let P₀ := subspaceStabilizer (elementaryRepresentation (p := 2) (faithfulAction F F.uhatAction)) (hatSpace F V)
  let P := P₀.comap D.subtype
  have hLi : dotImage F F.uhatAction (F.Li L 1) ≤ P₀ :=
    seed_normalizer_stabilizes F _ ((F.Li_le L 1).trans (inf_le_left.trans chosen.normalizes))
  have hT : dotImage F F.uhatAction (T : Subgroup G) ≤ P₀ :=
    seed_normalizer_stabilizes F _ (by simpa only [F.last] using F.invariant 3)
  have hproper : P ≠ ⊤ := by
    intro he
    have hDP : D ≤ P₀ := fun a ha => show (⟨a,ha⟩ : D) ∈ P from he ▸ mem_top _
    have htop : P₀ = ⊤ := top_unique (row.supplement ▸ sup_le (sup_le hDP hLi) hT)
    exact whole_action_not_stable d earlier hq chosen structural alternatives F hne htop
  have hZD : dotImage F F.uhatAction (conjugate F.ZU g) ≤ D :=
    map_mono (comap_mono (le_conjugateSpanBy (conjugate F.ZU g) F.H))
  have hZP : dotImage F F.uhatAction (conjugate F.ZU g) ≤ P₀ :=
    seed_normalizer_stabilizes F _ ((F.conjugate_center_centralizes_seed g
      (F.P_le_seed_normalizer L chosen.normalizes hgP)).trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨z,hz1,_⟩ := (Nat.card_eq_two_iff' (1 : dotImage F F.uhatAction (conjugate F.ZU g))).mp
    row.marked_order
  let a : D := ⟨z,hZD z.property⟩
  have ha : orderOf a = 2 := by
    apply orderOf_eq_prime_iff.mpr
    constructor
    · apply Subtype.ext
      have hzpow := pow_card_eq_one' (x := z)
      rw [row.marked_order] at hzpow
      exact congrArg (fun x : dotImage F F.uhatAction (conjugate F.ZU g) =>
        (x : Hdot F F.uhatAction)) hzpow
    · intro he
      exact hz1 (Subtype.ext (congrArg (fun x : D => (x : Hdot F F.uhatAction)) he))
  let f : K →* D := (q.comp K.subtype).codRestrict D
    (fun k => mem_map_of_mem q k.property)
  have hf : Function.Surjective f := by
    rintro ⟨x,k,hk,rfl⟩
    exact ⟨⟨k,hk⟩,rfl⟩
  obtain ⟨hWZ,hr⟩ := source_faithful_test_reduced d earlier hq chosen structural alternatives F
  let W := (faithfulTestModule F L).subgroupOf F.H
  let := hr.normal
  let C := centralizer (W : Set F.H)
  let N := C.comap K.subtype
  have hWH : faithfulTestModule F L ≤ F.H :=
    hWZ.trans ((map_subtype_le (center F.U)).trans F.U_le_H)
  have hCM : C.map F.H.subtype ≤ normalizer (L : Set G) := by
    apply le_trans ?_ (source_faithful_test_centralizer d earlier hq chosen structural alternatives F hz)
    rintro x ⟨c,hc,rfl⟩ w hw
    exact congrArg Subtype.val (hc ⟨w,hWH hw⟩ hw)
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
  have hCV : C.map F.H.subtype ≤ normalizer (V : Set G) := by
    intro c hc
    exact (hm ▸ (show c ∈ F.H ⊓ normalizer (L : Set G) from
      ⟨map_subtype_le C hc,hCM hc⟩)).2
  have hCP := seed_normalizer_stabilizes F _ hCV
  let : (N.map f).Normal := Normal.map inferInstance f hf
  have hNP : N.map f ≤ P := by
    rintro _ ⟨k,hk,rfl⟩
    apply hCP
    exact ⟨k,mem_map_of_mem F.H.subtype hk,rfl⟩
  obtain ⟨e⟩ := row.model
  have hN : N.map f = ⊥ := SymmetricThree.normal_eq_bot_of_le_proper_with_involution e P (N.map f)
    hproper a (hZP z.property) ha hNP
  have hNk := (map_eq_bot_iff N).mp hN
  intro k hk
  have he : f k = 1 := hNk hk
  have he' : q (k : F.H) = 1 := congrArg Subtype.val he
  change F.uhatAction (k : F.H) = 1
  exact (QuotientGroup.eq_one_iff (k : F.H)).mp he'

/-- The actual action of K on VH has the hatted S3 image as a quotient.
The map agrees with the original quotient map on every element of K. -/
theorem source_solvable_seed_quotient (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (row : SolvableSeedRow F L g) :
    let K := solvableSeedActor F g
    let C := (centralizer ((faithfulTestModule F L).subgroupOf F.H : Set F.H)).comap K.subtype
    ∃ hn : C.Normal, letI := hn
    ∃ (f : (K ⧸ C) →* K.map (QuotientGroup.mk' F.uhatAction.ker)),
      Function.Surjective f ∧
      (∀ k : K, (f (QuotientGroup.mk' C k) : Hdot F F.uhatAction) =
        QuotientGroup.mk' F.uhatAction.ker (k : F.H)) ∧
      Nonempty ((K.map (QuotientGroup.mk' F.uhatAction.ker)) ≃* Equiv.Perm (Fin 3)) := by
  dsimp only
  let K := solvableSeedActor F g
  let W := (faithfulTestModule F L).subgroupOf F.H
  let C := (centralizer (W : Set F.H)).comap K.subtype
  have hr := (source_faithful_test_reduced d earlier hq chosen structural alternatives F).2
  let := hr.normal
  have hn : C.Normal := inferInstance
  refine ⟨hn,?_⟩
  let := hn
  let q := QuotientGroup.mk' F.uhatAction.ker
  let f : K →* K.map q := (q.comp K.subtype).codRestrict (K.map q)
    (fun k => mem_map_of_mem q k.property)
  have hf : Function.Surjective f := by
    rintro ⟨x,k,hk,rfl⟩
    exact ⟨⟨k,hk⟩,rfl⟩
  have hc : C ≤ f.ker := by
    intro k hk
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (k : F.H)).mpr
      (source_solvable_seed_kernel_comparison d earlier hq chosen structural alternatives
        F hne hz g hgP row hk)
  exact ⟨QuotientGroup.lift C f hc,
    QuotientGroup.lift_surjective_of_surjective C f hf hc,fun _ => rfl,row.model⟩

/-- A marked conjugate-center element survives as a rank-one actor on VH.
Reducedness supplies the exact core-free action quotient; no seed exclusion is assumed. -/
theorem source_solvable_seed_rank_one (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    let W := (faithfulTestModule F L).subgroupOf F.H
    ∃ hn : W.Normal, ∃ he : IsElementaryAbelian 2 W, letI := hn; letI := he
      pCore 2 (F.H ⧸ centralizer (W : Set F.H)) = ⊥ ∧
      ∃ a : F.H, (a : G) ∈ conjugate F.ZU g ∧ F.uhatAction a ≠ 1 ∧
        Module.finrank (ZMod 2)
          (NormalElementaryQuotient.originalAction W a - LinearMap.id).range = 1 ∧
        NormalElementaryQuotient.originalAction W (a ^ 2) = 1 := by
  dsimp only
  let := chosen.elementary
  obtain ⟨hWZ,hr⟩ := source_faithful_test_reduced d earlier hq chosen structural alternatives F
  let W := (faithfulTestModule F L).subgroupOf F.H
  let := hr.normal
  let := hr.elementary
  refine ⟨hr.normal,hr.elementary,hr.quotient_pCore_eq_bot,?_⟩
  let q := QuotientGroup.mk' F.uhatAction.ker
  obtain ⟨z,hz1,_⟩ := (Nat.card_eq_two_iff' (1 : dotImage F F.uhatAction (conjugate F.ZU g))).mp
    row.marked_order
  obtain ⟨a,ha,haz⟩ := z.property
  have hqa : q a ≠ 1 := by
    intro he
    exact hz1 (Subtype.ext (haz.symm.trans he))
  have hhat : F.uhatAction a ≠ 1 := by
    intro he
    exact hqa ((QuotientGroup.eq_one_iff a).mpr he)
  have haK : a ∈ solvableSeedActor F g := le_conjugateSpanBy (conjugate F.ZU g) F.H ha
  have hρ : NormalElementaryQuotient.originalAction W a ≠ 1 := by
    intro he
    have hC : a ∈ centralizer (W : Set F.H) :=
      (NormalElementaryQuotient.originalAction_kernel W).le he
    exact hhat (source_solvable_seed_kernel_comparison d earlier hq chosen structural alternatives
      F hne hz g hgP row (show (⟨a,haK⟩ : solvableSeedActor F g) ∈
        (centralizer (W : Set F.H)).comap (solvableSeedActor F g).subtype from hC))
  have hWH : faithfulTestModule F L ≤ F.H :=
    hWZ.trans ((map_subtype_le (center F.U)).trans F.U_le_H)
  have hWmap : W.map F.H.subtype ≤ F.ZU :=
    (map_subgroupOf_eq_of_le hWH).le.trans hWZ
  let f := F.uhatAction.comp (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)
  have hactor : f.range = (dotImage F F.uhatAction (conjugate F.ZU g)).map
      (faithfulAction F F.uhatAction) := by
    rw [faithfulAction_dotImage]
    ext a
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨F.conjugateCenterActor (by decide) L chosen.normalizes g hgP z,z.property,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hz⟩,rfl⟩
  have hcard : Nat.card f.range = 2 := by
    rw [hactor,card_map_of_injective (faithfulAction_injective F F.uhatAction)]
    exact row.marked_order
  have hd := source_seed_center_displacement d earlier hq chosen structural alternatives
    F hne g hgP hgH hcard W hWmap a ha
  have hn : Module.finrank (ZMod 2)
      (NormalElementaryQuotient.originalAction W a - LinearMap.id).range ≠ 0 := by
    intro he
    exact hρ (sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp he)))
  refine ⟨a,ha,hhat,le_antisymm hd (Nat.one_le_iff_ne_zero.mpr hn),?_⟩
  apply (NormalElementaryQuotient.originalAction_kernel W).ge
  have h := higherRankHypothesis d earlier hq chosen
  obtain ⟨_,hsquare⟩ := F.localKernel_commutator_squares d.qtke L
    (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
    (h.sylow_normalizes structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape F alternatives)
  have hs : (a : G) ^ 2 ∈ conjugate (F.Vi 1) g := by
    obtain ⟨b,hb,he⟩ := ha
    change (MulAut.conj g⁻¹).toMonoidHom b = (a : G) at he
    rw [←he,←map_pow]
    exact mem_map_of_mem _ (hsquare b ((map_subtype_le (center F.U)) hb))
  have hsU : (a : G) ^ 2 ∈ F.U :=
    le_conjugateSpanBy V F.H ((conjugate_point_le_plane F g
      (F.P_le_G₂ (by decide) L chosen.normalizes hgP)).trans (F.le_seed 2) hs)
  intro w hw
  apply Subtype.ext
  exact (centerIn_le_centralizer F.U (hWZ hw) _ hsU).symm

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
