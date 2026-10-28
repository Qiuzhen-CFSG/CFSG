module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.Nonsolvable

/-!
# The solvable central-seed exclusion at G,T

The literal S3 by S3 action constructs the normal cubic and its marked
transvection plane. Comparing the original faithful-test, central and
hatted action kernels proves central splitting and excludes the nonzero
central LT seed. No marked solvable-row hypothesis remains in the final
seed theorem.
Source: Aschbacher--Smith 14.3.25, printed p.1001.

The universal APIs are preserved. The proofs below specialize their
source arguments without promoting a local earlier implication to a
universal statement. This extension remains above Section04.
-/

public noncomputable section

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableSeed.lean. -/
section
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
private theorem solvableSeed_seed_normalizer_stabilizes_at (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat] (A : Subgroup G)
    (hA : A ≤ normalizer (V : Set G)) :
    dotImage F F.uhatAction A ≤ subspaceStabilizer (elementaryRepresentation (p := 2) (faithfulAction F F.uhatAction)) (hatSpace F V) := by
  apply le_subspaceStabilizer
  rintro a ⟨b,hb,rfl⟩ w hw
  obtain ⟨v,hv,he⟩ := (show w.toMul ∈ hatImage F V from hw)
  refine ⟨F.uAction b v,(mem_normalizer_iff.mp (hA hb) (v:G)).mp hv,?_⟩
  change QuotientGroup.mk' (center F.U) (F.uAction b v) = F.uhatAction b w.toMul
  rw [← F.uhatAction_apply_mk,he]
private theorem solvableSeed_whole_action_not_stable_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
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
  obtain ⟨htwo,hphi,hvc⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  have hp := seed_hat_dimension F hvc
  have hd := (quotient_dimension F htwo hphi hvc).1
  rw [htop,finrank_top] at hp
  omega
theorem source_solvable_seed_kernel_comparison_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
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
    solvableSeed_seed_normalizer_stabilizes_at F _ ((F.Li_le L 1).trans (inf_le_left.trans chosen.normalizes))
  have hT : dotImage F F.uhatAction (T : Subgroup G) ≤ P₀ :=
    solvableSeed_seed_normalizer_stabilizes_at F _ (by simpa only [F.last] using F.invariant 3)
  have hproper : P ≠ ⊤ := by
    intro he
    have hDP : D ≤ P₀ := fun a ha => show (⟨a,ha⟩ : D) ∈ P from he ▸ mem_top _
    have htop : P₀ = ⊤ := top_unique (row.supplement ▸ sup_le (sup_le hDP hLi) hT)
    exact solvableSeed_whole_action_not_stable_at d earlier hq chosen structural alternatives F hne htop
  have hZD : dotImage F F.uhatAction (conjugate F.ZU g) ≤ D :=
    map_mono (comap_mono (le_conjugateSpanBy (conjugate F.ZU g) F.H))
  have hZP : dotImage F F.uhatAction (conjugate F.ZU g) ≤ P₀ :=
    solvableSeed_seed_normalizer_stabilizes_at F _ ((F.conjugate_center_centralizes_seed g
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
  obtain ⟨hWZ,hr⟩ := source_faithful_test_reduced_at d earlier hq chosen structural alternatives F
  let W := (faithfulTestModule F L).subgroupOf F.H
  let := hr.normal
  let C := centralizer (W : Set F.H)
  let N := C.comap K.subtype
  have hWH : faithfulTestModule F L ≤ F.H :=
    hWZ.trans ((map_subtype_le (center F.U)).trans F.U_le_H)
  have hCM : C.map F.H.subtype ≤ normalizer (L : Set G) := by
    apply le_trans ?_ (source_faithful_test_centralizer_at d earlier hq chosen structural alternatives F hz)
    rintro x ⟨c,hc,rfl⟩ w hw
    exact congrArg Subtype.val (hc ⟨w,hWH hw⟩ hw)
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hm := intersection_normalizer_at d earlier hq chosen structural
    (F.Vi 1) F.H hpoint (F.le_seed 1) le_rfl
  have hCV : C.map F.H.subtype ≤ normalizer (V : Set G) := by
    intro c hc
    exact (hm ▸ (show c ∈ F.H ⊓ normalizer (L : Set G) from
      ⟨map_subtype_le C hc,hCM hc⟩)).2
  have hCP := solvableSeed_seed_normalizer_stabilizes_at F _ hCV
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
theorem source_solvable_seed_quotient_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
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
  have hr := (source_faithful_test_reduced_at d earlier hq chosen structural alternatives F).2
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
      (source_solvable_seed_kernel_comparison_at d earlier hq chosen structural alternatives
        F hne hz g hgP row hk)
  exact ⟨QuotientGroup.lift C f hc,
    QuotientGroup.lift_surjective_of_surjective C f hf hc,fun _ => rfl,row.model⟩
theorem source_solvable_seed_rank_one_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
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
  obtain ⟨hWZ,hr⟩ := source_faithful_test_reduced_at d earlier hq chosen structural alternatives F
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
    exact hhat (source_solvable_seed_kernel_comparison_at d earlier hq chosen structural alternatives
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
  have hd := source_seed_center_displacement_at d earlier hq chosen structural alternatives
    F hne g hgP hgH hcard W hWmap a ha
  have hn : Module.finrank (ZMod 2)
      (NormalElementaryQuotient.originalAction W a - LinearMap.id).range ≠ 0 := by
    intro he
    exact hρ (sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp he)))
  refine ⟨a,ha,hhat,le_antisymm hd (Nat.one_le_iff_ne_zero.mpr hn),?_⟩
  apply (NormalElementaryQuotient.originalAction_kernel W).ge
  have h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨_,hsquare⟩ := F.localKernel_commutator_squares d.qtke L
    (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
    (h.sylow_normalizes_at structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape_at F alternatives)
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

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableSeedAction.lean. -/
section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_solvable_marked_kernel_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (a : F.H) (ha : (a : G) ∈ conjugate F.ZU g) (hk : F.uhatAction a = 1) :
    a ∈ centralizer ((faithfulTestModule F L).subgroupOf F.H : Set F.H) := by
  let := chosen.elementary
  have hpar := (source_parabolic_action_at d earlier hq chosen structural alternatives
    F hne g hgP hgH).2.1
  have hx : (a : G) ∈ F.xHatKernel g (F.P_le_G₂ (by decide) L chosen.normalizes hgP) :=
    (F.mem_xHatKernel _ _ _).mpr ⟨F.conjugate_ZU_le_X g ha,
      (F.mem_uhatAction_ker_iff _).mp hk⟩
  rw [hpar] at hx
  have hWZ := (source_faithful_test_reduced_at d earlier hq chosen structural alternatives F).1
  intro w hw
  apply Subtype.ext
  exact (centerIn_le_centralizer F.U (hWZ hw) a hx.1.1).symm
theorem source_solvable_marked_image_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (row : SolvableSeedRow F L g)
    (a : F.H) (ha : (a : G) ∈ conjugate F.ZU g) (hneA : F.uhatAction a ≠ 1)
    (hn : ((faithfulTestModule F L).subgroupOf F.H).Normal) :
    letI := hn
    let q := QuotientGroup.mk' (centralizer
      ((faithfulTestModule F L).subgroupOf F.H : Set F.H))
    ((conjugate F.ZU g).subgroupOf F.H).map q = zpowers (q a) := by
  let := hn
  dsimp only
  let q := QuotientGroup.mk' (centralizer
    ((faithfulTestModule F L).subgroupOf F.H : Set F.H))
  let r := QuotientGroup.mk' F.uhatAction.ker
  let D := dotImage F F.uhatAction (conjugate F.ZU g)
  let aD : D := ⟨r a,mem_map_of_mem r ha⟩
  have haD : aD ≠ 1 := by
    intro he
    exact hneA ((QuotientGroup.eq_one_iff a).mp (congrArg Subtype.val he))
  obtain ⟨z,hz,hunique⟩ := (Nat.card_eq_two_iff' (1 : D)).mp row.marked_order
  have allD (b : D) : b = 1 ∨ b = aD := by
    by_cases hb : b = 1
    · exact Or.inl hb
    · exact Or.inr ((hunique b hb).trans (hunique aD haD).symm)
  apply le_antisymm
  · rintro _ ⟨b,hb,rfl⟩
    rcases allD ⟨r b,mem_map_of_mem r hb⟩ with he | he
    · have hk : F.uhatAction b = 1 :=
        (QuotientGroup.eq_one_iff b).mp (congrArg Subtype.val he)
      have hc := source_solvable_marked_kernel_at d earlier hq chosen structural alternatives
        F hne g hgP hgH b hb hk
      rw [show q b = 1 from (QuotientGroup.eq_one_iff b).mpr hc]
      exact one_mem _
    · have he' : r b = r a := congrArg Subtype.val he
      have hk : F.uhatAction (b * a⁻¹) = 1 := by
        change b * a⁻¹ ∈ F.uhatAction.ker
        apply (QuotientGroup.eq_one_iff (b * a⁻¹)).mp
        change r (b * a⁻¹) = 1
        rw [map_mul,map_inv,he',mul_inv_cancel]
      have hc := source_solvable_marked_kernel_at d earlier hq chosen structural alternatives
        F hne g hgP hgH (b * a⁻¹) ((conjugate F.ZU g).mul_mem hb
          ((conjugate F.ZU g).inv_mem ha)) hk
      have hqa : q b = q a := by
        have hh := (QuotientGroup.eq_one_iff (b * a⁻¹)).mpr hc
        change q (b * a⁻¹) = 1 at hh
        rw [map_mul,map_inv,mul_inv_eq_one] at hh
        exact hh
      rw [hqa]
      exact mem_zpowers _
  · exact zpowers_le.mpr (mem_map_of_mem q ha)
theorem source_solvable_seed_normal_closure_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (row : SolvableSeedRow F L g)
    (a : F.H) (ha : (a : G) ∈ conjugate F.ZU g) (hneA : F.uhatAction a ≠ 1)
    (hn : ((faithfulTestModule F L).subgroupOf F.H).Normal) :
    letI := hn
    let q := QuotientGroup.mk' (centralizer
      ((faithfulTestModule F L).subgroupOf F.H : Set F.H))
    (solvableSeedActor F g).map q = normalClosure ({q a} : Set _) := by
  let := hn
  dsimp only
  let A := (conjugate F.ZU g).subgroupOf F.H
  have hAH : conjugate F.ZU g ≤ F.H := by
    intro z hz
    exact (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP ⟨z,hz⟩).property
  have hK : solvableSeedActor F g = normalClosure (A : Set F.H) :=
    (normalClosure_subgroupOf_eq_conjugateSpanBy _ _ hAH).symm
  let q := QuotientGroup.mk' (centralizer
    ((faithfulTestModule F L).subgroupOf F.H : Set F.H))
  rw [hK, map_normalClosure (A : Set F.H) q (QuotientGroup.mk'_surjective _)]
  have hA := source_solvable_marked_image_at d earlier hq chosen structural alternatives
    F hne g hgP hgH row a ha hneA hn
  rw [← Subgroup.coe_map]
  rw [hA]
  apply le_antisymm
  · apply normalClosure_le_normal
    exact zpowers_le.mpr (subset_normalClosure (Set.mem_singleton (q a)))
  · apply normalClosure_mono
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact mem_zpowers (q a)
private theorem solvableSeedAction_pointNormalizer_sqtk_at (d : Counterexample T L)
    (chosen : ChosenModule T L V) (F : InvariantFlag T V 3) :
    IsSQTK KnownSimple.IsKnownSimple F.H := by
  let := chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
  apply d.qtke.twoLocal_sqtk
  refine ⟨F.Vi 1, ?_, IsElementaryAbelian.isPGroup 2 (F.Vi 1), rfl⟩
  intro he
  have hc := F.card 1 (by decide)
  rw [he,card_bot] at hc
  norm_num at hc
theorem source_solvable_seed_classification_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    let W := (faithfulTestModule F L).subgroupOf F.H
    ∃ hn : W.Normal, ∃ he : IsElementaryAbelian 2 W, letI := hn; letI := he
    let C := centralizer (W : Set F.H)
    let q := QuotientGroup.mk' C
    let σ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let D := (solvableSeedActor F g).map q
    FFHypothesis KnownSimple.IsKnownSimple (σ.comp D.subtype) ∧
      NontrivialAdequateAlternative (σ.comp D.subtype) := by
  dsimp only
  obtain ⟨hn,he,hcore,a,ha,hhat,hr,hsq⟩ := source_solvable_seed_rank_one_at d earlier hq chosen
    structural alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  refine ⟨hn,he,?_⟩
  let W := (faithfulTestModule F L).subgroupOf F.H
  let C := centralizer (W : Set F.H)
  let q := QuotientGroup.mk' C
  let σ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let D := (solvableSeedActor F g).map q
  have hD := source_solvable_seed_normal_closure_at d earlier hq chosen structural alternatives
    F hne g hgP hgH row a ha hhat hn
  have hf : Function.Injective σ := NormalElementaryQuotient.representation_injective W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  have hσ (b : F.H) : σ (q b) = NormalElementaryQuotient.originalAction W b := by
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) b w).trans
        (NormalElementaryQuotient.originalAction_apply W b w).symm
  have hr' : Module.finrank (ZMod 2) (σ (q a) - LinearMap.id).range = 1 := by
    rw [hσ]
    exact hr
  have ht : q a ^ 2 = 1 := by
    apply hf
    rw [←map_pow,map_one,hσ]
    exact hsq
  have hneQ : q a ≠ 1 := by
    intro hqa
    rw [hqa,map_one,Module.End.one_eq_id,sub_self,LinearMap.range_zero,finrank_bot] at hr'
    omega
  have htwo : pCore 2 D = ⊥ := by
    have hl : (pCore 2 D).map D.subtype ≤ pCore 2 (F.H ⧸ C) :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map D.subtype⟩
    rw [hcore] at hl
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro x hx
    exact Subtype.ext (hl (mem_map_of_mem D.subtype hx))
  have hgen : offenderSubgroup (σ.comp D.subtype) = ⊤ := by
    rw [show D = normalClosure ({q a} : Set _) from hD]
    exact normalClosure_offenderSubgroup_of_rank_one σ (q a) ht hneQ hr'.le
  let cover : SQTKQuotient KnownSimple.IsKnownSimple (F.H ⧸ C) := {
    Cover := F.H
    kernel := C
    sqtk := solvableSeedAction_pointNormalizer_sqtk_at d chosen F
    equiv := MulEquiv.refl _ }
  have hff : FFHypothesis KnownSimple.IsKnownSimple (σ.comp D.subtype) :=
    ⟨inferInstance,hf.comp D.subtype_injective,htwo,hgen,⟨cover.subgroup D⟩⟩
  have hnon : Nontrivial D := by
    apply (Subgroup.nontrivial_iff_ne_bot D).mpr
    intro hd
    have hm : q a ∈ D := by
      rw [show D = normalClosure ({q a} : Set _) from hD]
      exact subset_normalClosure (Set.mem_singleton _)
    exact hneQ (hd.le hm)
  let := hnon
  exact ⟨hff,nontrivialAdequateAlternative_knownSimple _ hff⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableSeedSplitting.lean. -/
section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
private theorem solvableSeedSplitting_symmetricThree_case_at {D X : Type*} [Group D] [Finite D]
    [AddCommGroup X] [Module (ZMod 2) X] (ρ : Representation (ZMod 2) D X)
    (hc : NontrivialAdequateAlternative ρ) (e : D ≃* Equiv.Perm (Fin 3)) :
    Nonempty (SymmetricThreeCase ρ) := by
  have hcard : Nat.card D = 6 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hr : primeRank 3 D ≤ 1 := primeRank_le_of_prime_pow_not_dvd (by rw [hcard]; decide)
  rcases hc.at_three_rank_le_one hr with ⟨hq,_⟩ | hs
  · let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective
    let := hq
    let : IsSimpleGroup (generalizedFitting D ⧸ center (generalizedFitting D)) :=
      IsQuasisimple.simple
    let : Nontrivial (generalizedFitting D) :=
      (QuotientGroup.mk'_surjective (center (generalizedFitting D))).nontrivial
    exact (Group.IsPerfect.not_isSolvable (generalizedFitting D) inferInstance).elim
  · exact hs
theorem source_solvable_seed_kernel_eq_of_model_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (row : SolvableSeedRow F L g)
    (hn : ((faithfulTestModule F L).subgroupOf F.H).Normal)
    (model : letI := hn
      Nonempty (((solvableSeedActor F g).map (QuotientGroup.mk' (centralizer
        ((faithfulTestModule F L).subgroupOf F.H : Set F.H)))) ≃* Equiv.Perm (Fin 3))) :
    (centralizer ((faithfulTestModule F L).subgroupOf F.H : Set F.H)).comap
        (solvableSeedActor F g).subtype =
      (F.uhatAction.comp (solvableSeedActor F g).subtype).ker := by
  let := hn
  let K := solvableSeedActor F g
  let C := (centralizer ((faithfulTestModule F L).subgroupOf F.H : Set F.H)).comap K.subtype
  obtain ⟨hnC,f,hf,heval,hemodel⟩ := source_solvable_seed_quotient_at d earlier hq chosen
    structural alternatives F hne hz g hgP row
  let := hnC
  obtain ⟨e,he⟩ := solvable_seed_action_equiv (L := L) F g hn
  obtain ⟨em⟩ := model
  obtain ⟨ed⟩ := hemodel
  have hc : Nat.card (K ⧸ C) = Nat.card (K.map (QuotientGroup.mk' F.uhatAction.ker)) :=
    Nat.card_congr ((e.trans em).trans ed.symm).toEquiv
  have hi : Function.Injective f := (hf.bijective_of_nat_card_le hc.le).1
  apply le_antisymm
  · exact source_solvable_seed_kernel_comparison_at d earlier hq chosen structural alternatives
      F hne hz g hgP row
  · intro k hk
    have hfq : f (QuotientGroup.mk' C k) = 1 := by
      apply Subtype.ext
      rw [heval]
      exact (QuotientGroup.eq_one_iff (k : F.H)).mpr hk
    exact (QuotientGroup.eq_one_iff k).mp (hi (hfq.trans f.map_one.symm))
theorem source_solvable_seed_plane_of_model_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g)
    (hn : ((faithfulTestModule F L).subgroupOf F.H).Normal)
    (he : IsElementaryAbelian 2 ((faithfulTestModule F L).subgroupOf F.H))
    (model : letI := hn
      Nonempty (((solvableSeedActor F g).map (QuotientGroup.mk' (centralizer
        ((faithfulTestModule F L).subgroupOf F.H : Set F.H)))) ≃* Equiv.Perm (Fin 3))) :
    letI := hn; letI := he
    let W := (faithfulTestModule F L).subgroupOf F.H
    let K := solvableSeedActor F g
    IsCompl (NormalElementaryQuotient.commutatorSpace W K)
      (fixedSpace (NormalElementaryQuotient.originalAction W) K) ∧
      Module.finrank (ZMod 2) (NormalElementaryQuotient.commutatorSpace W K) = 2 := by
  let := hn
  let := he
  dsimp only
  let W := (faithfulTestModule F L).subgroupOf F.H
  let K := solvableSeedActor F g
  let C := centralizer (W : Set F.H)
  let q := QuotientGroup.mk' C
  let D := K.map q
  let σ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨_,_,_,hc⟩ := source_solvable_seed_classification_at d earlier hq chosen structural
    alternatives F hne hz g hgP hgH row
  obtain ⟨em⟩ := model
  obtain ⟨cs⟩ := solvableSeedSplitting_symmetricThree_case_at (σ.comp D.subtype) hc em
  have hσ : σ.comp q = NormalElementaryQuotient.originalAction W := by
    apply MonoidHom.ext
    intro b
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) b w).trans
        (NormalElementaryQuotient.originalAction_apply W b w).symm
  have hm : ChapterB.QuasisimpleSource.moved (σ.comp D.subtype) ⊤ =
      NormalElementaryQuotient.commutatorSpace W K := by
    rw [NormalElementaryQuotient.original_moved_space,←hσ,subspaceCommutator_comp_map]
    change subspaceCommutator (σ.comp D.subtype) ⊤ ⊤ = _
    rw [subspaceCommutator_comp_map,← MonoidHom.range_eq_map,Subgroup.range_subtype]
  have hfix : Representation.invariants (σ.comp D.subtype) =
      fixedSpace (NormalElementaryQuotient.originalAction W) K := by
    rw [←hσ,fixedSpace_comp_map]
    rfl
  change IsCompl (NormalElementaryQuotient.commutatorSpace W K)
    (fixedSpace (NormalElementaryQuotient.originalAction W) K) ∧
    Module.finrank (ZMod 2) (NormalElementaryQuotient.commutatorSpace W K) = 2
  rw [←hm,←hfix]
  exact ⟨cs.decomposition,cs.dimension⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableSeedRecognition.lean. -/
section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_solvable_seed_action_quotient_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (row : SolvableSeedRow F L g)
    (hn : ((faithfulTestModule F L).subgroupOf F.H).Normal) :
    letI := hn
    let K := solvableSeedActor F g
    let q := QuotientGroup.mk' (centralizer
      ((faithfulTestModule F L).subgroupOf F.H : Set F.H))
    let r := QuotientGroup.mk' F.uhatAction.ker
    let D := K.map q
    ∃ (e : K.map r ≃* Equiv.Perm (Fin 3)) (f : D →* Equiv.Perm (Fin 3)),
      Function.Surjective f ∧
      (∀ k : K, f ⟨q k,mem_map_of_mem q k.property⟩ =
        e ⟨r k,mem_map_of_mem r k.property⟩) ∧
      (f.ker.map D.subtype).Normal := by
  let := hn
  dsimp only
  let K := solvableSeedActor F g
  let C := centralizer ((faithfulTestModule F L).subgroupOf F.H : Set F.H)
  let q := QuotientGroup.mk' C
  let r := QuotientGroup.mk' F.uhatAction.ker
  let D := K.map q
  obtain ⟨hnC,f₀,hf₀,heval,em⟩ := source_solvable_seed_quotient_at d earlier hq chosen
    structural alternatives F hne hz g hgP row
  let := hnC
  obtain ⟨e₀,he₀⟩ := solvable_seed_action_equiv (L := L) F g hn
  obtain ⟨e⟩ := em
  let f : D →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (f₀.comp e₀.symm.toMonoidHom)
  have hf : Function.Surjective f := e.surjective.comp (hf₀.comp e₀.symm.surjective)
  have he (k : K) : f ⟨q k,mem_map_of_mem q k.property⟩ =
      e ⟨r k,mem_map_of_mem r k.property⟩ := by
    have heD : (⟨q k,mem_map_of_mem q k.property⟩ : D) =
        e₀ (QuotientGroup.mk' (C.comap K.subtype) k) := Subtype.ext (he₀ k).symm
    change e (f₀ (e₀.symm _)) = _
    rw [heD,e₀.symm_apply_apply]
    apply congrArg e
    exact Subtype.ext (heval k)
  refine ⟨e,f,hf,he,?_⟩
  have hk : f.ker.map D.subtype = (K ⊓ F.uhatAction.ker).map q := by
    apply le_antisymm
    · rintro x ⟨b,hb,rfl⟩
      obtain ⟨k,hk,hqb⟩ := b.property
      let kK : K := ⟨k,hk⟩
      have hbe : b = ⟨q k,mem_map_of_mem q hk⟩ := Subtype.ext hqb.symm
      have hh : e ⟨r k,mem_map_of_mem r hk⟩ = 1 := by
        rw [←he kK,←hbe]
        exact hb
      have hkhat : k ∈ F.uhatAction.ker := by
        apply (QuotientGroup.eq_one_iff k).mp
        exact congrArg Subtype.val (e.injective (hh.trans e.map_one.symm))
      exact ⟨k,⟨hk,hkhat⟩,hqb⟩
    · rintro x ⟨k,⟨hk,hkhat⟩,rfl⟩
      refine ⟨⟨q k,mem_map_of_mem q hk⟩,?_,rfl⟩
      change f ⟨q k,mem_map_of_mem q hk⟩ = 1
      rw [he ⟨k,hk⟩]
      have hh : (⟨r k,mem_map_of_mem r hk⟩ : K.map r) = 1 :=
        Subtype.ext ((QuotientGroup.eq_one_iff k).mpr hkhat)
      rw [hh,map_one]
  rw [hk]
  exact Normal.map inferInstance q (QuotientGroup.mk'_surjective C)
theorem source_solvable_seed_symmetricThree_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    let W := (faithfulTestModule F L).subgroupOf F.H
    ∃ hn : W.Normal, ∃ he : IsElementaryAbelian 2 W, letI := hn; letI := he
    let C := centralizer (W : Set F.H)
    let q := QuotientGroup.mk' C
    let σ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let D := (solvableSeedActor F g).map q
    Nonempty (SymmetricThreeCase (σ.comp D.subtype)) := by
  dsimp only
  obtain ⟨hn,he,hcore,a,ha,hhat,hr,hsq⟩ := source_solvable_seed_rank_one_at d earlier hq chosen
    structural alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  refine ⟨hn,he,?_⟩
  let W := (faithfulTestModule F L).subgroupOf F.H
  let C := centralizer (W : Set F.H)
  let q := QuotientGroup.mk' C
  let σ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let D := (solvableSeedActor F g).map q
  obtain ⟨_,_,hf,hc⟩ := source_solvable_seed_classification_at d earlier hq chosen structural
    alternatives F hne hz g hgP hgH row
  obtain ⟨e,f,hf',heval,hkernel⟩ := source_solvable_seed_action_quotient_at d earlier hq chosen
    structural alternatives F hne hz g hgP row hn
  have hD := source_solvable_seed_normal_closure_at d earlier hq chosen structural alternatives
    F hne g hgP hgH row a ha hhat hn
  have haK : a ∈ solvableSeedActor F g := le_conjugateSpanBy _ _ ha
  have haD : q a ∈ D := mem_map_of_mem q haK
  have hσ (b : F.H) : σ (q b) = NormalElementaryQuotient.originalAction W b := by
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) b w).trans
        (NormalElementaryQuotient.originalAction_apply W b w).symm
  have ht2 : q a ^ 2 = 1 := by
    apply NormalElementaryQuotient.representation_injective W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    rw [←map_pow,map_one,hσ]
    exact hsq
  have htf : f ⟨q a,haD⟩ ≠ 1 := by
    rw [heval ⟨a,haK⟩]
    intro hh
    have hh' := congrArg Subtype.val (e.injective (hh.trans e.map_one.symm))
    exact hhat ((QuotientGroup.eq_one_iff a).mp hh')
  have hr' : Module.finrank (ZMod 2)
      ((σ.comp D.subtype) ⟨q a,haD⟩ - LinearMap.id).range ≤ 1 := by
    change Module.finrank (ZMod 2) (σ (q a) - LinearMap.id).range ≤ 1
    rw [hσ]
    exact hr.le
  cases hc with
  | quasisimple hquasi c =>
      let := hquasi
      exact (c.no_symmetricThree_quotient f hf').elim
  | symmetricThree c => exact ⟨c⟩
  | twoFactors c =>
      exact (c.no_normalClosure_symmetricThree_quotient D (q a) haD hD
        (σ.comp D.subtype) hf.twoCore f hf' hkernel ht2 htf hr').elim
  | outerSixThree c =>
      have hqa : q a ≠ 1 := by
        intro hh
        have hh' : (⟨q a,haD⟩ : D) = 1 := Subtype.ext hh
        exact htf ((congrArg f hh').trans f.map_one)
      have hr'' : Module.finrank (ZMod 2)
          ((σ.comp D.subtype) ⟨q a,haD⟩ - LinearMap.id).range = 1 := by
        change Module.finrank (ZMod 2) (σ (q a) - LinearMap.id).range = 1
        rw [hσ]
        exact hr
      exact (ChapterG.Section06.no_outerShape_of_rank_one_normalClosure
        D (q a) haD hD (σ.comp D.subtype) hf ht2 hqa hr'' c).elim
  | hyperplane c =>
      exact (c.no_normalClosure_symmetricThree_quotient D (q a) haD hD
        (σ.comp D.subtype) hf.faithful hf.twoCore f hf' hkernel htf hr').elim
theorem source_solvable_seed_model_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g)
    (hn : ((faithfulTestModule F L).subgroupOf F.H).Normal) :
    letI := hn
    let K := solvableSeedActor F g
    let C := (centralizer ((faithfulTestModule F L).subgroupOf F.H : Set F.H)).comap K.subtype
    Nonempty ((K ⧸ C) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((K.map (QuotientGroup.mk' (centralizer
        ((faithfulTestModule F L).subgroupOf F.H : Set F.H)))) ≃* Equiv.Perm (Fin 3)) := by
  let := hn
  obtain ⟨_,_,⟨c⟩⟩ := source_solvable_seed_symmetricThree_at d earlier hq chosen structural
    alternatives F hne hz g hgP hgH row
  obtain ⟨e,_⟩ := solvable_seed_action_equiv (L := L) F g hn
  exact ⟨⟨e.trans c.equiv⟩,⟨c.equiv⟩⟩
theorem source_solvable_seed_kernel_and_plane_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    let W := (faithfulTestModule F L).subgroupOf F.H
    ∃ hn : W.Normal, ∃ he : IsElementaryAbelian 2 W, letI := hn; letI := he
    let K := solvableSeedActor F g
    (centralizer (W : Set F.H)).comap K.subtype =
        (F.uhatAction.comp K.subtype).ker ∧
      IsCompl (NormalElementaryQuotient.commutatorSpace W K)
        (fixedSpace (NormalElementaryQuotient.originalAction W) K) ∧
      Module.finrank (ZMod 2) (NormalElementaryQuotient.commutatorSpace W K) = 2 := by
  obtain ⟨hn,he,_⟩ := source_solvable_seed_symmetricThree_at d earlier hq chosen structural
    alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  have hm := (source_solvable_seed_model_at d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row hn).2
  exact ⟨hn,he,source_solvable_seed_kernel_eq_of_model_at d earlier hq chosen structural
    alternatives F hne hz g hgP row hn hm,
    source_solvable_seed_plane_of_model_at d earlier hq chosen structural alternatives
      F hne hz g hgP hgH row hn he hm⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableCentralQuotient.lean. -/
section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_solvable_center_commutator_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    ⁅F.ZU,conjugateSpanBy (conjugate F.ZU g) F.H⁆ =
      ⁅faithfulTestModule F L,conjugateSpanBy (conjugate F.ZU g) F.H⁆ := by
  let := chosen.elementary
  obtain ⟨hn,he,_,a,ha,hhat,hr,hsq⟩ := source_solvable_seed_rank_one_at d earlier hq chosen
    structural alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  let W := (faithfulTestModule F L).subgroupOf F.H
  let B := F.ZU ⊓ conjugate F.U g
  have hWZ := (source_faithful_test_reduced_at d earlier hq chosen structural alternatives F).1
  obtain ⟨hi,hc⟩ := source_center_axis_at d earlier hq chosen structural alternatives F hne g hgP hgH
  let f := F.uhatAction.comp (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)
  have hactor : f.range = (dotImage F F.uhatAction (conjugate F.ZU g)).map
      (faithfulAction F F.uhatAction) := by
    rw [faithfulAction_dotImage]
    ext b
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨F.conjugateCenterActor (by decide) L chosen.normalizes g hgP z,z.property,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hz⟩,rfl⟩
  have hcard : Nat.card f.range = 2 := by
    rw [hactor,card_map_of_injective (faithfulAction_injective F F.uhatAction)]
    exact row.marked_order
  rw [hcard] at hi
  have hWB : ¬ faithfulTestModule F L ≤ B := by
    intro hh
    have hca : a ∈ centralizer (W : Set F.H) := by
      intro w hw
      apply Subtype.ext
      exact (hc (hh hw) a ha).symm
    have hρ : NormalElementaryQuotient.originalAction W a = 1 :=
      (NormalElementaryQuotient.originalAction_kernel W).ge hca
    rw [hρ,Module.End.one_eq_id,sub_self,LinearMap.range_zero,finrank_bot] at hr
    omega
  obtain ⟨w,hw,hwB⟩ := SetLike.not_le_iff_exists.mp hWB
  have hsup : F.ZU = faithfulTestModule F L ⊔ B := by
    apply le_antisymm
    · rw [←sup_zpowers_eq_of_relIndex_prime (M := B) inf_le_left (by decide : Nat.Prime 2)
        hi (hWZ hw) hwB]
      exact sup_le le_sup_right ((zpowers_le.mpr hw).trans le_sup_left)
    · exact sup_le hWZ inf_le_left
  apply fixed_supplement_commutator_span F.H F.ZU (faithfulTestModule F L)
    (conjugate F.ZU g) B
  · intro z hz
    exact (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP ⟨z,hz⟩).property
  · exact (map_subtype_le (center F.U)).trans F.U_le_H
  · exact F.H_normalizes_ZU
  · exact le_normalizer_conjugateSpanBy _ _
  · exact hsup
  · exact hc
theorem source_solvable_center_plane_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    let Z := F.ZU.subgroupOf F.H
    let W := (faithfulTestModule F L).subgroupOf F.H
    let K := solvableSeedActor F g
    ⁅Z,K⁆ = ⁅W,K⁆ ∧ Nat.card (⁅Z,K⁆ : Subgroup F.H) = 4 ∧
      Disjoint (⁅Z,K⁆ : Subgroup F.H) (solvableCenterFixed F g) := by
  let := chosen.elementary
  dsimp only
  let Z := F.ZU.subgroupOf F.H
  let W := (faithfulTestModule F L).subgroupOf F.H
  let K := solvableSeedActor F g
  obtain ⟨hn,he,_,hc,hd⟩ := source_solvable_seed_kernel_and_plane_at d earlier hq chosen
    structural alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  have hWZ := (source_faithful_test_reduced_at d earlier hq chosen structural alternatives F).1
  have hZH : F.ZU ≤ F.H := (map_subtype_le (center F.U)).trans F.U_le_H
  have hWmap : W.map F.H.subtype = faithfulTestModule F L :=
    map_subgroupOf_eq_of_le (hWZ.trans hZH)
  have hZmap : Z.map F.H.subtype = F.ZU := map_subgroupOf_eq_of_le hZH
  have hKmap : K.map F.H.subtype = conjugateSpanBy (conjugate F.ZU g) F.H :=
    solvableSeedActor_map F chosen.normalizes g hgP
  have hcomm : ⁅Z,K⁆ = ⁅W,K⁆ := by
    apply (map_injective F.H.subtype_injective)
    rw [map_commutator,map_commutator,hWmap,hZmap,hKmap]
    exact source_solvable_center_commutator_at d earlier hq chosen structural alternatives
      F hne hz g hgP hgH row
  refine ⟨hcomm,?_,?_⟩
  · rw [hcomm]
    let : IsElementaryAbelian 2 (⁅W,K⁆ : Subgroup F.H) :=
      IsElementaryAbelian.of_le (commutator_le_left W K)
    let : Module.Finite (ZMod 2) (NormalElementaryQuotient.commutatorSpace W K) := Module.Finite.of_finite
    change Nat.card (Additive (⁅W,K⁆ : Subgroup F.H)) = 4
    rw [Nat.card_congr (NormalElementaryQuotient.commutatorSpaceEquiv W K).toEquiv,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    decide
  · rw [hcomm]
    apply disjoint_def.mpr
    intro x hx hxc
    let v : Additive W := Additive.ofMul ⟨x,commutator_le_left W K hx⟩
    have hm : v ∈ NormalElementaryQuotient.commutatorSpace W K := hx
    have hf : v ∈ fixedSpace (NormalElementaryQuotient.originalAction W) K :=
      (NormalElementaryQuotient.original_fixedSpace W K v).mpr hxc.2
    have hv : v = 0 := hc.disjoint.le_bot ⟨hm,hf⟩
    exact congrArg (fun w : Additive W => (w.toMul : F.H)) hv
theorem source_solvable_center_quotient_elementary_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (g : G) :
    IsElementaryAbelian 2 ((F.U.subgroupOf F.H).map
      (QuotientGroup.mk' (solvableCenterFixed F g))) := by
  let := chosen.elementary
  let C := solvableCenterFixed F g
  let q := QuotientGroup.mk' C
  let U := F.U.subgroupOf F.H
  have h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm,hsquare⟩ := F.localKernel_commutator_squares d.qtke L
    (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
    (h.sylow_normalizes_at structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape_at F alternatives)
  have hUC : ⁅U,U⁆ ≤ C := by
    apply commutator_le.mpr
    intro u hu v hv
    apply solvableCenterFixed_point F g
    exact hcomm (commutator_mem_commutator hu hv)
  have hcommQ : ⁅U.map q,U.map q⁆ = ⊥ := by
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hUC
  let : IsMulCommutative (U.map q) := commutator_self_eq_bot_iff.mp hcommQ
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  rintro ⟨_,u,hu,rfl⟩
  apply Subtype.ext
  change (q u)^2 = 1
  rw [←map_pow]
  apply (QuotientGroup.eq_one_iff (u^2)).mpr
  exact solvableCenterFixed_point F g (hsquare u hu)
theorem source_solvable_center_quotient_reduced_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (g : G) :
    IsPReduced 2 ((F.U.subgroupOf F.H).map
      (QuotientGroup.mk' (solvableCenterFixed F g))) := by
  let := chosen.elementary
  let C := solvableCenterFixed F g
  let q := QuotientGroup.mk' C
  let U := F.U.subgroupOf F.H
  let P := (F.Vi 2).subgroupOf F.H
  let B := P.map q
  let Q := F.H ⧸ C
  let S : Sylow 2 F.H := T.subtype (show (T : Subgroup G) ≤ F.H from F.invariant 1)
  let Sq := S.mapSurjective (QuotientGroup.mk'_surjective C)
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy V F.H)
  let : IsElementaryAbelian 2 (U.map q) :=
    source_solvable_center_quotient_elementary_at d earlier hq chosen structural alternatives F g
  have hPU : F.Vi 2 ≤ F.U := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
  have hPH : F.Vi 2 ≤ F.H := hPU.trans F.U_le_H
  have hpoint : (F.Vi 1).subgroupOf F.H ≤ C := solvableCenterFixed_point F g
  have hVZ := (source_closure_at d earlier hq chosen structural alternatives F hne).2.2
  have hPZ : F.Vi 2 ⊓ F.ZU = F.Vi 1 := by
    apply le_antisymm
    · exact (inf_le_inf_right F.ZU (F.le_seed 2)).trans hVZ.le
    · exact le_inf (F.monotone (by decide : 1 ≤ 2)) (F.point_le_ZU (by decide))
  have hPC : P ⊓ C = (F.Vi 1).subgroupOf F.H := by
    ext x
    constructor
    · intro hx
      exact hPZ.le ⟨hx.1,hx.2.1⟩
    · intro hx
      exact ⟨F.monotone (by decide : 1 ≤ 2) hx,hpoint hx⟩
  have hBcard : Nat.card B = 2 := by
    rw [←relIndex_ker,QuotientGroup.ker_mk',←inf_relIndex_left,hPC,
      relIndex_subgroupOf hPH]
    have ht := relIndex_mul_relIndex (⊥ : Subgroup G) (F.Vi 1) (F.Vi 2)
      bot_le (F.monotone (by decide : 1 ≤ 2))
    rw [relIndex_bot_left,relIndex_bot_left,F.card 1 (by decide),F.card 2 (by decide)] at ht
    norm_num at ht
    omega
  have hSP : (S : Subgroup F.H) ≤ normalizer (P : Set F.H) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro p
    exact mem_normalizer_iff.mp (F.invariant 2 hs) (p : G)
  have hSB : (Sq : Subgroup Q) ≤ normalizer (B : Set Q) :=
    (map_mono hSP).trans (P.le_normalizer_map q)
  have hBS : B ≤ centralizer (Sq : Set Q) :=
    le_centralizer_iff.mp (hSB.trans (normalizer_le_centralizer_of_card_two B hBcard))
  have h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  have hspan := F.U_eq_plane_span L (by decide) chosen.normalizes
    (F.localKernel_irreducible L (by decide) chosen.normalizes (fun _ => ⟨h.naturalMarking⟩))
  have hUspan : U = conjugateSpanBy P ⊤ := by
    apply map_injective F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le F.U_le_H,map_conjugateSpanBy,
      map_subgroupOf_eq_of_le hPH,←MonoidHom.range_eq_map,Subgroup.range_subtype]
    exact hspan
  have hgen : U.map q = conjugateSpanBy B ⊤ := by
    rw [hUspan,map_conjugateSpanBy,map_top_of_surjective q (QuotientGroup.mk'_surjective C)]
  have hr := reduced_of_sylow_central_seed Sq ⊤ (U.map q) B le_top le_top
    (by rw [normalizer_eq_top]) (map_mono (comap_mono hPU)) hBS hgen
  have hm : ((U.map q).subgroupOf ⊤).map
      (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q).toMonoidHom = U.map q :=
    map_subgroupOf_eq_of_le le_top
  rw [←hm]
  exact hr.map_equiv Subgroup.topEquiv
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableCentralSplitting.lean. -/
section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_solvable_center_quotient_kernel_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    solvableSeedActor F g ⊓ solvableCenterQuotientKernel F g =
      solvableSeedActor F g ⊓ F.uhatAction.ker := by
  let := chosen.elementary
  let U := F.U.subgroupOf F.H
  let Z := F.ZU.subgroupOf F.H
  let W := (faithfulTestModule F L).subgroupOf F.H
  let K := solvableSeedActor F g
  let N := K ⊓ F.uhatAction.ker
  let C := solvableCenterFixed F g
  let q := QuotientGroup.mk' C
  have hUZ : ⁅U,N⁆ ≤ Z := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro n hn x hx
    exact (F.mem_uhatAction_ker_iff n).mp hn.2 x hx
  obtain ⟨hn,he,hker,_,_⟩ := source_solvable_seed_kernel_and_plane_at d earlier hq chosen
    structural alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  have hZN : ⁅Z,N⁆ ≤ W := by
    have hsame := (source_solvable_center_plane_at d earlier hq chosen structural alternatives
      F hne hz g hgP hgH row).1
    exact ((commutator_mono le_rfl inf_le_left).trans hsame.le).trans (commutator_le_left W K)
  have hWN : ⁅W,N⁆ = ⊥ := by
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro n hn
    exact hker.ge (show (⟨n,hn.1⟩ : K) ∈ (F.uhatAction.comp K.subtype).ker from hn.2)
  have hred := source_solvable_center_quotient_reduced_at d earlier hq chosen structural alternatives
    F hne g
  let : (N.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective C)
  have hNC : N.map q ≤ centralizer (U.map q : Set (F.H ⧸ C)) :=
    hred.centralizes_of_three_layers (N.map q) (Z.map q) (W.map q)
      (by rw [←map_commutator]; exact map_mono hUZ)
      (by rw [←map_commutator]; exact map_mono hZN)
      (by rw [←map_commutator,hWN,Subgroup.map_bot])
  apply le_antisymm
  · intro k hk
    refine ⟨hk.1,(F.mem_uhatAction_ker_iff k).mpr ?_⟩
    intro x hx
    have hxH : x ∈ F.H := F.U_le_H hx
    have hc : q ⁅k,(⟨x,hxH⟩ : F.H)⁆ = 1 := by
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact (hk.2 _ (mem_map_of_mem q hx)).symm
    exact (QuotientGroup.eq_one_iff _).mp hc |>.1
  · intro k hk
    exact ⟨hk.1,hNC (mem_map_of_mem q hk)⟩
theorem source_solvable_center_kernel_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    solvableSeedActor F g ⊓ centralizer (F.ZU.subgroupOf F.H : Set F.H) =
      solvableSeedActor F g ⊓ F.uhatAction.ker := by
  let := chosen.elementary
  let K := solvableSeedActor F g
  let Z := F.ZU.subgroupOf F.H
  let C := solvableCenterFixed F g
  let q := QuotientGroup.mk' C
  obtain ⟨_,_,hd⟩ := source_solvable_center_plane_at d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  have hqkernel := source_solvable_center_quotient_kernel_at d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  obtain ⟨hn,he,hker,_,_⟩ := source_solvable_seed_kernel_and_plane_at d earlier hq chosen
    structural alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  have hWZ := (source_faithful_test_reduced_at d earlier hq chosen structural alternatives F).1
  apply le_antisymm
  · intro k hk
    refine ⟨hk.1,?_⟩
    have hc : (⟨k,hk.1⟩ : K) ∈ (centralizer
        ((faithfulTestModule F L).subgroupOf F.H : Set F.H)).comap K.subtype :=
      (centralizer_le (comap_mono hWZ)) hk.2
    exact hker.le hc
  · intro k hk
    refine ⟨hk.1,?_⟩
    intro z hz
    have hcomm : ⁅z,k⁆ ∈ C := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q ⁅z,k⁆ = 1
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact (hqkernel.ge hk).2 _ (mem_map_of_mem q ((map_subtype_le (center F.U)) hz))
    have hbot : ⁅z,k⁆ = 1 := hd.le_bot ⟨commutator_mem_commutator hz hk.1,hcomm⟩
    exact commutatorElement_eq_one_iff_mul_comm.mp hbot
theorem source_solvable_center_splitting_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    F.ZU.subgroupOf F.H = ⁅F.ZU.subgroupOf F.H,solvableSeedActor F g⁆ ⊔
        solvableCenterFixed F g ∧
      Disjoint (⁅F.ZU.subgroupOf F.H,solvableSeedActor F g⁆ : Subgroup F.H)
        (solvableCenterFixed F g) := by
  let := chosen.elementary
  let Z := F.ZU.subgroupOf F.H
  let W := (faithfulTestModule F L).subgroupOf F.H
  let K := solvableSeedActor F g
  let : Z.Normal := normal_subgroupOf_of_le_normalizer F.H_normalizes_ZU
  let : IsMulCommutative F.ZU := by
    change IsMulCommutative ((center F.U).map F.U.subtype)
    infer_instance
  let : IsMulCommutative Z := inferInstanceAs (IsMulCommutative (F.ZU.subgroupOf F.H))
  obtain ⟨hn,he,hker,_,_⟩ := source_solvable_seed_kernel_and_plane_at d earlier hq chosen
    structural alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  have hkZ := source_solvable_center_kernel_at d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  have hCeq : (centralizer (Z : Set F.H)).comap K.subtype =
      (centralizer (W : Set F.H)).comap K.subtype := by
    ext k
    constructor
    · intro hk
      exact hker.ge ((hkZ.le ⟨k.property,hk⟩).2)
    · intro hk
      exact (hkZ.ge ⟨k.property,hker.le hk⟩).2
  obtain ⟨⟨em⟩,_⟩ := source_solvable_seed_model_at d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row hn
  have hmodel : Nonempty ((K ⧸ (centralizer (Z : Set F.H)).comap K.subtype) ≃*
      Equiv.Perm (Fin 3)) := ⟨(QuotientGroup.quotientMulEquivOfEq hCeq).trans em⟩
  obtain ⟨_,hcard,hdis⟩ := source_solvable_center_plane_at d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  have hZtwo : IsPGroup 2 Z :=
    (T.isPGroup'.to_le ((map_subtype_le (center F.U)).trans
      (source_closure_le_sylow_at d earlier hq chosen structural alternatives F))).comap_subtype
  exact ⟨commutator_plane_splitting_of_symmetricThree Z K hZtwo hcard hdis hmodel,hdis⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableFullKernel.lean. -/
section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_solvable_hatted_kernel_plane_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    F.uhatAction.ker ≤ centralizer
      ((⁅F.ZU.subgroupOf F.H,solvableSeedActor F g⁆ : Subgroup F.H) : Set F.H) := by
  let := chosen.elementary
  let Z := F.ZU.subgroupOf F.H
  let W := (faithfulTestModule F L).subgroupOf F.H
  let K := solvableSeedActor F g
  let D := ⁅Z,K⁆
  let C := solvableCenterFixed F g
  let N := F.uhatAction.ker
  let : Z.Normal := normal_subgroupOf_of_le_normalizer F.H_normalizes_ZU
  obtain ⟨hn,he,hker,_,_⟩ := source_solvable_seed_kernel_and_plane_at d earlier hq chosen
    structural alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  obtain ⟨hsame,hcard,hd⟩ := source_solvable_center_plane_at d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  have hDW : D ≤ W := hsame.le.trans (commutator_le_left W K)
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le hDW
  have hs := (source_solvable_center_splitting_at d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row).1
  have hkZ := source_solvable_center_kernel_at d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  have hCeq : (centralizer (D : Set F.H)).comap K.subtype =
      (centralizer (W : Set F.H)).comap K.subtype := by
    ext k
    constructor
    · intro hk
      have hCZ : (k:F.H) ∈ centralizer (Z : Set F.H) := by
        intro z hz
        obtain ⟨x,hx,y,hy,rfl⟩ := mem_sup_of_normal_left.mp (hs.le hz)
        have hc : y * (k:F.H) = (k:F.H) * y := (hy.2 k k.property).symm
        have hcx : x * (k:F.H) = (k:F.H) * x := hk x hx
        rw [mul_assoc,hc,←mul_assoc,hcx,mul_assoc]
      exact hker.ge ((hkZ.le ⟨k.property,hCZ⟩).2)
    · intro hk
      exact centralizer_le hDW hk
  obtain ⟨⟨em⟩,_⟩ := source_solvable_seed_model_at d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row hn
  have hmodel : Nonempty ((K ⧸ (centralizer (D : Set F.H)).comap K.subtype) ≃*
      Equiv.Perm (Fin 3)) := ⟨(QuotientGroup.quotientMulEquivOfEq hCeq).trans em⟩
  apply centralizes_four_plane_of_commuting_symmetricThree D K N hcard hmodel
  intro x hx
  have hxN : x ∈ K ⊓ N := by
    have hh := commutator_le_inf N K hx
    exact ⟨hh.2,hh.1⟩
  exact centralizer_le (commutator_le_left Z K) (hkZ.ge hxN).2
theorem source_solvable_full_kernel_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    solvableCenterQuotientKernel F g = F.uhatAction.ker := by
  let := chosen.elementary
  let U := F.U.subgroupOf F.H
  let Z := F.ZU.subgroupOf F.H
  let K := solvableSeedActor F g
  let D := ⁅Z,K⁆
  let C := solvableCenterFixed F g
  let N := F.uhatAction.ker
  let q := QuotientGroup.mk' C
  let : Z.Normal := normal_subgroupOf_of_le_normalizer F.H_normalizes_ZU
  have hUZ : ⁅U,N⁆ ≤ Z := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro n hn x hx
    exact (F.mem_uhatAction_ker_iff n).mp hn x hx
  have hND := source_solvable_hatted_kernel_plane_at d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  have hZN : ⁅Z,N⁆ ≤ C := by
    have hs : Z = D ⊔ C := (source_solvable_center_splitting_at d earlier hq chosen
      structural alternatives F hne hz g hgP hgH row).1
    rw [hs]
    apply commutator_sup_le_of_relative_normal ⊤ D C N C le_normalizer_of_normal le_top le_top
    · rw [commutator_comm,commutator_eq_bot_iff_le_centralizer.mpr hND]
      exact bot_le
    · exact commutator_le_left C N
  have hred := source_solvable_center_quotient_reduced_at d earlier hq chosen structural alternatives
    F hne g
  let : (N.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective C)
  have hNC : N.map q ≤ centralizer (U.map q : Set (F.H ⧸ C)) :=
    hred.centralizes_of_three_layers (N.map q) (Z.map q) ⊥
      (by rw [←map_commutator]; exact map_mono hUZ)
      (by
        rw [←map_commutator]
        apply (map_mono hZN).trans
        exact ((Subgroup.map_eq_bot_iff (H := C)).mpr (by rw [QuotientGroup.ker_mk'])).le)
      (by rw [Subgroup.commutator_bot_left])
  apply le_antisymm
  · intro k hk
    apply (F.mem_uhatAction_ker_iff k).mpr
    intro x hx
    have hxH : x ∈ F.H := F.U_le_H hx
    have hc : q ⁅k,(⟨x,hxH⟩ : F.H)⁆ = 1 := by
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact (hk _ (mem_map_of_mem q hx)).symm
    exact (QuotientGroup.eq_one_iff _).mp hc |>.1
  · intro k hk
    exact hNC (mem_map_of_mem q hk)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableExclusion.lean. -/
section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
omit [Finite G] in
private theorem solvableExclusion_seed_moved_at [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 (F.tilde V)]
    (hLV : L ≤ normalizer (V : Set G)) (D : F.NaturalSeedMarking L hLV) :
    ∃ k v, F.localSeedRepresentation L hLV k v ≠ v := by
  by_contra! hfix
  let v := D.coordinates.symm (![1,0] : Fin 2 → ZMod 2)
  obtain ⟨a,ha⟩ := BinaryLinear.OuterCyclic.BinaryTwo.derived_transitive_nonzero
    (by decide : (![1,0] : Fin 2 → ZMod 2) ≠ 0)
    (by decide : (![0,1] : Fin 2 → ZMod 2) ≠ 0)
  obtain ⟨q,hq⟩ := D.quotientEquiv.surjective a
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.Li L 1)) q
  have he := D.equivariant k v
  rw [hfix,hq] at he
  simp only [v,LinearEquiv.apply_symm_apply] at he
  have hh := congrFun (he.trans ha) 0
  norm_num at hh
theorem source_solvable_center_quotient_fixed_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g)
    (hn : (dotImage F F.uhatAction (F.Li L 1)).Normal) :
    let q := QuotientGroup.mk' (solvableCenterFixed F g)
    ((F.U.subgroupOf F.H).map q) ⊓
      centralizer (((F.Li L 1).subgroupOf F.H).map q : Set (F.H ⧸ solvableCenterFixed F g)) = ⊥ := by
  let := chosen.elementary
  let C := solvableCenterFixed F g
  let q := QuotientGroup.mk' C
  let U := F.U.subgroupOf F.H
  let Uq := U.map q
  have hr := source_solvable_center_quotient_reduced_at d earlier hq chosen structural alternatives F hne g
  let := hr.normal
  let := hr.elementary
  let ρ := (NormalElementaryQuotient.originalAction Uq).comp q
  have hρ (a : F.H) (x : Additive Uq) :
      ((ρ a x).toMul : F.H ⧸ C) = q a * (x.toMul : F.H ⧸ C) * (q a)⁻¹ :=
    NormalElementaryQuotient.originalAction_apply Uq (q a) x
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  let := F.localKernel_tilde_seed_elementary
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient (by decide) L chosen.normalizes h.naturalMarking
  let σ := F.localSeedRepresentation L chosen.normalizes
  let k : F.Li L 1 →* F.H := inclusion ((F.Li_le L 1).trans inf_le_right)
  let p : F.G₁tilde →* (F.H ⧸ C) := QuotientGroup.map _ _ (MonoidHom.id F.H)
    (solvableCenterFixed_point F g)
  have hp (a : F.H) : p (F.tildeProjection a) = q a := rfl
  have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
  have hVH : V ≤ F.H := hVU.trans F.U_le_H
  let f : F.tilde V →* Uq := (p.comp (F.tilde V).subtype).codRestrict Uq (by
    rintro ⟨x,a,ha,rfl⟩
    exact mem_map_of_mem q (hVU ha))
  let ι := f.toAdditive.toZModLinearMap 2
  have hi : Function.Injective ι := by
    apply (injective_iff_map_eq_zero ι).mpr
    intro x hx
    apply Additive.toMul.injective
    apply Subtype.ext
    obtain ⟨a,ha,he⟩ := x.toMul.property
    have hqa : q a = 1 := by
      have hh := congrArg (fun y : Additive Uq => (y.toMul : F.H ⧸ C)) hx
      change p (x.toMul : F.G₁tilde) = 1 at hh
      rw [←he] at hh
      exact hh
    have hC : a ∈ C := (QuotientGroup.eq_one_iff a).mp hqa
    have hpt : (a:G) ∈ F.Vi 1 :=
      (source_closure_at d earlier hq chosen structural alternatives F hne).2.2.le ⟨ha,hC.1⟩
    exact he.symm.trans ((QuotientGroup.eq_one_iff a).mpr hpt)
  have he (a : F.Li L 1) (x : Additive (F.tilde V)) :
      ι (σ a x) = ρ (k a) (ι x) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change p ((F.tildeAction (F.Li L 1) V _ _ a x.toMul : F.tilde V) : F.G₁tilde) = _
    rw [F.tildeAction_apply_coe,map_mul,map_mul,map_inv,hp]
    exact (NormalElementaryQuotient.originalAction_apply Uq (q (k a)) (ι x)).symm
  have hgen : ∀ R : Subrepresentation ρ, LinearMap.range ι ≤ R.toSubmodule → R = ⊤ := by
    intro R hR
    let A : Subgroup (F.H ⧸ C) := R.toSubmodule.toAddSubgroup.toSubgroup'.map Uq.subtype
    have hnA : F.H ≤ normalizer ((A.comap q).map F.H.subtype : Set G) := by
      apply le_normalizer_iff.mpr
      intro a ha x hx
      obtain ⟨b,hb,rfl⟩ := hx
      obtain ⟨w,hw,hwe⟩ := hb
      refine ⟨(⟨a,ha⟩ : F.H) * b * (⟨a,ha⟩ : F.H)⁻¹,?_,rfl⟩
      refine ⟨(ρ ⟨a,ha⟩ (Additive.ofMul w)).toMul,R.apply_mem_toSubmodule ⟨a,ha⟩ hw,?_⟩
      change ((ρ ⟨a,ha⟩ (Additive.ofMul w)).toMul : F.H ⧸ C) = _
      rw [hρ]
      change q ⟨a,ha⟩ * Uq.subtype w * (q ⟨a,ha⟩)⁻¹ = _
      rw [hwe,map_mul,map_mul,map_inv]
    have hVA : V ≤ (A.comap q).map F.H.subtype := by
      intro v hv
      refine ⟨⟨v,hVH hv⟩,?_,rfl⟩
      exact ⟨f (F.tildeMap V hVH ⟨v,hv⟩), hR ⟨Additive.ofMul (F.tildeMap V hVH ⟨v,hv⟩),rfl⟩,rfl⟩
    have hUA : F.U ≤ (A.comap q).map F.H.subtype := conjugateSpanBy_le hVA hnA
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro x _
    obtain ⟨a,ha,he⟩ := x.toMul.property
    obtain ⟨b,hb,hba⟩ := hUA ha
    have hba' : b = a := Subtype.ext hba
    subst b
    obtain ⟨w,hw,hwe⟩ := hb
    have hwx : w = x.toMul := Subtype.ext (hwe.trans he)
    have hwx' : Additive.ofMul w = x := congrArg Additive.ofMul hwx
    exact hwx' ▸ hw
  let qhat := QuotientGroup.mk' F.uhatAction.ker
  have hker : qhat.ker ≤ ρ.ker := by
    rw [QuotientGroup.ker_mk']
    intro a ha
    apply (NormalElementaryQuotient.originalAction_kernel Uq).ge
    exact (source_solvable_full_kernel_at d earlier hq chosen structural alternatives F hne hz g hgP hgH row).ge ha
  have hnormal : (qhat.comp k).range.Normal := by
    have heq : (qhat.comp k).range = dotImage F F.uhatAction (F.Li L 1) := by
      ext x
      constructor
      · rintro ⟨a,rfl⟩
        exact ⟨k a,a.property,rfl⟩
      · rintro ⟨a,ha,rfl⟩
        exact ⟨⟨a,ha⟩,rfl⟩
    rw [heq]
    exact hn
  have hf := fixed_eq_zero_of_normal_image_simple_seed ρ σ qhat k hker hnormal ι hi he
    ((irreducible_iff_isSimpleModule_asModule σ).mpr (D.seed_simple (by decide)))
    (solvableExclusion_seed_moved_at F chosen.normalizes D) hgen
  apply le_bot_iff.mp
  intro x hx
  let v : Additive Uq := Additive.ofMul ⟨x,hx.1⟩
  have hv : v = 0 := hf v (by
    intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((ρ (k a) v).toMul : F.H ⧸ C) = _
    rw [hρ]
    exact mul_inv_eq_iff_eq_mul.mpr (hx.2 (q (k a)) (mem_map_of_mem q a.property)))
  exact congrArg (fun y : Additive Uq => (y.toMul : F.H ⧸ C)) hv
theorem source_seed_exclusion_of_solvable_row_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g)
    (hn : (dotImage F F.uhatAction (F.Li L 1)).Normal) :
    centralLTSeed F L = ⊥ := by
  by_contra hz
  let := chosen.elementary
  let C := solvableCenterFixed F g
  let q := QuotientGroup.mk' C
  let W := (faithfulTestModule F L).subgroupOf F.H
  let K := solvableSeedActor F g
  have hfix := source_solvable_center_quotient_fixed_at d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row hn
  have hseed : centralLTSeed F L ≤ C.map F.H.subtype := by
    intro z hz
    let zH : F.H := ⟨z,F.U_le_H hz.2⟩
    have hzq : q zH = 1 := hfix.le ⟨mem_map_of_mem q hz.2,by
      rintro _ ⟨a,ha,rfl⟩
      apply (map_mul q a zH).symm.trans
      apply Eq.trans _ (map_mul q zH a)
      apply congrArg q
      apply Subtype.ext
      obtain ⟨c,hc,he⟩ := hz.1
      have hcomm := congrArg Subtype.val (mem_center_iff.mp hc
        ⟨a,mem_sup_left ((F.Li_le L 1 ha).1)⟩)
      change (a:G) * z = z * (a:G)
      rw [←he]
      exact hcomm⟩
    exact ⟨zH,(QuotientGroup.eq_one_iff zH).mp hzq,rfl⟩
  have hnorm : F.H ≤ normalizer (C.map F.H.subtype : Set G) := by
    apply le_normalizer_iff.mpr
    intro a ha z hz
    obtain ⟨c,hc,rfl⟩ := hz
    exact ⟨(⟨a,ha⟩ : F.H) * c * (⟨a,ha⟩ : F.H)⁻¹,
      (inferInstance : C.Normal).conj_mem c hc ⟨a,ha⟩,rfl⟩
  have hspan : faithfulTestModule F L ≤ C.map F.H.subtype := conjugateSpanBy_le hseed hnorm
  have hWC : W ≤ C := by
    intro w hw
    obtain ⟨c,hc,he⟩ := hspan hw
    exact (Subtype.ext he : c = w) ▸ hc
  have hcomm : ⁅W,K⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hWC.trans inf_le_right)
  obtain ⟨heq,hcard,_⟩ := source_solvable_center_plane_at d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  rw [heq,hcomm,card_bot] at hcard
  omega
theorem source_dot_Li_one_normal_of_symmetricThreePair_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    (dotImage F F.uhatAction (F.Li L 1)).Normal := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  let N := (F.Li L 1).subgroupOf F.H
  let q := QuotientGroup.mk' F.uhatAction.ker
  obtain ⟨e⟩ := model
  have hcard : Nat.card (pResidual 2 (Hdot F F.uhatAction)) = 9 := by
    rw [←card_map_of_injective (f := e.toMonoidHom) (K := pResidual 2 (Hdot F F.uhatAction)) e.injective,
      map_pResidual_of_surjective 2 e.toMonoidHom e.surjective]
    exact SymmetricThreeProductResidual.residual_card
  let : IsMulCommutative (pResidual 2 (Hdot F F.uhatAction)) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcard
  have hres : F.Li L 1 = (pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype := by
    simp only [Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) from by omega, if_false]
  have hTn : (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) := by
    rw [hres]
    exact ((le_inf (h.sylow_normalizes_at structural)
      ((F.invariant 1).trans (F.Gi 1).le_normalizer)).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (L ⊓ F.Gi 1) (pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)))
  have hLH : F.Li L 1 ≤ F.H := fun x hx => (F.Li_le L 1 hx).2
  have hp : IsPPerfect 2 N := by
    have hh : IsPPerfect 2 (F.Li L 1) := by
      rw [hres]
      exact isPPerfect_embedded_pResidual 2 (L ⊓ F.Gi 1)
    exact hh.of_surjective (subgroupOfEquivOfLe hLH).symm.toMonoidHom
      (subgroupOfEquivOfLe hLH).symm.surjective
  let S := (T.subtype (F.invariant 1)).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hSN : (S : Subgroup (Hdot F F.uhatAction)) ≤ normalizer (N.map q : Set (Hdot F F.uhatAction)) := by
    apply le_trans (map_mono (f := q) ?_) (N.le_normalizer_map q)
    intro t ht
    rw [mem_normalizer_iff]
    intro x
    exact (mem_normalizer_iff.mp (hTn ht)) (x : G)
  have hN : N.map q ≤ pResidual 2 (Hdot F F.uhatAction) :=
    le_pResidual_of_isPPerfect _ (hp.of_surjective (q.subgroupMap N) (q.subgroupMap_surjective N))
  have hC : pResidual 2 (Hdot F F.uhatAction) ≤ centralizer (N.map q : Set (Hdot F F.uhatAction)) := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm
      (⟨y,hN hy⟩ : pResidual 2 (Hdot F F.uhatAction)) ⟨x,hx⟩)
  change (N.map q).Normal
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [←pResidual_sup_sylow_eq_top S]
  exact sup_le (hC.trans (Subgroup.centralizer_le_normalizer _)) hSN
theorem source_seed_exclusion_of_symmetricThreePair_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    centralLTSeed F L = ⊥ :=
  source_seed_exclusion_of_solvable_row_at d earlier hq chosen structural alternatives F hne
    g hgP hgH row (source_dot_Li_one_normal_of_symmetricThreePair_at d earlier hq chosen structural F model)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SolvableRow.lean. -/
section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
private theorem solvableRow_source_solvable_point_kernel_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    (F.uhatAction.comp (inclusion ((F.Li_le L 1).trans inf_le_right))).ker =
      pCore 2 (F.Li L 1) := by
  let := chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient (by decide) L chosen.normalizes h.naturalMarking
  let q := QuotientGroup.mk' F.uhatAction.ker
  let f := q.comp (inclusion ((F.Li_le L 1).trans inf_le_right))
  have hp : IsPPerfect 2 (F.Li L 1) := by
    change IsPPerfect 2 ((pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype)
    exact isPPerfect_embedded_pResidual 2 _
  have hfr : f.range ≤ pResidual 2 (Hdot F F.uhatAction) :=
    le_pResidual_of_isPPerfect _ (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  obtain ⟨e⟩ := model
  have hr : Nat.card (pResidual 2 (Hdot F F.uhatAction)) = 9 := by
    rw [←card_map_of_injective (f := e.toMonoidHom) e.injective,
      map_pResidual_of_surjective 2 e.toMonoidHom e.surjective]
    exact SymmetricThreeProductResidual.residual_card
  have hdis := IsPGroup.disjoint_of_coprime
    (pCore_isPGroup.map f : IsPGroup 2 ((pCore 2 (F.Li L 1)).map f))
    (IsPGroup.of_card (p := 3) (n := 2) hr) (by decide : Nat.Coprime 2 3)
  have hcore : pCore 2 (F.Li L 1) ≤ f.ker := by
    intro k hk
    exact Subgroup.disjoint_def.mp hdis (mem_map_of_mem f hk) (hfr ⟨k,rfl⟩)
  apply le_antisymm
  · intro k hk
    rw [←D.seedAction_ker]
    apply (F.mem_tildeAction_ker_iff _ _ _
      ((le_conjugateSpanBy V F.H).trans F.U_le_H) _ k).mpr
    intro v hv
    rw [← (source_closure_at d earlier hq chosen structural alternatives F hne).2.2]
    refine ⟨V.mul_mem ((mem_normalizer_iff.mp
      (chosen.normalizes (F.Li_le L 1 k.property).1) v).mp hv) (V.inv_mem hv),?_⟩
    exact (F.mem_uhatAction_ker_iff _).mp hk v (le_conjugateSpanBy V F.H hv)
  · intro k hk
    have hh : (⟨k,(F.Li_le L 1 k.property).2⟩ : F.H) ∈ q.ker := hcore hk
    rw [show q.ker = F.uhatAction.ker from QuotientGroup.ker_mk' _] at hh
    exact hh
private theorem solvableRow_source_solvable_point_order_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    Nat.card (dotImage F F.uhatAction (F.Li L 1)) = 3 := by
  let := chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient (by decide) L chosen.normalizes h.naturalMarking
  let q := QuotientGroup.mk' F.uhatAction.ker
  let f := q.comp (inclusion ((F.Li_le L 1).trans inf_le_right))
  have hrange : f.range = dotImage F F.uhatAction (F.Li L 1) := by
    ext x
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨_,k.property,rfl⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨⟨k,hk⟩,rfl⟩
  have hker : f.ker = pCore 2 (F.Li L 1) := by
    rw [←solvableRow_source_solvable_point_kernel_at d earlier hq chosen structural alternatives F hne model]
    ext k
    exact QuotientGroup.eq_one_iff _
  rw [←hrange,←Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hker,
    Nat.card_congr D.quotientEquiv.toEquiv]
  exact BinaryLinear.SmallParabolicLevi.derived_two_card
private theorem solvableRow_source_solvable_point_faithful_on_seed_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (n : Hdot F F.uhatAction) (hn : n ∈ dotImage F F.uhatAction (F.Li L 1))
    (hf : ∀ w ∈ hatSpace F V, F.terminalRepresentation n w = w) : n = 1 := by
  let := chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient (by decide) L chosen.normalizes h.naturalMarking
  obtain ⟨k,hk,rfl⟩ := hn
  let kL : F.Li L 1 := ⟨k,hk⟩
  have hc : kL ∈ pCore 2 (F.Li L 1) := by
    rw [←D.seedAction_ker]
    apply (F.mem_tildeAction_ker_iff _ _ _
      ((le_conjugateSpanBy V F.H).trans F.U_le_H) _ kL).mpr
    intro v hv
    rw [← (source_closure_at d earlier hq chosen structural alternatives F hne).2.2]
    refine ⟨V.mul_mem ((mem_normalizer_iff.mp
      (chosen.normalizes (F.Li_le L 1 hk).1) v).mp hv) (V.inv_mem hv),?_⟩
    let vU : F.U := ⟨v,le_conjugateSpanBy V F.H hv⟩
    have he := congrArg Additive.toMul (hf (hatElement F vU) ⟨vU,hv,rfl⟩)
    change F.uhatAction k (QuotientGroup.mk' (center F.U) vU) =
      QuotientGroup.mk' (center F.U) vU at he
    rw [F.uhatAction_apply_mk] at he
    refine ⟨_,QuotientGroup.eq_iff_div_mem.mp he,?_⟩
    simp only [commutatorElement_def,div_eq_mul_inv]
    rfl
  have hh := (solvableRow_source_solvable_point_kernel_at d earlier hq chosen structural alternatives F hne model).symm ▸ hc
  exact (QuotientGroup.eq_one_iff k).mpr hh
private theorem solvableRow_source_solvable_center_centralizes_point_image_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (g : G) (hgP : g ∈ F.P L) :
    dotImage F F.uhatAction (conjugate F.ZU g) ≤
      centralizer (dotImage F F.uhatAction (F.Li L 1) : Set (Hdot F F.uhatAction)) := by
  let N := dotImage F F.uhatAction (F.Li L 1)
  let ρ := elementaryRepresentation (p := 2) (faithfulAction F F.uhatAction)
  let W := hatSpace F V
  let := source_dot_Li_one_normal_of_symmetricThreePair_at d earlier hq chosen structural F model
  have hstable (n : Hdot F F.uhatAction) (hn : n ∈ N) (w : Additive F.Uhat) (hw : w ∈ W) :
      ρ n w ∈ W := by
    obtain ⟨k,hk,rfl⟩ := hn
    obtain ⟨v,hv,he⟩ := hw
    refine ⟨F.uAction k v,(mem_normalizer_iff.mp
      (chosen.normalizes (F.Li_le L 1 hk).1) (v:G)).mp hv,?_⟩
    change QuotientGroup.mk' (center F.U) (F.uAction k v) = F.uhatAction k w.toMul
    rw [←F.uhatAction_apply_mk,he]
  intro z hz n hn
  have hzK : z ∈ BinaryOffender.subspaceKernel ρ W ⊤ :=
    ⟨mem_top _,source_conjugate_center_fixes_seed chosen F g hgP z hz⟩
  have hzi := (BinaryOffender.subspaceKernel ρ W ⊤).inv_mem hzK
  have hm : n⁻¹ * (z*n*z⁻¹) ∈ N := N.mul_mem (N.inv_mem hn)
    ((inferInstance : N.Normal).conj_mem n hn z)
  have he : n⁻¹ * (z*n*z⁻¹) = 1 :=
    solvableRow_source_solvable_point_faithful_on_seed_at d earlier hq chosen structural alternatives F hne model _ hm (by
      intro w hw
      change ρ (n⁻¹ * (z*n*z⁻¹)) w = w
      simp only [map_mul,Module.End.mul_apply,hzi.2 w hw,hzK.2 _ (hstable n hn w hw)]
      rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply])
  exact (mul_inv_eq_iff_eq_mul.mp (inv_mul_eq_one.mp he).symm).symm
theorem source_solvable_seed_row_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3)
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : SolvableSeedRow F L g := by
  let := chosen.elementary
  obtain ⟨htwo,hphi,_⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  let q := QuotientGroup.mk' F.uhatAction.ker
  let N := dotImage F F.uhatAction (F.Li L 1)
  let A := dotImage F F.uhatAction (conjugate F.ZU g)
  let := source_dot_Li_one_normal_of_symmetricThreePair_at d earlier hq chosen structural F model
  let := source_actor_elementary_at d earlier hq chosen structural alternatives F hne g hgP hgH
  have hAX : A ≤ dotImage F F.uhatAction (F.X g) :=
    map_mono (comap_mono (F.conjugate_ZU_le_X g))
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAX
  have hpL : IsPPerfect 2 (F.Li L 1) := by
    change IsPPerfect 2 ((pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype)
    exact isPPerfect_embedded_pResidual 2 _
  let f : F.Li L 1 →* N :=
    (q.comp (inclusion ((F.Li_le L 1).trans inf_le_right))).codRestrict N
      (fun k => mem_map_of_mem q k.property)
  have hfs : Function.Surjective f := by
    rintro ⟨x,k,hk,rfl⟩
    exact ⟨⟨k,hk⟩,rfl⟩
  let S := (T.subtype (F.invariant 1)).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  obtain ⟨hc,hm,hs⟩ := SymmetricThreeProduct.marked_normalClosure model N A
    (hpL.of_surjective f hfs)
    (solvableRow_source_solvable_point_order_at d earlier hq chosen structural alternatives F hne model)
    (source_earlier_conjugate_center_ne_bot_at d earlier hq chosen structural alternatives F hne hZ g hgP hgH)
    (solvableRow_source_solvable_center_centralizes_point_image_at d earlier hq chosen structural alternatives F hne model g hgP) S
  have hAH : conjugate F.ZU g ≤ F.H := by
    intro z hz
    exact (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP ⟨z,hz⟩).property
  have hK : solvableSeedActor F g =
      conjugateSpanBy ((conjugate F.ZU g).subgroupOf F.H) ⊤ := by
    apply map_injective F.H.subtype_injective
    rw [solvableSeedActor_map F chosen.normalizes g hgP,map_conjugateSpanBy,
      map_subgroupOf_eq_of_le hAH,←MonoidHom.range_eq_map,range_subtype]
  have hKm : (solvableSeedActor F g).map q = conjugateSpanBy A ⊤ := by
    rw [hK,map_conjugateSpanBy,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rfl
  refine ⟨?_,?_,hc⟩
  · rw [hKm]
    exact hm
  · rw [hKm]
    exact hs
theorem source_seed_exclusion_of_solvable_model_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3)
    (hne : ¬ IsMulCommutative F.U)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) : centralLTSeed F L = ⊥ := by
  let := chosen.elementary
  obtain ⟨htwo,hphi,_⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  by_cases hZ : F.ZU = F.Vi 1
  · apply le_bot_iff.mp
    intro z hz
    have hzP := (source_centralLT_seed_at d earlier hq chosen structural alternatives F).2.1 hz
    rw [hZ] at hzP
    exact (source_point_inf_centerLT_at d earlier hq chosen structural F).le ⟨hzP,hz.1⟩
  · obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
    exact source_seed_exclusion_of_symmetricThreePair_at d earlier hq chosen structural alternatives F hne
      g hgP hgH (source_solvable_seed_row_at d earlier hq chosen structural alternatives F hne hZ model g hgP hgH) model
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end
