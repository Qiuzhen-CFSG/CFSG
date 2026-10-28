module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableSeedRecognition
public import Theory.GroupTheory.Commutator.FixedSupplement
public import Theory.GroupAction.MaximalCosetOrbit
public import Theory.GroupTheory.ReducedNormal.SylowCentralSeed
public import Theory.GroupTheory.ReducedNormal.Equiv

/-!
# The central quotient in the solvable seed exclusion

The original marked actor moves VH and centralizes a hyperplane of Z(U).
Consequently VH supplements that hyperplane. Normal generation then gives
[Z(U),K] = [VH,K]. The checked S3 action on VH makes this the same
order-four plane, disjoint from C_Z(U)(K).

The literal C_Z(U)(K) is normal in H and contains the original point V1.
Thus the image of U in H/C_Z(U)(K) is elementary. The marked plane V2
has image of order two, fixed by the image Sylow subgroup; its conjugates
generate the image of U. The genuine B.2.13 theorem therefore makes this
image reduced. The original commutator plane survives with order four
in this same quotient.

These results discharge the central commutator, elementary-quotient and
reducedness steps of the solvable paragraph of 14.3.25. They do not yet
assert Z(U) = [VH,K] C_Z(U)(K), the subsequent equality of action kernels,
or the final seed exclusion. SolvableSeedRow remains the explicit earlier
marked-action premise. Its construction, the remaining seed and
centerlessness contradictions, and final source_centerless stay with
qt-d-hs-centerless-source; final LocalStructure discharge remains with
qt-d-hs-local-structure. The later action theorem assuming centerlessness
is not used here.

Source: Aschbacher--Smith 14.3.25, printed p.1001, and B.2.13, p.78,
refs/quasithin.pdf.
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

/-- The hyperplane fixed by the marked actor extends the commutator equality
from VH to the whole center, with the original normal closure K. -/
theorem source_solvable_center_commutator (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    ⁅F.ZU,conjugateSpanBy (conjugate F.ZU g) F.H⁆ =
      ⁅faithfulTestModule F L,conjugateSpanBy (conjugate F.ZU g) F.H⁆ := by
  let := chosen.elementary
  obtain ⟨hn,he,_,a,ha,hhat,hr,hsq⟩ := source_solvable_seed_rank_one d earlier hq chosen
    structural alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  let W := (faithfulTestModule F L).subgroupOf F.H
  let B := F.ZU ⊓ conjugate F.U g
  have hWZ := (source_faithful_test_reduced d earlier hq chosen structural alternatives F).1
  obtain ⟨hi,hc⟩ := source_center_axis d earlier hq chosen structural alternatives F hne g hgP hgH
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



/-- The source central fixed subgroup in the original H. -/
@[expose] def solvableCenterFixed (F : InvariantFlag T V 3) (g : G) : Subgroup F.H :=
  F.ZU.subgroupOf F.H ⊓ centralizer (solvableSeedActor F g : Set F.H)

instance solvableCenterFixed_normal (F : InvariantFlag T V 3) (g : G) :
    (solvableCenterFixed F g).Normal := by
  let : (F.ZU.subgroupOf F.H).Normal := normal_subgroupOf_of_le_normalizer F.H_normalizes_ZU
  exact inferInstanceAs (F.ZU.subgroupOf F.H ⊓ centralizer (solvableSeedActor F g : Set F.H)).Normal

/-- The whole-center commutator is the same order-four plane as [VH,K]
and meets the literal K-fixed center trivially. -/
theorem source_solvable_center_plane (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
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
  obtain ⟨hn,he,_,hc,hd⟩ := source_solvable_seed_kernel_and_plane d earlier hq chosen
    structural alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  have hWZ := (source_faithful_test_reduced d earlier hq chosen structural alternatives F).1
  have hZH : F.ZU ≤ F.H := (map_subtype_le (center F.U)).trans F.U_le_H
  have hWmap : W.map F.H.subtype = faithfulTestModule F L :=
    map_subgroupOf_eq_of_le (hWZ.trans hZH)
  have hZmap : Z.map F.H.subtype = F.ZU := map_subgroupOf_eq_of_le hZH
  have hKmap : K.map F.H.subtype = conjugateSpanBy (conjugate F.ZU g) F.H :=
    solvableSeedActor_map F chosen.normalizes g hgP
  have hcomm : ⁅Z,K⁆ = ⁅W,K⁆ := by
    apply (map_injective F.H.subtype_injective)
    rw [map_commutator,map_commutator,hWmap,hZmap,hKmap]
    exact source_solvable_center_commutator d earlier hq chosen structural alternatives
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



omit [Finite G] in
/-- The original point is killed in the source quotient by the fixed center. -/
theorem solvableCenterFixed_point (F : InvariantFlag T V 3) [IsMulCommutative V]
    (g : G) : (F.Vi 1).subgroupOf F.H ≤ solvableCenterFixed F g := by
  have hHC : F.H ≤ centralizer (F.Vi 1 : Set G) :=
    normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  intro z hz
  refine ⟨F.point_le_ZU (by decide) hz,?_⟩
  intro k hk
  apply Subtype.ext
  exact (hHC k.property z hz).symm

/-- The original U has elementary image in H/C_Z(U)(K). -/
theorem source_solvable_center_quotient_elementary (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (g : G) :
    IsElementaryAbelian 2 ((F.U.subgroupOf F.H).map
      (QuotientGroup.mk' (solvableCenterFixed F g))) := by
  let := chosen.elementary
  let C := solvableCenterFixed F g
  let q := QuotientGroup.mk' C
  let U := F.U.subgroupOf F.H
  have h := higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm,hsquare⟩ := F.localKernel_commutator_squares d.qtke L
    (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
    (h.sylow_normalizes structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape F alternatives)
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

/-- The original commutator plane survives in the same elementary quotient. -/
theorem source_solvable_center_quotient_plane (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    Nat.card ((⁅F.ZU.subgroupOf F.H,solvableSeedActor F g⁆ : Subgroup F.H).map
      (QuotientGroup.mk' (solvableCenterFixed F g))) = 4 := by
  obtain ⟨_,hc,hd⟩ := source_solvable_center_plane d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row
  rw [←relIndex_ker,QuotientGroup.ker_mk',←inf_relIndex_right,hd.symm.eq_bot,relIndex_bot_left]
  exact hc

/-- The elementary image of U in the original central quotient is reduced.
Its marked plane has order two and is centralized by the image of T. -/
theorem source_solvable_center_quotient_reduced (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    source_solvable_center_quotient_elementary d earlier hq chosen structural alternatives F g
  have hPU : F.Vi 2 ≤ F.U := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
  have hPH : F.Vi 2 ≤ F.H := hPU.trans F.U_le_H
  have hpoint : (F.Vi 1).subgroupOf F.H ≤ C := solvableCenterFixed_point F g
  have hVZ := (source_closure d earlier hq chosen structural alternatives F hne).2.2
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
  have h := higherRankHypothesis d earlier hq chosen
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
