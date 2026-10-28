module
public import Stellmacher.SectionEight.EightFourSourceNineCentralizerSize
public import Stellmacher.SectionOne.OneSevenFixedSpaceFixer
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# The adjacent cores generate the Sylow in the final case of (8.4)

Under the nontrivial fixed-closure branch, the initial and first-step two-cores
join to the distinguished Sylow subgroup. The fixed subgroup has order four,
so its Sylow centralizer has index at most two. The faithful fixed-space fixer
is exactly the barred offender join; the opposite-center closure realizes this
image. Hence that Sylow centralizer is contained in the join of the two cores.

The first-step core cannot centralize the fixed subgroup. Otherwise normality
of that core in its stabilizer would extend centralization to the whole fixed
closure, contrary to the already proved noncommuting-core case. The core join
therefore strictly contains the index-at-most-two centralizer and equals S.
This supplies the missing generation hypothesis for the terminal invariant
subgroup argument, with the original witness and source-nine data unchanged.

The local theorem and its fixed-centralizer helper use the same local graph
and supplied quotient witness. The generic normal-closure argument is unchanged;
the original canonical statement is retained through the context and data adapters.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.4), printed p.40,
final paragraph; `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem fixed_centralizer_le_adjacent_cores
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S) :
    S ⊓ Subgroup.centralizer (w.oneJFixedPoints S : Set H) ≤
      QAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Z := ZAt Γ cp.a
  let h := ctx.sectionSeven
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Z w.action
  have hfirst := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  have hlocal := (local_quotient_sylow_action_setup h Γ cp w).1
  obtain ⟨hSP, U, hU⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  have hUS : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  let Ub := U.mapSurjective w.surjective
  let Sb := (S.subgroupOf P).map w.projection
  have hUb : (Ub : Subgroup w.X) = Sb := by
    change (U : Subgroup P).map w.projection = _
    rw [hUS]
  have hfixer := SectionOne.oneSeven_fixedSpace_fixer_eq_oneJ_unconditional hlocal Ub
  rw [hUb] at hfixer
  have himage := eight_four_opposite_closure_image_local ctx hcenter w hbranch
  have hKS : oppositeClosureLocal ctx ≤ S := (opposite_closure_normal_sylow_local ctx).1
  intro actor hactor
  let native : P := ⟨actor, hSP hactor.1⟩
  have hJ : w.projection native ∈ SectionOne.oneJ (V := Z) Sb := by
    rw [← hfixer, mem_fixingSubgroup_iff]
    intro point hpoint
    apply Subtype.ext
    change ((w.action (w.projection native)) point : H) = point
    rw [w.action_compatible]
    have hF : (point : H) ∈ w.oneJFixedPoints S :=
      Subgroup.mem_map_of_mem Z.subtype hpoint
    have hcomm := Subgroup.mem_centralizer_iff.mp hactor.2 (point : H) hF
    change (point : H) * actor = actor * (point : H) at hcomm
    rw [← hcomm, mul_inv_cancel_right]
  rw [← himage] at hJ
  obtain ⟨representative, hrepresentative, heq⟩ := hJ
  have hkernel : native * representative⁻¹ ∈ w.projection.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq, mul_inv_cancel]
  rw [w.kernel_eq] at hkernel
  have hdiff : actor * (representative : H)⁻¹ ∈ QAt Γ cp.a := by
    change actor * (representative : H)⁻¹ ∈ q Γ cp.a
    rw [← (lemma_seven_four h Γ cp).edge_centralizer]
    exact ⟨S.mul_mem hactor.1 (S.inv_mem (hKS hrepresentative)), hkernel.2⟩
  have hrepCore : (representative : H) ∈ QAt Γ cp.firstStep :=
    opposite_closure_le_next_core_local ctx hrepresentative
  have hproduct := (QAt Γ cp.a ⊔ QAt Γ cp.firstStep).mul_mem
    ((show QAt Γ cp.a ≤ QAt Γ cp.a ⊔ QAt Γ cp.firstStep from le_sup_left) hdiff)
    ((show QAt Γ cp.firstStep ≤ QAt Γ cp.a ⊔ QAt Γ cp.firstStep from le_sup_right) hrepCore)
  simpa only [inv_mul_cancel_right] using hproduct

private theorem normal_closure_centralizes_normal
    {H : Type u} [Group H] (F K P : Subgroup H)
    (hKP : K ≤ P) (hnormal : (K.subgroupOf P).Normal)
    (hcentral : F ≤ Subgroup.centralizer (K : Set H)) :
    (Subgroup.normalClosure (F.subgroupOf P : Set P)).map P.subtype ≤
      Subgroup.centralizer (K : Set H) := by
  let _ := hnormal
  have hnative : F.subgroupOf P ≤ Subgroup.centralizer (K.subgroupOf P : Set P) := by
    intro point hpoint
    rw [Subgroup.mem_centralizer_iff]
    intro actor hactor
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hcentral hpoint) actor hactor
  have hclosure := Subgroup.normalClosure_le_normal hnative
  rintro _ ⟨point, hpoint, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro actor hactor
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_iff.mp (hclosure hpoint) ⟨actor, hKP hactor⟩ hactor)

section LocalProof

variable {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineLocalData ctx F)
    (hlen : 2 < ctx.criticalPath.length)

include hcenter w hbranch hbase hcov hsub hformula configuration hlen

/-- In the final noncommuting-core case, the adjacent cores generate S. -/
public theorem eight_four_source_nine_core_generation_local :
    S = QAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let seed := w.oneJFixedPoints S
  let C := ⨆ vertex, F vertex cp.firstStep
  let Q := QAt Γ cp.firstStep
  let centralizer := S ⊓ Subgroup.centralizer (seed : Set H)
  let joined := QAt Γ cp.a ⊔ Q
  let hyp := ctx.sectionSeven
  have hcores := SevenSix.local_cores_le_edge_sylow hyp Γ cp
  have hjoined : joined ≤ S := sup_le hcores.1 hcores.2
  have hcentralizer : centralizer ≤ joined :=
    fixed_centralizer_le_adjacent_cores ctx hcenter w hbranch
  have hnoncentral : ¬ Q ≤ Subgroup.centralizer (seed : Set H) := by
    intro hcomm
    have hnormal : (Q.subgroupOf P).Normal := by
      rw [show Q = (pCore 2 P).map P.subtype from Γ.twoCoreAt_def cp.firstStep]
      change (((pCore 2 P).map P.subtype).comap P.subtype).Normal
      rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
      infer_instance
    have hQP : Q ≤ P := by
      rw [show Q = (pCore 2 P).map P.subtype from Γ.twoCoreAt_def cp.firstStep]
      exact Subgroup.map_subtype_le _
    have hCeq := (eight_four_edge_star_closure_local ctx w F hbase hcov hsub hformula).1
    have hCcentral : C ≤ Subgroup.centralizer (Q : Set H) := by
      change C = _ at hCeq
      rw [hCeq]
      exact normal_closure_centralizes_normal seed Q P hQP hnormal
        (Subgroup.le_centralizer_iff.mp hcomm)
    apply eight_four_source_nine_noncommuting_core_local ctx hcenter w hbranch
      F hbase hcov hsub hformula configuration hlen
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hCcentral.trans (Subgroup.centralizer_le inf_le_right))
  have hcard : Nat.card seed = 4 := eight_four_source_nine_fixed_card_four_local
    ctx hcenter w hbranch F hbase hcov hsub hformula configuration hlen
  have helementary : IsElementaryAbelian 2 seed := by
    have hneighbor := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
    let _ := SevenSix.z_isElementaryAbelian_of_neighbor hyp Γ hneighbor
    have hseed : seed ≤ ZAt Γ cp.a := Subgroup.map_subtype_le _
    refine { toIsMulCommutative := { is_comm := ⟨?_⟩ }, exponent_dvd_p := ?_ }
    · intro first second
      apply Subtype.ext
      change (first : H) * (second : H) = (second : H) * (first : H)
      exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ZAt Γ cp.a)).comm
        ⟨first, hseed first.property⟩ ⟨second, hseed second.property⟩)
    · apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro point
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (point : H) (hseed point.property)
  have hnorm : S ≤ Subgroup.normalizer (seed : Set H) :=
    cp.S_le_edge_stabilizers.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (eight_four_edge_fixed_normal_local ctx hcenter w hbranch).1).mp
          (eight_four_edge_fixed_normal_local ctx hcenter w hbranch).2)
  obtain ⟨_, nativeSylow, hnativeSylow⟩ := (SevenSix.edge_sylow_data hyp Γ cp).1
  have hStwo : IsPGroup 2 S := hnativeSylow ▸ nativeSylow.isPGroup'.map _
  have hindex : centralizer.relIndex S ≤ 2 := by
    rw [show centralizer = S ⊓ Subgroup.centralizer (seed : Set H) from rfl,
      Subgroup.inf_relIndex_left]
    exact two_group_normalizing_four_centralizer_index_le_two seed S helementary hcard
      hStwo hnorm
  have hstrict : ¬ joined ≤ centralizer := by
    intro hle
    exact hnoncentral (le_sup_right.trans (hle.trans inf_le_right))
  have hprod := Subgroup.relIndex_mul_relIndex centralizer joined S hcentralizer hjoined
  have hpositive : centralizer.relIndex joined ≠ 0 :=
    ne_zero_of_dvd_ne_zero Nat.card_pos.ne' (Subgroup.relIndex_dvd_card _ _)
  have hpositive' : joined.relIndex S ≠ 0 :=
    ne_zero_of_dvd_ne_zero Nat.card_pos.ne' (Subgroup.relIndex_dvd_card _ _)
  have hne : centralizer.relIndex joined ≠ 1 := by
    intro hone
    exact hstrict (Subgroup.relIndex_eq_one.mp hone)
  have hlarge : 2 ≤ centralizer.relIndex joined := by omega
  have hlarge' : 1 ≤ joined.relIndex S := by omega
  have hone : joined.relIndex S = 1 := by nlinarith
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hone) hjoined

end LocalProof

section CanonicalProof

variable {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineData ctx F)
    (hlen : 2 < ctx.criticalPath.length)

include hcenter w hbranch hbase hcov hsub hformula configuration hlen

public theorem eight_four_source_nine_core_generation :
    S = QAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep := by
  exact eight_four_source_nine_core_generation_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen

end CanonicalProof

end Stellmacher.SectionEight
