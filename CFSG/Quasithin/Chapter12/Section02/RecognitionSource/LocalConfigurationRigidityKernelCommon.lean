module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelBlockBridge
public import Theory.Representation.FirstCohomologyAutomorphism.Subkernel
public import Theory.GroupTheory.FixedSupplementCentralizer

/-!
# Common factors and literal kernel displacement in 12.2.25

The two Sylow centralizers have trivial intersection: T normalizes both,
L centralizes their intersection, and the escaping pair I centralizes it.
The original uniqueness theorem therefore eliminates this common factor.
The action kernel of U on V also makes U disjoint from C_T(L), so these
mutually normalizing subgroups commute.

For Q=C_T(V)=O₂(LT), two-perfect commutator idempotence gives [Q,L]=V.
Comparing actual conjugations shows that O₂(L) centralizes Q; hence the
connecting cocycles descend through the literal L/O₂(L). The final theorem
splits C_T(UV) over U∩V using the already proved decomposition of C_T(U).
No dimension branch, splitting of Q, or equality O₂(L)=V is assumed.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
12.2.25, printed p.805, first three paragraphs; C.1.13, pp.124--125.
The remaining kernel splitting and Thompson calculation are owned by
qt-d-12225-common-centralizers, with final source assembly in
qt-d-12213-local-rigidity.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel

omit [Finite G] in
theorem sylow_normalizes_component_centralizer (D : ChosenModule T L V) :
    (T : Subgroup G) ≤ normalizer
      (((T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
  (le_inf (T : Subgroup G).le_normalizer
    (D.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
    inf_normalizer_le_normalizer_inf

omit [Finite G] in
theorem sylow_normalizes_pair_centralizer (C : CyclicLocalAnalysis T L V d H P U) :
    (T : Subgroup G) ≤ normalizer
      (((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G) : Subgroup G) : Set G) :=
  (le_inf (T : Subgroup G).le_normalizer
    ((C.sylow_le_overgroup.trans C.pair_normal).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf

omit [Finite G] in
theorem kernel_disjoint (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d) :
    Disjoint V ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  rw [disjoint_iff]
  exact bot_unique ((inf_le_inf_left V inf_le_right).trans (A.fixed_eq_bot D).le)

omit [Finite G] in
theorem core_disjoint_component_centralizer
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) :
    Disjoint U ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  apply disjoint_def.mpr
  intro x hxU hxZ
  have hxV : x ∈ V := (C.action_kernel.le
    ⟨hxU, centralizer_le D.le_component hxZ.2⟩).2
  exact disjoint_def.mp (kernel_disjoint D A) hxV hxZ

omit [Finite G] in
theorem component_centralizer_le_core_centralizer
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) ≤ centralizer (U : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  have hc : ⁅(T : Subgroup G) ⊓ centralizer (L : Set G), U⁆ ≤
      U ⊓ ((T : Subgroup G) ⊓ centralizer (L : Set G)) :=
    le_inf (le_normalizer_iff_commutator_le_right.mp
      (inf_le_left.trans C.sylow_normalizes_core))
      (le_normalizer_iff_commutator_le_left.mp
        (C.core_le_sylow.trans (sylow_normalizes_component_centralizer D)))
  exact hc.trans (disjoint_iff.mp (core_disjoint_component_centralizer D A C)).le

/-- The literal common central factor vanishes, before either cohomology case. -/
theorem common_trivial (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (C : CyclicLocalAnalysis T L V d H P U) :
    ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓
      ((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) = ⊥ := by
  let B := ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓
      ((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G))
  have hLB : L ≤ normalizer (B : Set G) :=
    (le_centralizer_iff.mp (inf_le_left.trans inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hIB : cyclicPairJoin P U V ≤ normalizer (B : Set G) :=
    (le_centralizer_iff.mp (inf_le_right.trans inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    (le_inf (sylow_normalizes_component_centralizer D)
      (sylow_normalizes_pair_centralizer C)).trans inf_normalizer_le_normalizer_inf
  exact chosen_common_normal_subgroup_eq_bot h D C
    (inf_le_left.trans (inf_le_left.trans le_sup_right)) (sup_le hLB hTB) hIB

/-- The displacement of the actual kernel under L lies in the original V. -/
theorem kernel_commutator_eq
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) :
    ⁅(T : Subgroup G) ⊓ centralizer (V : Set G), L⁆ = V := by
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  have hLQ : L ≤ normalizer (Q : Set G) := by
    rw [show Q = (L ⊔ (T : Subgroup G)).pCoreIn 2 from
      LiteralNaturalBlock.kernel_eq_local_core D A C]
    exact le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hQL : Q ≤ normalizer (L : Set G) := inf_le_left.trans D.sylow_normalizes_component
  have hq : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  have hc : ⁅Q,L⁆ ≤ L.pCoreIn 2 := le_pCoreIn_of_normalizes
    (hq.to_le (le_normalizer_iff_commutator_le_left.mp hLQ))
    (le_normalizer_iff_commutator_le_right.mp hQL)
    (normalizer_commutator_ge_right Q L)
  have hid := commutator_isPPerfect_idempotent L Q C.block.2.1.twoPerfect hq hLQ
  apply le_antisymm
  · exact hid.symm.le.trans ((commutator_mono hc le_rfl).trans
      (LiteralNaturalBlock.component_commutator_eq D A C).le)
  · let := D.elementary
    exact D.eq_commutator.le.trans (commutator_mono
      (le_inf D.le_sylow (le_centralizer V)) le_rfl)

/-- The two-core of L centralizes the literal kernel, so its displacement
cocycles descend through L/O₂(L), with no assumption O₂(L)=V. -/
theorem component_core_centralizes_kernel
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) :
    L.pCoreIn 2 ≤ centralizer
      (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
  let N := V.subgroupOf L
  let := D.elementary
  let : IsElementaryAbelian 2 N := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe D.le_component).toMonoidHom
    (subgroupOfEquivOfLe D.le_component).injective
  have hNC : pCore 2 L ≤ centralizer (N : Set L) := by
    intro x hx v hv
    apply Subtype.ext
    exact D.core_centralizes ((pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component))
        (mem_map_of_mem L.subtype hx)) v hv
  have hcomm : ⁅pCore 2 L, (⊤ : Subgroup L)⁆ ≤ N := by
    intro x hx
    exact (LiteralNaturalBlock.component_commutator_eq D A C).le (by
      have hm := mem_map_of_mem L.subtype hx
      rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hm
      exact hm)
  have hZ : N ⊓ center L = ⊥ := by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp ((A.fixed_eq_bot D).le ⟨hx.1, fun l hl =>
      congrArg Subtype.val (mem_center_iff.mp hx.2 ⟨l,hl⟩)⟩)
  intro x hx q hq
  obtain ⟨x,hx,rfl⟩ := hx
  let α : MulAut L := L.normalizerMonoidHom
    ⟨q, D.sylow_normalizes_component hq.1⟩
  have hd (l : L) : α l * l⁻¹ ∈ N :=
    (kernel_commutator_eq D A C).le (commutator_mem_commutator hq l.property)
  have hf (v : L) (hv : v ∈ N) : α v = v := by
    apply Subtype.ext
    change q * (v : G) * q⁻¹ = v
    rw [← hq.2 v hv, mul_inv_cancel_right]
  have hh := Representation.OneCohomology.automorphism_fixes_centralizing_layer
    N (pCore 2 L) hNC hcomm hZ α hd hf x hx
  have he := congrArg Subtype.val hh
  change q * (x : G) * q⁻¹ = x at he
  exact mul_inv_eq_iff_eq_mul.mp he

/-- The centralizer of UV in the Sylow subgroup splits over the original
intersection U∩V. This is the second equality in the opening paragraph. -/
theorem join_centralizer_split
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    (T : Subgroup G) ⊓ centralizer ((U ⊔ V : Subgroup G) : Set G) =
      (U ⊓ V) ⊔ ((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) := by
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  have hEU : E ≤ centralizer (U : Set G) := inf_le_right.trans
    (centralizer_le (show U ≤ cyclicPairJoin P U V from le_sup_right.trans le_sup_left))
  have hEV : E ≤ centralizer (V : Set G) := inf_le_right.trans
    (centralizer_le (show V ≤ cyclicPairJoin P U V from le_sup_right))
  have he : (T : Subgroup G) ⊓ centralizer ((U ⊔ V : Subgroup G) : Set G) =
      ((T : Subgroup G) ⊓ centralizer (U : Set G)) ⊓ centralizer (V : Set G) := by
    apply le_antisymm
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans
        (centralizer_le (show U ≤ U ⊔ V from le_sup_left))))
        (inf_le_right.trans (centralizer_le (show V ≤ U ⊔ V from le_sup_right)))
    · exact le_inf (inf_le_left.trans inf_le_left) (le_centralizer_iff.mp
        (sup_le (le_centralizer_iff.mp (inf_le_left.trans inf_le_right))
          (le_centralizer_iff.mp inf_le_right)))
  rw [he, C.sylow_centralizer_core_decomposition
    (by have := A.dimension.1; omega) (((structural G T L h).2.2 V D).1) D.le_sylow hnone]
  rw [sup_comm U E, inf_centralizer_sup_of_centralizing E U V
    (hEU.trans (Subgroup.centralizer_le_normalizer _)) hEV, C.action_kernel, sup_comm]

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
