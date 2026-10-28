module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.KernelSylow

/-!
# Literal b=2 quotient actions and the characteristic-two contradiction

Short distances and the actual kernel Sylows place both critical centers
inside the intermediate vertex core. The literal D intersection gives the
mixed commutator bound and complementary quotient images. A chosen actor
conjugating the two neighbors supplies fixed-space generation. The paired
adjacent-core calculation proves quadraticity. Consequently the earlier
center-line indices compute the two core-section orders, force equal field
orders and identify each Q/Z with its actual natural quotient action.
The involution-lifting argument then contradicts noncommutation.

The original F1.11 application retains the reduced-completion inclusion,
the full original parabolic cores and the original marked line indices.
No original Sylow is identified with the reduced Borel core.

This is a conditional calculation within 10.6. `BTwoLocalGeometry` still
requires the source core span, D=Z, the actor conjugator and Sylow image,
and the original fixed-preimage assertion. Constructing these from the
noncentral branch remains with this Chapter 10 proof; this module does not
claim an unconditional exclusion or prove 10.9/10.10.

Source: DGS, *Groups and Graphs* (1985), 10.3--10.6, printed pp.154--158;
the natural-center line indices come from 7.1, printed pp.126--127.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise MatrixGroups commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G]

/-- The remaining local geometry in 10.6, with the literal D intersection
and the original actor map. Its construction is still a Chapter 10 obligation. -/
structure BTwoLocalGeometry (F : Bool → Subgroup G) (t v w u : Vertex F)
    (k : Type*) [Field k] [Finite k] [CharP k 2] where
  actor : Subgroup G
  actor_le : actor ≤ stabilizer F w
  core_le : Q F w ≤ actor
  quotient : actor →* SL(2,k)
  onto : Function.Surjective quotient
  kernel : quotient.ker = (Q F w).subgroupOf actor
  sylow : Sylow 2 SL(2,k)
  actor_image : ((Z F t).subgroupOf actor).map quotient = sylow
  conjugator : actor
  moves : (conjugator : G) • v = u
  span : Q F w = (Z F v ⊔ Z F u) ⊔ D F v u
  intersection : D F v u = Z F w
  fixed_preimage : ∀ x ∈ Q F w,
    (∀ a ∈ actor, ⁅a,x⁆ ∈ Z F w) → x ∈ Z F w

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]

/-- Source b=2 and the actual kernel Sylows supply both neighbor-core
placements. Critical-center normalization and D=Z supply the commutator bound;
short-distance centralization supplies the fixed-generator premise. -/
def BTwoLocalGeometry.corePairAction (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (hb : b (family P) = 2)
    {t v w u : Vertex (family P)}
    (htv : (graph (family P)).Adj t v) (hvw : (graph (family P)).Adj v w)
    (huw : (graph (family P)).Adj u w) (hc : IsCriticalPair (family P) v u)
    (d : BTwoLocalGeometry (family P) t v w u k)
    (hquad : ⁅Z (family P) t,⁅Z (family P) t,Q (family P) w⁆⁆ ≤ Z (family P) w) :
    CorePairAction d.actor (Q (family P) w) (Z (family P) w)
      (Z (family P) v) (Z (family P) u) (Z (family P) t) k := by
  let := finite_endpoints h
  have hZQ (x : Vertex (family P)) : Z (family P) x ≤ Q (family P) x := by
    intro z hz
    exact ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h x).1 hz)).1
  refine {
    core_le := d.core_le
    kernel_le := hZQ w
    normalized_core := ?_
    normalized_kernel := ?_
    left_le := graph_Z_le_Q_of_short h hS (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hvw,hb]; decide)
    right_le := graph_Z_le_Q_of_short h hS (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr huw,hb]; decide)
    span := d.span.trans (congrArg ((Z (family P) v ⊔ Z (family P) u) ⊔ ·) d.intersection)
    commutator := ?_
    conjugator := d.conjugator
    conjugate := ?_
    quotient := d.quotient
    onto := d.onto
    kernel := d.kernel
    sylow := d.sylow
    actor_image := d.actor_image
    fixed_left := ?_
    quadratic_bound := hquad
    fixed_preimage := d.fixed_preimage }
  · exact d.actor_le.trans ((stabilizer (family P) w).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  · exact d.actor_le.trans ((normal_subgroupOf_iff_le_normalizer
      (Z_le_stabilizer (family P) w)).mp (Z_normal (family P) w))
  · have hi := (criticalPair_centers (family P) h.generate hc).2
    exact hi.trans ((inf_le_inf (hZQ v) (hZQ u)).trans d.intersection.le)
  · exact (congrArg (Z (family P)) d.moves).symm.trans
      (Z_translate (family P) (d.conjugator : G) v)
  · have he : ⁅Z (family P) t,Z (family P) v⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr
        (graph_centers_commute_of_short h hS (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr htv,hb]; decide))
    exact he.le.trans bot_le

/-- D is the literal intersection of the two endpoint cores. Thus the
two center images in Q/Z are complementary; their conjugacy computes the
core index as the square of the original critical-center line index. -/
theorem BTwoLocalGeometry.section_index (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (hb : b (family P) = 2)
    {t v w u : Vertex (family P)}
    (_htv : (graph (family P)).Adj t v) (hvw : (graph (family P)).Adj v w)
    (huw : (graph (family P)).Adj u w) (hc : IsCriticalPair (family P) v u)
    (d : BTwoLocalGeometry (family P) t v w u k) :
    (Z (family P) w).relIndex (Q (family P) w) =
      ((Q (family P) u).relIndex (Z (family P) v))^2 := by
  let := finite_endpoints h
  have hZQ (x : Vertex (family P)) : Z (family P) x ≤ Q (family P) x := by
    intro z hz
    exact ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h x).1 hz)).1
  let := graph_Z_elementary h v
  let := graph_Z_elementary h u
  have hAQ : Z (family P) v ≤ Q (family P) w := graph_Z_le_Q_of_short h hS
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hvw,hb]; decide)
  have hCQ : Z (family P) u ≤ Q (family P) w := graph_Z_le_Q_of_short h hS
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr huw,hb]; decide)
  have hspan : Q (family P) w = (Z (family P) v ⊔ Z (family P) u) ⊔ Z (family P) w :=
    d.span.trans (congrArg ((Z (family P) v ⊔ Z (family P) u) ⊔ ·) d.intersection)
  have hcomm : ⁅Z (family P) v,Z (family P) u⁆ ≤ Z (family P) w :=
    (criticalPair_centers (family P) h.generate hc).2.trans
      ((inf_le_inf (hZQ v) (hZQ u)).trans d.intersection.le)
  have hnZ := (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer (family P) w)).mp
    (Z_normal (family P) w)
  let : ((Z (family P) w).subgroupOf (Q (family P) w)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hZQ w)).mpr
      ((Q_le_stabilizer (family P) w).trans hnZ)
  let := pair_quotient_elementary (Q (family P) w) (Z (family P) w)
    (Z (family P) v) (Z (family P) u) hAQ hCQ (hZQ w) hspan hcomm
  obtain ⟨σ,e,_⟩ := exists_canonical d.actor (Q (family P) w) (Z (family P) w)
    d.core_le (hZQ w)
    (d.actor_le.trans ((stabilizer (family P) w).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))
    (d.actor_le.trans hnZ) d.quotient d.onto d.kernel
  have hZv : Z (family P) w ≤ Q (family P) v :=
    graph_Z_le_Q_of_short h hS (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hvw.symm,hb]; decide)
  have hZu : Z (family P) w ≤ Q (family P) u :=
    graph_Z_le_Q_of_short h hS (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr huw.symm,hb]; decide)
  have hinter : (Z (family P) v ⊔ Z (family P) w) ⊓
      (Z (family P) u ⊔ Z (family P) w) = Z (family P) w := by
    apply le_antisymm
    · exact (inf_le_inf (sup_le (hZQ v) hZv) (sup_le (hZQ u) hZu)).trans d.intersection.le
    · exact le_inf le_sup_right le_sup_right
  have hi := e.section_index_square_of_conjugate_pair (Z (family P) v) (Z (family P) u)
    hAQ hCQ hspan hinter d.conjugator
    ((congrArg (Z (family P)) d.moves).symm.trans (Z_translate (family P) (d.conjugator : G) v))
    (d.actor_le.trans hnZ)
  have he : (Z (family P) w).relIndex (Z (family P) v) =
      (Q (family P) u).relIndex (Z (family P) v) := by
    have hm : Z (family P) v ⊓ Z (family P) w = Z (family P) v ⊓ Q (family P) u := by
      rw [←d.intersection,D,←inf_assoc,inf_of_le_left (hZQ v)]
    rw [←inf_relIndex_left (Z (family P) v) (Z (family P) w),hm,inf_relIndex_left]
  exact hi.trans (congrArg (· ^ 2) he)

/-- The paired p157 cross-indices exclude the literal noncommuting b=2
configuration, with all elementary and central-kernel facts discharged. -/
theorem bTwo_paired_local_geometry_impossible
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (hb : b (family P) = 2) {t v w u : Vertex (family P)}
    (htv : (graph (family P)).Adj t v) (hvw : (graph (family P)).Adj v w)
    (huw : (graph (family P)).Adj u w)
    (hc₀ : IsCriticalPair (family P) w t) (hc₁ : IsCriticalPair (family P) v u)
    (hne₀ : ⁅Z (family P) w,Z (family P) t⁆ ≠ ⊥)
    (hne₁ : ⁅Z (family P) v,Z (family P) u⁆ ≠ ⊥)
    {k₀ k₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
    [Field k₁] [Finite k₁] [CharP k₁ 2]
    (d₀ : BTwoLocalGeometry (family P) u w v t k₀)
    (d₁ : BTwoLocalGeometry (family P) t v w u k₁)
    (hcross₀ : (Z (family P) v).relIndex (Q (family P) v) = Nat.card k₁ ^ 2)
    (hcross₁ : (Z (family P) w).relIndex (Q (family P) w) = Nat.card k₀ ^ 2) : False := by
  let := finite_endpoints h
  let : ∀ x : Vertex (family P), Finite (Q (family P) x) := fun x =>
    Finite.of_injective (inclusion (Q_le_stabilizer (family P) x)) (inclusion_injective _)
  let : ∀ x : Vertex (family P), IsElementaryAbelian 2 (Z (family P) x) :=
    graph_Z_elementary h
  have hq₀ := bTwo_quadratic_core_commutator h hS hb huw hvw.symm hc₁ d₁.span d₁.intersection
  have hq₁ := bTwo_quadratic_core_commutator h hS hb htv hvw hc₀ d₀.span d₀.intersection
  let c₀ := d₀.corePairAction h hS hb huw hvw.symm htv hc₀ hq₀
  let c₁ := d₁.corePairAction h hS hb htv hvw huw hc₁ hq₁
  exact c₀.paired_impossible c₁
    (le_centralizer_iff.mp (graph_Q_centralizes_Z h v))
    (le_centralizer_iff.mp (graph_Q_centralizes_Z h w)) hne₀ hne₁ hcross₀ hcross₁

/-- The natural-center line indices from Chapter 7 supply both core/center
cross-indices. No core quotient size or equal-field premise is assumed. -/
theorem bTwo_paired_local_geometry_impossible_of_line_indices
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (hb : b (family P) = 2) {t v w u : Vertex (family P)}
    (htv : (graph (family P)).Adj t v) (hvw : (graph (family P)).Adj v w)
    (huw : (graph (family P)).Adj u w)
    (hc₀ : IsCriticalPair (family P) w t) (hc₁ : IsCriticalPair (family P) v u)
    (hne₀ : ⁅Z (family P) w,Z (family P) t⁆ ≠ ⊥)
    (hne₁ : ⁅Z (family P) v,Z (family P) u⁆ ≠ ⊥)
    {k₀ k₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
    [Field k₁] [Finite k₁] [CharP k₁ 2]
    (d₀ : BTwoLocalGeometry (family P) u w v t k₀)
    (d₁ : BTwoLocalGeometry (family P) t v w u k₁)
    (hline₀ : (Q (family P) u).relIndex (Z (family P) v) = Nat.card k₀)
    (hline₁ : (Q (family P) t).relIndex (Z (family P) w) = Nat.card k₁) : False := by
  apply bTwo_paired_local_geometry_impossible h hS hb htv hvw huw
    hc₀ hc₁ hne₀ hne₁ d₀ d₁
  · exact (d₀.section_index h hS hb huw hvw.symm htv hc₀).trans (congrArg (· ^ 2) hline₁)
  · exact (d₁.section_index h hS hb htv hvw huw hc₁).trans (congrArg (· ^ 2) hline₀)

namespace Reduction
open DGS85.Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

/-- The original full-core index equals the reduced graph section index.
Only the literal inclusion of the reduced completion is used. -/
theorem original_center_core_index (h : HypothesisF11 L S) (i : Bool) :
    ((Z F (base F i)).map (G₀ L S).subtype).relIndex
      ((parabolic L S (if i then 1 else 0)).pCoreIn 2) =
        (Z F (base F i)).relIndex (Q F (base F i)) := by
  have hi := relIndex_map_map_of_injective (Z F (base F i)) (Q F (base F i))
    (G₀ L S).subtype_injective
  rwa [reduced_base_Q_map h i] at hi

/-- Literal conditional F1.11 application of the noncentral b=2 exclusion.
The cross-indices refer to the original full parabolic cores, not unmarked
isomorphic groups. The local geometry and these counts remain explicit
Chapter 10 obligations. -/
theorem original_bTwo_noncentral_exclusion_from_local_geometry
    (h : HypothesisF11 L S) (hb : b F = 2) {t u : Vertex F}
    (ht : (graph F).Adj t α) (hu : (graph F).Adj u β)
    (hc₀ : IsCriticalPair F β t) (hc₁ : IsCriticalPair F α u)
    (hne₀ : ⁅Z F β,Z F t⁆ ≠ ⊥) (hne₁ : ⁅Z F α,Z F u⁆ ≠ ⊥)
    {k₀ k₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
    [Field k₁] [Finite k₁] [CharP k₁ 2]
    (d₀ : BTwoLocalGeometry F u β α t k₀)
    (d₁ : BTwoLocalGeometry F t α β u k₁)
    (hcross₀ : ((Z F α).map (G₀ L S).subtype).relIndex
      ((parabolic L S 0).pCoreIn 2) = Nat.card k₁ ^ 2)
    (hcross₁ : ((Z F β).map (G₀ L S).subtype).relIndex
      ((parabolic L S 1).pCoreIn 2) = Nat.card k₀ ^ 2) : False := by
  have hadj : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base F false true⟩
  apply bTwo_paired_local_geometry_impossible (reduced_triple h)
    (reduced_kernel_sylow h) hb ht hadj hu hc₀ hc₁ hne₀ hne₁ d₀ d₁
  · exact (original_center_core_index h false).symm.trans hcross₀
  · exact (original_center_core_index h true).symm.trans hcross₁
/-- Original marked application using only the earlier natural-center line
indices. Both indices retain the inclusion into the original completion;
the larger core-section indices are proved by the literal D calculation. -/
theorem original_bTwo_noncentral_exclusion_of_line_indices
    (h : HypothesisF11 L S) (hb : b F = 2) {t u : Vertex F}
    (ht : (graph F).Adj t α) (hu : (graph F).Adj u β)
    (hc₀ : IsCriticalPair F β t) (hc₁ : IsCriticalPair F α u)
    (hne₀ : ⁅Z F β,Z F t⁆ ≠ ⊥) (hne₁ : ⁅Z F α,Z F u⁆ ≠ ⊥)
    {k₀ k₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
    [Field k₁] [Finite k₁] [CharP k₁ 2]
    (d₀ : BTwoLocalGeometry F u β α t k₀)
    (d₁ : BTwoLocalGeometry F t α β u k₁)
    (hline₀ : ((Q F u).map (G₀ L S).subtype).relIndex
      ((Z F α).map (G₀ L S).subtype) = Nat.card k₀)
    (hline₁ : ((Q F t).map (G₀ L S).subtype).relIndex
      ((Z F β).map (G₀ L S).subtype) = Nat.card k₁) : False := by
  have hadj : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base F false true⟩
  apply bTwo_paired_local_geometry_impossible_of_line_indices (reduced_triple h)
    (reduced_kernel_sylow h) hb ht hadj hu hc₀ hc₁ hne₀ hne₁ d₀ d₁
  · rwa [relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective] at hline₀
  · rwa [relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective] at hline₁

end Reduction

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
