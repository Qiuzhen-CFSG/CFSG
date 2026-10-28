module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.Actions
public import Theory.Representation.NormalElementaryQuotient.FixedQuotient
public import Theory.Representation.BinaryOffender.PPerfectFixedLift
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.ElementaryAbelian.Injective

/-!
# The literal neighborhood section modulo the residual centralizer

For any local group H between the vertex two-core and the full stabilizer,
the original radius-one span is an elementary normal subgroup when b > 2.
Construct its actual binary section V/C_V(O²(H)), retaining conjugation and
its exact coordinate kernel. The residual has no new fixed vectors on this
quotient: displacement of a fixed lift is a homomorphism into a two-group,
and O²(H) is two-perfect. The short-distance quadratic action of each
neighboring span passes to these same quotient coordinates.

These are the residual-fixed and quadratic premises used in DGS 9.3.
Faithfulness through H/O₂(H), fixed-space generation and natural recognition
are separate remaining obligations. The source local group S G_delta_star
is instantiated in `ResidualSource`; it is not replaced by the full stabilizer.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 6.0, p.118; 9.1(c) and 9.3, pp.141--142.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.NormalElementaryQuotient
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

private theorem residual_fixed_quotient (H : Type*) [Group H] [Finite H]
    (A : Subgroup H) [A.Normal] [IsElementaryAbelian 2 A] :
    fixedSpace (fixedQuotientAction A (pResidual 2 H)) (pResidual 2 H) = ⊥ := by
  apply bot_unique
  intro w hw
  obtain ⟨a, rfl⟩ := (fixedSpace (originalAction A) (pResidual 2 H)).mkQ_surjective w
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact fixed_of_pPerfect_central_kernel (originalAction A) (pResidual 2 H)
    (isPPerfect_pResidual 2) (fixedSpace (originalAction A) (pResidual 2 H)).mkQ
    (by rw [Submodule.ker_mkQ]) a hw

/-- Relative normality of the original neighborhood span in its local group. -/
theorem neighborhoodIn_normal (F : Bool → Subgroup G) [∀ i, Finite (F i)]
    (v : Vertex F) (H : Subgroup G) (hH : H ≤ stabilizer F v) :
    ((V F v 1).subgroupOf H).Normal :=
  normal_subgroupOf_of_le_normalizer (hH.trans (stabilizer_normalizes_V F v 1))

/-- The same neighborhood span is elementary in local subgroup coordinates. -/
theorem neighborhoodIn_elementary (F : Bool → Subgroup G) [∀ i, Finite (F i)]
    (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hS : ∀ v, ∃ T : Sylow 2 (U F v),
      (T : Subgroup (U F v)).map (U F v).subtype = Q F v)
    (v : Vertex F) (hb : 2 < b F) (H : Subgroup G) :
    IsElementaryAbelian 2 ((V F v 1).subgroupOf H) := by
  let := V_elementary F hgen hZ hS v (r := 1) (by simpa using hb)
  exact IsElementaryAbelian.comap_of_injective H.subtype H.subtype_injective (V F v 1)

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The actual section V/C_V(O²(H)), with its conjugation, zero residual fixed
space, and all short-distance quadratic actors. -/
theorem neighborhood_residual_section (h : LocallyRankOneTriple P B)
    (hS : ∀ v : Vertex (family P), ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v)
    (v : Vertex (family P)) (hb : 2 < b (family P))
    (H : Subgroup G) (hQH : Q (family P) v ≤ H) (hHP : H ≤ stabilizer (family P) v) :
    letI := finite_endpoints h
    let A := (V (family P) v 1).subgroupOf H
    letI := neighborhoodIn_normal (family P) v H hHP
    letI := neighborhoodIn_elementary (family P) h.generate
      (fun w => (source_Z_Q_U h w).1) hS v hb H
    Nonempty (BinaryConjugationSection H (V (family P) v 1)
      (V (family P) v 1 ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G))
      (fixedQuotientAction A (pResidual 2 H))) ∧
      fixedSpace (fixedQuotientAction A (pResidual 2 H)) (pResidual 2 H) = ⊥ ∧
      ∀ u : Vertex (family P), (graph (family P)).dist u v + 1 ≤ b (family P) →
        IsQuadratic (fixedQuotientAction A (pResidual 2 H)) ((V (family P) u 1).subgroupOf H) := by
  let := finite_endpoints h
  let : Finite H := Finite.of_injective (inclusion hHP) (inclusion_injective _)
  let A := (V (family P) v 1).subgroupOf H
  let := neighborhoodIn_normal (family P) v H hHP
  let := neighborhoodIn_elementary (family P) h.generate
    (fun w => (source_Z_Q_U h w).1) hS v hb H
  have hVH : V (family P) v 1 ≤ H :=
    (V_le_Q (family P) h.generate (fun w => (source_Z_Q_U h w).1) hS v (by omega)).trans hQH
  let e : V (family P) v 1 ≃* A := (subgroupOfEquivOfLe hVH).symm
  let π := (fixedQuotientProjection A (pResidual 2 H)).comp e.toMonoidHom
  have hk : π.ker = (centralizer ((pResidual 2 H).map H.subtype : Set G)).subgroupOf
      (V (family P) v 1) := by
    ext x
    change e x ∈ (fixedQuotientProjection A (pResidual 2 H)).ker ↔ _
    rw [fixedQuotientProjection_kernel]
    change (⟨(x : G), hVH x.property⟩ : H) ∈ centralizer (pResidual 2 H : Set H) ↔
      (x : G) ∈ centralizer ((pResidual 2 H).map H.subtype : Set G)
    constructor
    · intro hx y hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact congrArg Subtype.val (hx z hz)
    · intro hx y hy
      exact Subtype.ext (hx y (mem_map_of_mem H.subtype hy))
  let c : BinaryConjugationSection H (V (family P) v 1)
      (V (family P) v 1 ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G))
      (fixedQuotientAction A (pResidual 2 H)) := {
    section_le := hVH
    kernel_le := inf_le_left
    normalized := hHP.trans (stabilizer_normalizes_V (family P) v 1)
    coordinates := π
    onto := (fixedQuotientProjection_surjective A (pResidual 2 H)).comp e.surjective
    kernel_eq := by simpa only [inf_subgroupOf_left] using hk
    equivariant := by
      intro a x
      exact fixedQuotientProjection_equivariant A (pResidual 2 H) a (e x) }
  refine ⟨⟨c⟩, residual_fixed_quotient H A, ?_⟩
  intro u hd
  have hq := (V_mutual_quadratic (family P) h.generate
    (fun w => (source_Z_Q_U h w).1) hS u v hb hd).1
  have hqc : ⁅V (family P) u 1, ⁅V (family P) u 1, V (family P) v 1⁆⁆ ≤
      V (family P) v 1 ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G) := by
    rw [commutator_comm (V (family P) u 1), hq]
    exact bot_le
  have hquad := BinaryConjugationSection.isQuadratic_of_triple_commutator_le
    H (V (family P) v 1) _ (V (family P) u 1)
    (fixedQuotientAction A (pResidual 2 H)) (MonoidHom.id H) c hqc
  simpa only [Subgroup.map_id] using hquad

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
