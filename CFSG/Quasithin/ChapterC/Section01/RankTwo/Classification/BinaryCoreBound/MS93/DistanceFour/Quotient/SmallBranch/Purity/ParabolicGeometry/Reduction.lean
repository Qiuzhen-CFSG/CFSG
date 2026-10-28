module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.Criteria
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.Square
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Marked

/-!
# Parabolic bounds from actual subgroup calculations

The two-core and the source-ordered residual are transported through the
original quotient. An index-four commutator preimage gives codimension at
most two on core/U. A residual-fixed element outside U has a nonzero
coordinate under the original marking: the proved square obstruction
removes the full fixed kernel of the coordinate map.

The triple commutator also puts the edge-radius commutator in Z. Constructing
the nonzero residual-fixed element and the selected two-core index remains
geometric work; neither is assumed to follow from the generic FF property.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.9)--(4.6.11), pp.908--909.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)

/-- The selected source-ordered rank-one residual lies in the local component. -/
theorem flagResidual_le_component (i : Bool) :
    Flags.RankOne.flagResidual source i ≤ Ltilde R (alpha R) := by
  rw [← Flags.RankOne.flagResidual_sup source]
  cases i
  · exact le_sup_left
  · exact le_sup_right

include common radius in
/-- The supplied triple bound centralizes the actual edge-radius layer modulo Z. -/
theorem edge_commutator_le_Z_of_flag (i : Bool)
    (htriple : ⁅⁅V R (beta R), Flags.RankOne.flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    ⁅V R (beta R), Flags.RankOne.flagResidual source i⁆ ≤ Z R (alpha R) := by
  exact commutator_le_Z_of_triple source geometry common radius _ _
    (Flags.RankOne.edgeRadius_le_radius (alpha R) (beta R) rfl (base_adjacent R))
    (flagResidual_le_component source i) htriple

/-- The original projection preserves the ordered residual of the selected parabolic. -/
theorem parabolicResidual_projection (i : Bool) :
    (rankOne (parabolic source.projection source.flag i)).map source.projection =
      rankOne (modelParabolic source.flag i) := by
  have hk : IsPGroup 2 source.projection.ker := by
    rw [source.projection_kernel]
    exact pCore_isPGroup
  have hid : IsPGroup 2 (MonoidHom.id SL).ker := by
    rw [MonoidHom.ker_id]
    exact IsPGroup.of_subsingleton 2 _
  have hm : parabolic (MonoidHom.id SL) source.flag i = modelParabolic source.flag i :=
    comap_id _
  have hp : (parabolic source.projection source.flag i).map source.projection =
      modelParabolic source.flag i := by
    exact map_comap_eq_self_of_surjective source.projection_surjective _
  rw [rankOne_parabolic_eq source.projection source.projection_surjective hk,
    ← hm, rankOne_parabolic_eq (MonoidHom.id SL) Function.surjective_id hid, hm,
    map_embedded_pResidual, hp]

/-- The two-group kernel identifies the image of the intrinsic parabolic two-core. -/
theorem parabolicCore_projection (i : Bool) :
    (((pCore 2 (parabolic source.projection source.flag i)).map
      (parabolic source.projection source.flag i).subtype).map source.projection) =
      (pCore 2 (modelParabolic source.flag i)).map (modelParabolic source.flag i).subtype := by
  unfold parabolic
  let P := modelParabolic source.flag i
  let f := source.projection.subgroupComap P
  have hf : Function.Surjective f :=
    source.projection.subgroupComap_surjective_of_surjective P source.projection_surjective
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = source.projection.ker.comap
        ((modelParabolic source.flag i).comap source.projection).subtype := by
      ext x
      simp only [MonoidHom.mem_ker, Subtype.ext_iff]
      rfl
    rw [he, source.projection_kernel]
    exact pCore_isPGroup.comap_subtype
  have he : (pCore 2 (P.comap source.projection)).map f = pCore 2 P := by
    rw [← f.comap_pCore_of_ker_isPGroup hf hk, map_comap_eq_self_of_surjective hf]
  calc
    _ = ((pCore 2 (P.comap source.projection)).map f).map P.subtype := by
      rw [map_map, map_map]
      rfl
    _ = _ := by rw [he]

variable (d : CoreModule source)

include common in
/-- A genuine commutator-preimage index bounds the fixed codimension of its actor image. -/
theorem CoreModule.fixedCodim_le_two_of_preimage_index
    (E : Subgroup (FreeAmalgam R))
    (hindex : (commutatorPreimage (core R (alpha R)) E (U R (alpha R))).relIndex
      (core R (alpha R)) ≤ 4) :
    fixedCodim d.representation ((E.comap (embedM R)).map source.projection) ≤ 2 := by
  let C := core R (alpha R)
  let A := (E.comap (embedM R)).map source.projection
  let K := commutatorPreimage C E (U R (alpha R))
  let W := fixedSpace d.representation A
  let H : Subgroup (Multiplicative d.Space) := W.toAddSubgroup.toSubgroup
  let F : Subgroup C := H.comap d.projection
  have hC : C ≤ stabilizer R (alpha R) := (core_le_Q source).trans (fun _ hx => hx.1)
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite C := Finite.of_injective (Subgroup.inclusion hC) (Subgroup.inclusion_injective hC)
  have hKU : ⁅K, E⁆ ≤ U R (alpha R) :=
    commutator_commutatorPreimage_le _ _ _
      (hC.trans (by rw [alpha, stabilizer_m_base]; exact common.natural.normalized))
  have hKF : K.subgroupOf C ≤ F := by
    intro x hx
    change ∀ g : A, d.representation g.val (d.projection x).toAdd = (d.projection x).toAdd
    intro g
    obtain ⟨m, hm, hmg⟩ := g.property
    change embedM R m ∈ E at hm
    rw [← hmg]
    let y := coreAction (R := R) m x
    have hz : y * x⁻¹ ∈ d.projection.ker := by
      rw [d.kernel]
      change ⁅embedM R m, (x : FreeAmalgam R)⁆ ∈ U R (alpha R)
      rw [commutator_comm] at hKU
      exact hKU (commutator_mem_commutator hm hx)
    have hq : d.projection y = d.projection x := by
      change d.projection (y * x⁻¹) = 1 at hz
      rwa [map_mul, map_inv, mul_inv_eq_one] at hz
    rw [← d.action m x y rfl, hq]
  have hind : F.index ≤ 4 := (Subgroup.index_antitone hKF).trans hindex
  have hpow : 2 ^ fixedCodim d.representation A ≤ 4 := by
    rw [Subgroup.index_comap_of_surjective _ d.onto, AddSubgroup.index_toSubgroup] at hind
    change Nat.card (d.Space ⧸ W) ≤ 4 at hind
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hind
    exact hind
  exact (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hpow

include common in
/-- The edge-kernel index gives the codimension bound for the same selected model parabolic. -/
theorem codimension_of_flag_index (i : Bool)
    (hkernel : Flags.RankOne.flagKernel source i = Q R (beta R))
    (hindex : (commutatorPreimage (core R (alpha R)) (Q R (beta R))
      (U R (alpha R))).relIndex (core R (alpha R)) ≤ 4) :
    fixedCodim d.representation
      ((pCore 2 (modelParabolic source.flag i)).map (modelParabolic source.flag i).subtype) ≤ 2 := by
  have h := CoreModule.fixedCodim_le_two_of_preimage_index source geometry common d _ hindex
  rw [← hkernel, Flags.RankOne.flagKernel,
    comap_map_eq_self_of_injective (embedM_injective R), parabolicCore_projection] at h
  exact h

include common radius in
/-- A nonzero residual-fixed core/U element has a nonzero fixed coordinate with the supplied marking. -/
theorem fixed_vector_of_flag_preimage (m : ℕ)
    (q : AbelianCore.QuotientRecognition.ModuleQuotient d.representation m) (i : Bool)
    (hne : ¬ commutatorPreimage (core R (alpha R)) (Flags.RankOne.flagResidual source i)
      (U R (alpha R)) ≤ U R (alpha R)) :
    ∃ w : Fin 3 → ZMod 2, w ≠ 0 ∧
      ∀ k ∈ rankOne (modelParabolic source.flag i), (q.marking k).val.mulVec w = w := by
  classical
  obtain ⟨x, hx, hxu⟩ := SetLike.not_le_iff_exists.mp hne
  let z : core R (alpha R) := ⟨x, commutatorPreimage_le _ _ _ hx⟩
  have hz : (d.projection z).toAdd ≠ 0 := by
    intro hh
    apply hxu
    have hk : z ∈ d.projection.ker := by
      change d.projection z = 1
      exact Multiplicative.toAdd.injective hh
    rwa [d.kernel] at hk
  have hcoord : q.projection (d.projection z).toAdd ≠ 0 := by
    intro hh
    apply hz
    have hk : (d.projection z).toAdd ∈ q.projection.ker := hh
    rw [q.kernel, no_fixed source geometry common radius d m q] at hk
    exact hk
  obtain ⟨j, hj⟩ : ∃ j : Fin m, q.projection (d.projection z).toAdd j ≠ 0 := by
    by_contra! hh
    exact hcoord (funext hh)
  refine ⟨q.projection (d.projection z).toAdd j, hj, ?_⟩
  intro k hk
  rw [← parabolicResidual_projection source i] at hk
  obtain ⟨l, hl, rfl⟩ := hk
  have hl' : embedM R l ∈ Flags.RankOne.flagResidual source i := mem_map_of_mem _ hl
  have hC : core R (alpha R) ≤ stabilizer R (alpha R) :=
    (core_le_Q source).trans (fun _ hx => hx.1)
  have hc := commutator_commutatorPreimage_le (core R (alpha R))
    (Flags.RankOne.flagResidual source i) (U R (alpha R))
    (hC.trans (by rw [alpha, stabilizer_m_base]; exact common.natural.normalized))
  rw [commutator_comm] at hc
  let y := coreAction (R := R) l z
  have hker : y * z⁻¹ ∈ d.projection.ker := by
    rw [d.kernel]
    change ⁅embedM R l, x⁆ ∈ U R (alpha R)
    exact hc (commutator_mem_commutator hl' hx)
  have he : d.projection y = d.projection z := by
    change d.projection (y * z⁻¹) = 1 at hker
    rwa [map_mul, map_inv, mul_inv_eq_one] at hker
  have hfix : d.representation (source.projection l) (d.projection z).toAdd =
      (d.projection z).toAdd := by
    rw [← d.action l z y rfl, he]
  change specialLinearNatural 3 (q.marking (source.projection l))
    (q.projection (d.projection z).toAdd j) = _
  rw [← q.equivariant, hfix]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
