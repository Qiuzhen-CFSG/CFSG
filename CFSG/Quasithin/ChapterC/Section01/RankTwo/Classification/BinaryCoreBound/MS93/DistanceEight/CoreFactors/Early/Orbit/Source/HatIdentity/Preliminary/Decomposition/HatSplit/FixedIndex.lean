module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition.Bounds
public import Theory.GroupTheory.TwoLayerFixedIndex
public import Theory.Representation.BinaryOffender.FixedSubgroupIndex
/-!
# The fixed index on the actual first-hat quotient

The head action is the literal action on hatV/H. Its fixed preimage is the
ordinary two-residual centralizer: commutator idempotence removes the central
H-kernel. Thus the source fixed-codimension estimate gives index at most 64
for the fixed subgroup inside the hat, without any assertion about the full
radius fixed subgroup.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), printed p.897.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition
open Escape.Initial.Natural.Splitting Representation Representation.BinaryOffender
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The fixed subgroup on the literal hat/H quotient pulls back to the
ordinary residual centralizer: the central H-kernel disappears by two-perfectness. -/
theorem fixed_preimage_eq
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t : Vertex R} (w : Window geometry a b t) :
    let := quotient_elementary earlier w
    let σ := Offenders.linearize (headAction common earlier w)
    (AddSubgroup.toSubgroup' (fixedSpace σ ⊤).toAddSubgroup).comap
      (quotientProjection b a) =
    (centralizer (pResidual 2 (stabilizer R b) : Set (stabilizer R b))).subgroupOf
      (localHat b a) := by
  let := quotient_elementary earlier w
  let G := stabilizer R b
  let A := localHat b a
  let N := localH b
  let K := pResidual 2 G
  let := finite_stabilizer R b
  let : IsElementaryAbelian 2 (hatV R b a) :=
    PathCentrality.localZSpan_elementary R w.color_b
      (by rw [SimpleGraph.dist_comm,w.moving.1]) (by rw [earlier.distance]; decide)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf (hat_le_local earlier w)
  have hN : N ≤ centralizer (K : Set G) := by
    intro x hx l hl
    apply Subtype.ext
    exact (H_le_fixedFactor_of_central w.color_b common.large_distance
      (earlier.centrality b w.color_b) hx).2 l (mem_map_of_mem G.subtype hl)
  have hC := centralizerModulo_eq_inf_of_pPerfect_central_kernel 2 A K N
    (isPPerfect_pResidual 2) (IsElementaryAbelian.isPGroup 2 A) hN
  have hgen : K ⊔ (Q R b).subgroupOf G = ⊤ := by
    apply Subgroup.map_injective (f := G.subtype) G.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le
      (show Q R b ≤ G from fun _ hx => hx.1)]
    change Ltilde R b ⊔ Q R b = (⊤ : Subgroup G).map G.subtype
    rw [source.local_generation b w.color_b, ← MonoidHom.range_eq_map,range_subtype]
  ext x
  change (∀ g : (⊤ : Subgroup SL),
      headAction common earlier w g.val (quotientProjection b a x) =
        quotientProjection b a x) ↔ (x:G) ∈ centralizer (K : Set G)
  constructor
  · intro hx
    have hc : (x:G) ∈ centralizerModulo A K N := by
      apply mem_centralizerModulo_iff.mpr
      refine ⟨x.property,fun l hl => ?_⟩
      have he := hx ⟨localProjection source b w.color_b l,mem_top _⟩
      rw [headAction_apply] at he
      have hh := QuotientGroup.eq_iff_div_mem.mp he
      change l*(x:G)*l⁻¹/(x:G) ∈ N at hh
      simpa only [commutatorElement_def, div_eq_mul_inv] using hh
    rw [hC] at hc
    exact hc.2
  · intro hx g
    have hmap : K.map (localProjection source b w.color_b) = ⊤ := by
      have hh := congrArg (Subgroup.map (localProjection source b w.color_b)) hgen
      have hk : (Q R b).subgroupOf G = (localProjection source b w.color_b).ker :=
        (localProjection_kernel source b w.color_b).symm
      rw [Subgroup.map_sup, hk, map_ker_self, sup_bot_eq,
        map_top_of_surjective _ (localProjection_surjective source b w.color_b)] at hh
      exact hh
    obtain ⟨l,hl,he⟩ := (show g.val ∈ K.map (localProjection source b w.color_b) from
      hmap.symm ▸ mem_top _)
    rw [← he,headAction_apply]
    congr 1
    apply Subtype.ext
    change l*(x:G)*l⁻¹ = (x:G)
    rw [hx l hl,mul_inv_cancel_right]

/-- The actual source codimension bound bounds the fixed index of the hat,
after the central H-kernel has been removed. -/
theorem hat_fixed_index_le64
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t : Vertex R} (w : Window geometry a b t)
    (bounds : ActionBounds common earlier w) :
    (centralizer (pResidual 2 (stabilizer R b) : Set (stabilizer R b))).relIndex
      (localHat b a) ≤ 64 := by
  let := quotient_elementary earlier w
  let σ := Offenders.linearize (headAction common earlier w)
  let F := AddSubgroup.toSubgroup' (fixedSpace σ ⊤).toAddSubgroup
  have hi : F.index =
      (centralizer (pResidual 2 (stabilizer R b) : Set (stabilizer R b))).relIndex
        (localHat b a) := by
    have hh := relIndex_comap F (quotientProjection b a) (⊤ : Subgroup (localHat b a))
    rw [fixed_preimage_eq common earlier w,relIndex_top_right,
      map_top_of_surjective (quotientProjection b a) (QuotientGroup.mk'_surjective _),relIndex_top_right] at hh
    exact hh.symm
  rw [← hi,fixed_subgroup_index σ]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) bounds.2)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition
