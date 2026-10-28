module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedNeighborPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalNonsplitting

/-!
# Full-kernel comparison and contained endpoint saturation

Equal original neighboring mover orders make kernel containment equivalent
to equality of their quotient image orders. Missing the whole original
vertex kernel is therefore exactly the strict-image-growth branch; this
comparison does not assume that the critical image is a root.

For a contained large critical endpoint, the literal path puts its Z in
the original edge, and the marked parabolic intersection puts it in the
smaller mover J. If J has image order at most q², the large endpoint fills
that image. Pulling back through the original quotient map proves
J = Q join Z, retaining the entire kernel and all central attachments.
This does not assert that the endpoint contains a full field-sized root.

ContainedKernelPaths applies both conclusions to the same two residual
choices and actual backward critical path. Source: MS93 (5.5)(c),
(5.6)--(5.8), printed pp.915--920. Individual and exceptional paired-mover
generation and the terminal distance exclusions remain separate duties.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [CharP F 2] in
/-- Equal original mover orders give an exact test for retaining the whole
vertex kernel. Failure of containment strictly enlarges the quotient image. -/
theorem Input.replacement_neighbor_kernel_iff_image_eq
    {a t c : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)
    (Q d.radical a ≤ E ↔ (Q d.radical a).relIndex E = (Q d.radical a).relIndex J) ∧
      (¬ Q d.radical a ≤ E ↔ (Q d.radical a).relIndex J < (Q d.radical a).relIndex E) := by
  dsimp only
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  let Q₀ := (Q d.radical a).subgroupOf S
  let J₀ := J.subgroupOf S
  let E₀ := E.subgroupOf S
  let := finite_stabilizer d.radical a
  have hQS : Q d.radical a ≤ S := fun _ hx => hx.1
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hES : E ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hQJ : Q d.radical a ≤ J := by
    have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
      (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
      (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
      (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
        (h.replacement_two_group d) (h.replacement_core_le d)))
    rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh
  have hc : Nat.card J₀ = Nat.card E₀ := by
    rw [←card_map_of_injective S.subtype_injective (K := J₀),
      ←card_map_of_injective S.subtype_injective (K := E₀),
      map_subgroupOf_eq_of_le hJS,map_subgroupOf_eq_of_le hES]
    exact small_mover_neighbor_card_eq d.radical hat hct _
  have hjidx : Q₀.relIndex J₀ = (Q d.radical a).relIndex J := by
    have hh := relIndex_map_map_of_injective Q₀ J₀ S.subtype_injective
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hJS] at hh
    exact hh.symm
  have heidx : Q₀.relIndex E₀ = (Q d.radical a).relIndex E := by
    have hh := relIndex_map_map_of_injective Q₀ E₀ S.subtype_injective
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hES] at hh
    exact hh.symm
  have hle := Subgroup.SmallMover.relIndex_le_of_card_eq_of_le Q₀ J₀ E₀
    (comap_mono hQJ) hc
  have heq : Q d.radical a ≤ E ↔ (Q d.radical a).relIndex E = (Q d.radical a).relIndex J := by
    constructor
    · intro hQE
      have hreverse := Subgroup.SmallMover.relIndex_le_of_card_eq_of_le Q₀ E₀ J₀
        (comap_mono hQE) hc.symm
      exact heidx.symm.trans ((le_antisymm hreverse hle).trans hjidx)
    · intro hi
      have hQE := Subgroup.SmallMover.kernel_le_of_card_eq_of_relIndex_eq Q₀ J₀ E₀
        (comap_mono hQJ) hc (hjidx.trans (hi.symm.trans heidx.symm))
      have hm := map_mono (f := S.subtype) hQE
      rwa [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hES] at hm
  refine ⟨heq,?_⟩
  rw [heq]
  rw [hjidx,heidx] at hle
  dsimp only [J,E] at hle ⊢
  omega

/-- In the contained large-image branch, an original mover of image order
at most q² is exactly the critical endpoint together with the full vertex
kernel. This identifies the actual preimage, without assuming a full root
inside the endpoint image. -/
theorem Input.replacement_contained_minimal_endpoint_saturation
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (hcontained : ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
      (CentralRootGeometry.wing true).map unipotent.subtype)
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f)
    (hJsmall : (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2)) ≤ Nat.card F^2) :
    Q d.radical a ⊔ Z d.radical z = Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) ∧
      (Q d.radical a).relIndex (Z d.radical z) = Nat.card F^2 := by
  let S := stabilizer d.radical a
  let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
  let D := (P.comap f).map S.subtype
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let J₀ := J.subgroupOf S
  let A₀ := (Z d.radical z).subgroupOf S
  let := finite_stabilizer d.radical a
  have hsat := h.replacement_small_mover_parabolic_intersection d geometry hb path.start_color
    hat B hB f hf hindex hJplane
  change Q d.radical t ⊓ D = J at hsat
  have hTS : Q d.radical t ≤ S := fun _ hy => hy.2 a (adjacent_symm d.radical hat)
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hzT : Z d.radical z ≤ Q d.radical t := by
    rw [←hfirst]
    apply Z_le_Q_of_dist_lt d.radical z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.dist_end,geometry.distance_constant z path.end_color]
    change path.walk.length-1 < geometry.b d.radical
    rw [path.length_eq_b]
    omega
  have hzD : Z d.radical z ≤ D := by
    intro y hy
    exact ⟨⟨y,hzS hy⟩,hcontained (mem_map_of_mem f (show (⟨y,hzS hy⟩ : S) ∈ A₀ from hy)),rfl⟩
  have hzJ : Z d.radical z ≤ J := hsat ▸ le_inf hzT hzD
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hkJ : f.ker ≤ J₀ := by
    intro y hy
    change y.val ∈ J
    rw [←hsat]
    refine ⟨hQT (hfQ ▸ mem_map_of_mem S.subtype hy),mem_map_of_mem S.subtype ?_⟩
    change f y ∈ P
    rw [MonoidHom.mem_ker.mp hy]
    exact P.one_mem
  have imageIndex (C : Subgroup (FreeAmalgam d.radical)) (hCS : C ≤ S) :
      Nat.card ((C.subgroupOf S).map f) = (Q d.radical a).relIndex C := by
    rw [←relIndex_ker]
    have he := relIndex_map_map_of_injective f.ker (C.subgroupOf S) S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hCS] at he
    exact he.symm
  have hm : A₀.map f = J₀.map f := eq_of_le_of_card_ge (map_mono (comap_mono hzJ)) (by
    rw [imageIndex J hJS,imageIndex (Z d.radical z) hzS]
    exact hJsmall.trans hlarge)
  have hidx : (Q d.radical a).relIndex (Z d.radical z) = Nat.card F^2 := by
    have he := congrArg (fun C : Subgroup (Sp B.Carrier) => Nat.card C) hm
    rw [imageIndex (Z d.radical z) hzS,imageIndex J hJS] at he
    exact le_antisymm (he ▸ hJsmall) hlarge
  have he := congrArg (Subgroup.comap f) hm
  rw [comap_map_eq,comap_map_eq_self hkJ] at he
  have he' := congrArg (Subgroup.map S.subtype) he
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hzS,hfQ,map_subgroupOf_eq_of_le hJS] at he'
  exact ⟨by rwa [sup_comm],hidx⟩


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
