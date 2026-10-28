module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedPairedPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TerminalPaths

/-!
# Aligning the contained endpoint with the unique smaller mover

At an unequal neighboring pair, the maximum smaller mover is unique. In
any literal Sylow marking, a critical endpoint of image order at least q²
inside the plane radical forces that maximum into the same plane. If the
maximum were a nonstandard plane of order q², the endpoint image would
itself attain the maximum, contradicting uniqueness. The full endpoint
then lies in the original smaller-mover join by its exact parabolic
intersection, with every quotient kernel and central attachment retained.

On the actual first two-step neighbor at distance greater than four,
MS93 (5.9) supplies the required nonnormality. The application discharges
both that premise and the smaller-mover plane-containment premise in the
existing paired-path construction, retaining its literal quotient map,
residual choices, full edge kernels, two paths and generation alternative.

This is the contained large-image branch of MS93 (5.5)--(5.7), printed
pp.915--919, used in the terminal argument (5.10), pp.922--923. It now
retains both original-vertex mover equalities of (5.5)(b) at these same
selected edges in `replacement_contained_terminal_paired_paths_original_fixed`.
The remaining terminal normalizer comparisons, exclusions and the actual
minimum-replacement distance-two witness are still needed. No original-radical characteristic-control claim is made.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A large contained critical endpoint aligns the unique smaller mover in
its own original marking; no maximizing-parabolic or containment premise
for that mover is assumed. -/
theorem Input.replacement_contained_endpoint_aligns_mover
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (B : BinaryField) (hB : B.degree=n)
    (f : stabilizer d.radical a →* Sp B.Carrier)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype=Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (hcontained : ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
      (CentralRootGeometry.wing true).map unipotent.subtype) :
    (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f := by
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let A := (Z d.radical z).subgroupOf S
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let J₀ := J.subgroupOf S
  let := finite_stabilizer d.radical a
  have hcard : Nat.card B.Carrier=Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm _ hat)
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer _ _)
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hAS := path.endpoint_Z_le_start_stabilizer (by omega : 0<geometry.b d.radical)
  have hAT : Z d.radical z ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt _ z (geometry.exists_critical z path.end_color)
    rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,←hfirst,
      path.dist_end,path.length_eq_b]
    change geometry.b d.radical-1 < geometry.b d.radical
    omega
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hkT : f.ker ≤ T := by
    intro x hx
    exact hQT (hfQ ▸ mem_map_of_mem S.subtype hx)
  have hUK : U₀ ≤ centralizer (f.ker : Set S) := by
    intro u hu k hk
    apply Subtype.val_injective
    exact (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a path.start_color))
      (U_le_Z a hu) k.val (hfQ ▸ mem_map_of_mem S.subtype hk)
  have hi (D : Subgroup S) (hDT : D ≤ T) :
      (centralizer (D : Set S)).relIndex U₀ =
        movingIndex (Degree.Quotient.coordinates f unipotent.subtype D) := by
    rw [hindex,←binary_movingIndex]
    change 2 ^ fixedCodim (restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)) (D.map f) =
      2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
        (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype)
          ((D.map f).subgroupOf unipotent)
    rw [fixedCodim,fixedCodim,fixedSpace_comp_map,map_subgroupOf_eq_of_le ((map_mono hDT).trans hTf)]
  have hfamily := h.replacement_unequal_unique_maximal d geometry hb path.start_color hat hct hne
  have hJmax : J₀ ∈ Subgroup.SmallMover.Maximal U₀ f.ker T (Nat.card B.Carrier^2) := by
    apply (Subgroup.SmallMover.maximal_map_iff S.subtype S.subtype_injective _ _ _ _ _).mp
    rw [map_subgroupOf_eq_of_le hUS,hfQ,map_subgroupOf_eq_of_le hTS,
      map_subgroupOf_eq_of_le hJS,hcard]
    exact hfamily.symm ▸ Set.mem_singleton J
  let T₁ := Degree.Quotient.coordinates f unipotent.subtype T
  let J₁ := Degree.Quotient.coordinates f unipotent.subtype J₀
  let A₁ := Degree.Quotient.coordinates f unipotent.subtype A
  have hmax : J₁ ∈ Degree.Maximal T₁ := Degree.Quotient.maximal_coordinates U₀ T f
    unipotent.subtype Subtype.val_injective hkT hUK
      (by simpa only [range_subtype] using hTf) hi hJmax
  have hAj : A₁ ≤ T₁ := comap_mono (map_mono (comap_mono hAT))
  have hAw : A₁ ≤ CentralRootGeometry.wing true := by
    change (A.map f).comap unipotent.subtype ≤ _
    exact (comap_mono hcontained).trans_eq (comap_map_eq_self_of_injective unipotent.subtype_injective _)
  have hAm : A₁.map unipotent.subtype=A.map f :=
    map_subgroupOf_eq_of_le ((map_mono (comap_mono hAT)).trans hTf)
  have hAc : Nat.card B.Carrier^2 ≤ Nat.card A₁ := by
    rw [←card_map_of_injective unipotent.subtype_injective,hAm,←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker A S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hAS] at hh
    rw [←hh,hcard]
    exact hlarge
  have hJw : J₁ ≤ CentralRootGeometry.wing true := by
    rcases Degree.small_classification_nonstandard J₁ hmax.2.1 with hw | ⟨l,he⟩
    · exact hw
    have hAmax : A₁ ∈ Degree.Maximal T₁ := by
      refine ⟨hAj,Degree.small_of_le_wing_of_large A₁ hAw hAc,?_⟩
      intro D hDT hD
      have hh := hmax.2.2 D hDT hD
      rw [he,card_finitePlane] at hh
      exact hh.trans hAc
    obtain ⟨E,hE⟩ := (Degree.Quotient.maximal_coordinates_bijective U₀ T f
      unipotent.subtype Subtype.val_injective hkT hUK
        (by simpa only [range_subtype] using hTf) hi).surjective ⟨A₁,hAmax⟩
    have hEm := (Subgroup.SmallMover.maximal_map_iff S.subtype S.subtype_injective
      U₀ f.ker T E.val (Nat.card B.Carrier^2)).mpr E.property
    rw [map_subgroupOf_eq_of_le hUS,hfQ,map_subgroupOf_eq_of_le hTS] at hEm
    have hEm' : E.val.map S.subtype ∈ Subgroup.SmallMover.Maximal (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2) := by
      simpa only [hcard] using hEm
    rw [hfamily] at hEm'
    have heJ : E.val=J₀ := by
      apply map_injective S.subtype_injective
      rw [map_subgroupOf_eq_of_le hJS]
      exact Set.mem_singleton_iff.mp hEm'
    have hcoord := congrArg Subtype.val hE
    change Degree.Quotient.coordinates f unipotent.subtype E.val=A₁ at hcoord
    rw [heJ] at hcoord
    change J₁=A₁ at hcoord
    rw [hcoord]
    exact hAw
  apply map_le_iff_le_comap.mp
  have hJm : J₁.map unipotent.subtype=J₀.map f :=
    map_subgroupOf_eq_of_le ((map_mono (comap_mono (Subgroup.SmallMover.join_le _ _ _ _))).trans hTf)
  rw [←hJm]
  exact map_mono hJw


/-- The entire contained critical endpoint belongs to the smaller mover,
through the full original quotient kernel. -/
theorem Input.replacement_contained_endpoint_le_small_mover
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (B : BinaryField) (hB : B.degree=n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype=Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (hcontained : ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
      (CentralRootGeometry.wing true).map unipotent.subtype) :
    Z d.radical z ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) := by
  have hJplane := h.replacement_contained_endpoint_aligns_mover d path hb hat hfirst hct hne
    B hB f hfQ hTf hindex hlarge hcontained
  rw [←h.replacement_small_mover_parabolic_intersection d geometry hb path.start_color hat
    B hB f hf hindex hJplane]
  apply le_inf
  · apply Z_le_Q_of_dist_lt _ z (geometry.exists_critical z path.end_color)
    rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,←hfirst,
      path.dist_end,path.length_eq_b]
    change geometry.b d.radical-1 < geometry.b d.radical
    omega
  · have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0<geometry.b d.radical)
    intro y hy
    refine ⟨⟨y,hzS hy⟩,?_,rfl⟩
    exact hcontained (mem_map_of_mem f (show
      (⟨y,hzS hy⟩ : stabilizer d.radical a) ∈ (Z d.radical z).subgroupOf
        (stabilizer d.radical a) from hy))

/-- At the literal first two-step neighbor, the contained branch supplies
both paired backward paths without separate nonnormality or mover-plane
premises. The original marking and complete generation alternative remain. -/
theorem Input.replacement_contained_terminal_paired_paths_original_fixed_normalized
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hne : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 2))
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z)) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        unipotent ≤ normalizer
          (((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f : Set (Sp B.Carrier)) ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
        (((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
            (CentralRootGeometry.wing true).map unipotent.subtype →
          (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
            (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
              ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f ∧
          Z d.radical z ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
            (Q d.radical t) (Nat.card F^2) ∧
          ∃ u v : stabilizer d.radical a,
            u.val∈Ltilde d.radical a ∧ v.val∈Ltilde d.radical a ∧
            f u∈planeLocal ∧ f u∉pointParabolic ∧
            let f' := (MulAut.conj (f u)).toMonoidHom.comp f
            let A := (Z d.radical z).subgroupOf (stabilizer d.radical a)
            let t₁ := act d.radical v.val⁻¹ t
            let c₁ := act d.radical v.val⁻¹ (path.walk.getVert 2)
            let E := (Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
              (Q d.radical t₁) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)
            Function.Surjective f' ∧ f'.ker=f.ker ∧
            Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
            A.map f' ≤ (CentralRootGeometry.wing true).map unipotent.subtype ∧
            ∃ x : stabilizer d.radical a, x.val∈Ltilde d.radical a ∧
              f' x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
              f x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
              let t₂ := act d.radical x.val⁻¹ t₁
              let c₂ := act d.radical x.val⁻¹ c₁
              Adjacent d.radical a t₂ ∧ Adjacent d.radical c₂ t₂ ∧
              Q d.radical t₁ ⊔ Z d.radical z = stabilizer d.radical a ∧
              Q d.radical t₂ ⊔ Z d.radical z = stabilizer d.radical a ∧
              (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                (U d.radical c₁) =
                (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                  (U d.radical (path.walk.getVert 2)) ∧
              (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                (U d.radical c₂) =
                (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                  (U d.radical (path.walk.getVert 2)) ∧
              (¬ Z d.radical z ≤ normalizer
                ((Z d.radical c₁ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
              (¬ Z d.radical z ≤ normalizer
                ((Z d.radical c₂ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
              (∃ back : CriticalPath d.radical geometry c₁ (path.walk.getVert (path.walk.length-2)),
                back.walk.getVert 1 = t₁ ∧
                ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
              (∃ back : CriticalPath d.radical geometry c₂ (path.walk.getVert (path.walk.length-2)),
                back.walk.getVert 1 = t₂ ∧
                ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
              (Z d.radical t ⊓ centralizer (E.map (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer ((E.map (MulAut.conj x).toMonoidHom).map
                  (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₁) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₂) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
            ((pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E ∧
                pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E.map (MulAut.conj x).toMonoidHom) ∨
              (Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 2))
                  (Q d.radical t) (Nat.card F^2) ∧
                Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
                  (Q d.radical t₁) (Nat.card F^2) ∧
                (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t) (Nat.card F^2) ⊓ Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 2))
                  (Q d.radical t) (Nat.card F^2)) ≤ Nat.card F^2 ∧
                (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₁) (Nat.card F^2) ⊓ Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
                  (Q d.radical t₁) (Nat.card F^2)) ≤ Nat.card F^2 ∧
                X d.radical a ≠ U d.radical a ⊔ (X d.radical a ⊓
                  centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
                (A ⊔ E) ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤))) := by
  have hct : Adjacent d.radical (path.walk.getVert 2) t := by
    rw [←hfirst]
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 1 < path.walk.length)))
  have hnormal := h.replacement_path_neighbor_join_not_normal d path hb
  obtain ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,hall⟩ :=
    h.replacement_contained_neighbor_paired_paths_original_fixed_normalized d path hb.le hat hct hne hnormal hlarge
  refine ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,?_⟩
  intro hcontained
  have hJplane := h.replacement_contained_endpoint_aligns_mover d path hb.le hat hfirst hct hne
    B hB f hfQ hTf hindex hlarge hcontained
  exact ⟨hJplane,h.replacement_contained_endpoint_le_small_mover d path hb.le hat hfirst hct hne
    B hB f hf hfQ hTf hindex hlarge hcontained,hall hcontained hJplane⟩

/-- The original interface, with its quotient marking and all conclusions preserved. -/
theorem Input.replacement_contained_terminal_paired_paths_original_fixed
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hne : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 2))
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z)) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
        (((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
            (CentralRootGeometry.wing true).map unipotent.subtype →
          (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
            (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
              ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f ∧
          Z d.radical z ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
            (Q d.radical t) (Nat.card F^2) ∧
          ∃ u v : stabilizer d.radical a,
            u.val∈Ltilde d.radical a ∧ v.val∈Ltilde d.radical a ∧
            f u∈planeLocal ∧ f u∉pointParabolic ∧
            let f' := (MulAut.conj (f u)).toMonoidHom.comp f
            let A := (Z d.radical z).subgroupOf (stabilizer d.radical a)
            let t₁ := act d.radical v.val⁻¹ t
            let c₁ := act d.radical v.val⁻¹ (path.walk.getVert 2)
            let E := (Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
              (Q d.radical t₁) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)
            Function.Surjective f' ∧ f'.ker=f.ker ∧
            Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
            A.map f' ≤ (CentralRootGeometry.wing true).map unipotent.subtype ∧
            ∃ x : stabilizer d.radical a, x.val∈Ltilde d.radical a ∧
              f' x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
              f x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
              let t₂ := act d.radical x.val⁻¹ t₁
              let c₂ := act d.radical x.val⁻¹ c₁
              Adjacent d.radical a t₂ ∧ Adjacent d.radical c₂ t₂ ∧
              Q d.radical t₁ ⊔ Z d.radical z = stabilizer d.radical a ∧
              Q d.radical t₂ ⊔ Z d.radical z = stabilizer d.radical a ∧
              (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                (U d.radical c₁) =
                (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                  (U d.radical (path.walk.getVert 2)) ∧
              (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                (U d.radical c₂) =
                (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                  (U d.radical (path.walk.getVert 2)) ∧
              (¬ Z d.radical z ≤ normalizer
                ((Z d.radical c₁ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
              (¬ Z d.radical z ≤ normalizer
                ((Z d.radical c₂ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
              (∃ back : CriticalPath d.radical geometry c₁ (path.walk.getVert (path.walk.length-2)),
                back.walk.getVert 1 = t₁ ∧
                ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
              (∃ back : CriticalPath d.radical geometry c₂ (path.walk.getVert (path.walk.length-2)),
                back.walk.getVert 1 = t₂ ∧
                ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
              (Z d.radical t ⊓ centralizer (E.map (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer ((E.map (MulAut.conj x).toMonoidHom).map
                  (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₁) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₂) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
            ((pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E ∧
                pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E.map (MulAut.conj x).toMonoidHom) ∨
              (Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 2))
                  (Q d.radical t) (Nat.card F^2) ∧
                Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
                  (Q d.radical t₁) (Nat.card F^2) ∧
                (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t) (Nat.card F^2) ⊓ Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 2))
                  (Q d.radical t) (Nat.card F^2)) ≤ Nat.card F^2 ∧
                (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₁) (Nat.card F^2) ⊓ Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
                  (Q d.radical t₁) (Nat.card F^2)) ≤ Nat.card F^2 ∧
                X d.radical a ≠ U d.radical a ⊔ (X d.radical a ⊓
                  centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
                (A ⊔ E) ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤))) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,_hTn,hindex,hall⟩ :=
    h.replacement_contained_terminal_paired_paths_original_fixed_normalized d path hb hat hfirst hne hlarge
  exact ⟨B,hB,f,hf,hfQ,hTf,hindex,hall⟩

/-- The original terminal paired-path interface with its public statement preserved. -/
theorem Input.replacement_contained_terminal_paired_paths
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hne : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 2))
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z)) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
        (((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
            (CentralRootGeometry.wing true).map unipotent.subtype →
          (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
            (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
              ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f ∧
          Z d.radical z ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
            (Q d.radical t) (Nat.card F^2) ∧
          ∃ u v : stabilizer d.radical a,
            u.val∈Ltilde d.radical a ∧ v.val∈Ltilde d.radical a ∧
            f u∈planeLocal ∧ f u∉pointParabolic ∧
            let f' := (MulAut.conj (f u)).toMonoidHom.comp f
            let A := (Z d.radical z).subgroupOf (stabilizer d.radical a)
            let t₁ := act d.radical v.val⁻¹ t
            let c₁ := act d.radical v.val⁻¹ (path.walk.getVert 2)
            let E := (Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
              (Q d.radical t₁) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)
            Function.Surjective f' ∧ f'.ker=f.ker ∧
            Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
            A.map f' ≤ (CentralRootGeometry.wing true).map unipotent.subtype ∧
            ∃ x : stabilizer d.radical a, x.val∈Ltilde d.radical a ∧
              f' x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
              f x∈(planeParabolic (F := B.Carrier)).pCoreIn 2 ∧
              let t₂ := act d.radical x.val⁻¹ t₁
              let c₂ := act d.radical x.val⁻¹ c₁
              Adjacent d.radical a t₂ ∧ Adjacent d.radical c₂ t₂ ∧
              Q d.radical t₁ ⊔ Z d.radical z = stabilizer d.radical a ∧
              Q d.radical t₂ ⊔ Z d.radical z = stabilizer d.radical a ∧
              (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                (U d.radical c₁) =
                (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                  (U d.radical (path.walk.getVert 2)) ∧
              (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                (U d.radical c₂) =
                (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex
                  (U d.radical (path.walk.getVert 2)) ∧
              (¬ Z d.radical z ≤ normalizer
                ((Z d.radical c₁ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
              (¬ Z d.radical z ≤ normalizer
                ((Z d.radical c₂ ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
              (∃ back : CriticalPath d.radical geometry c₁ (path.walk.getVert (path.walk.length-2)),
                back.walk.getVert 1 = t₁ ∧
                ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
              (∃ back : CriticalPath d.radical geometry c₂ (path.walk.getVert (path.walk.length-2)),
                back.walk.getVert 1 = t₂ ∧
                ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
              (Z d.radical t ⊓ centralizer (E.map (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
              (Z d.radical t ⊓ centralizer ((E.map (MulAut.conj x).toMonoidHom).map
                  (stabilizer d.radical a).subtype : Set (FreeAmalgam d.radical)) =
                Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
            ((pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E ∧
                pResidual 2 (stabilizer d.radical a) ≤ A ⊔ E.map (MulAut.conj x).toMonoidHom) ∨
              (Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 2))
                  (Q d.radical t) (Nat.card F^2) ∧
                Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
                  (Q d.radical t₁) (Nat.card F^2) ∧
                (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t) (Nat.card F^2) ⊓ Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 2))
                  (Q d.radical t) (Nat.card F^2)) ≤ Nat.card F^2 ∧
                (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
                  (Q d.radical t₁) (Nat.card F^2) ⊓ Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
                  (Q d.radical t₁) (Nat.card F^2)) ≤ Nat.card F^2 ∧
                X d.radical a ≠ U d.radical a ⊔ (X d.radical a ⊓
                  centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
                (A ⊔ E) ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤))) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,hall⟩ :=
    h.replacement_contained_terminal_paired_paths_original_fixed d path hb hat hfirst hne hlarge
  refine ⟨B,hB,f,hf,hfQ,hTf,hindex,?_⟩
  intro hcontained
  obtain ⟨hJplane,hzJ,u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hAP,x,hx,hxc,hxc₀,hat₂,hct₂,hwhole₁,hwhole₂,hi₁,hi₂,hn₁,hn₂,hback₁,hback₂,hfix₁,hfix₂,_,_,hD⟩ := hall hcontained
  exact ⟨hJplane,hzJ,u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hAP,x,hx,hxc,hxc₀,hat₂,hct₂,hwhole₁,hwhole₂,hi₁,hi₂,hn₁,hn₂,hback₁,hback₂,hfix₁,hfix₂,hD⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
