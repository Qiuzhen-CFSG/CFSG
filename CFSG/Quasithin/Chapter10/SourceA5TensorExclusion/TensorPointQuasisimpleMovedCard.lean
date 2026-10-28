module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointMovedOrbit
public import Theory.Representation.OrthogonalFourPlusMatrix.NonsingularPointMoved

/-!
# Order of the original tensor point's moved subgroup and its central image

The actual residual surjects onto the nonsingular matrix stabilizer, so its
commutator image is the entire perpendicular hyperplane. Faithful coordinates
therefore give order64 for the literal moved subgroup. Its projection modulo
the center of any containing subgroup has kernel contained in the residual's
fixed field line of orderfour, giving an image of order at least16.

Source: Aschbacher--Smith9.4.1, printed p.735, and the original A.3.12
local-section application. No Sylow-placement or quasisimplicity premise is
needed for these order and coordinate statements.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix PointOrbit
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

private theorem tensorPoint_displacement_mem_image (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (g : pointStabilizer (m.sectionData.coordinates v).toAdd) (M : Binary.V) :
    matrixAction g.val M - M ∈
      m.sectionData.imageSpace ⁅D.fullModule,m.tensorPointResidual v⁆ := by
  obtain ⟨r,hr⟩ := m.tensorPointResidualQuotient_surjective v hv g
  obtain ⟨a,ha⟩ := m.sectionData.onto (Multiplicative.ofAdd M)
  let rO : localOrbit T L := ⟨r,m.tensorPointResidual_le_orbit v r.property⟩
  have hq : m.quotient rO = g.val := congrArg Subtype.val hr
  let b : D.fullModule := ⟨(r : G)*a*(r : G)⁻¹,
    (mem_normalizer_iff.mp (m.sectionData.normalized rO.property) a).mp a.property⟩
  let c : D.fullModule := b*a⁻¹
  apply (m.sectionData.mem_imageSpace_iff _ _).mpr
  refine ⟨c,?_,?_⟩
  · rw [commutator_comm]
    exact commutator_mem_commutator r.property a.property
  · change (m.sectionData.coordinates (b*a⁻¹)).toAdd = _
    rw [map_mul,map_inv]
    change (m.sectionData.coordinates b).toAdd + -(m.sectionData.coordinates a).toAdd = _
    rw [←sub_eq_add_neg]
    have hb := m.sectionData.equivariant rO a
    change (m.sectionData.coordinates b).toAdd =
      matrixAction (m.quotient rO) (m.sectionData.coordinates a).toAdd at hb
    rw [hb,hq,ha]
    rfl

/-- The literal moved subgroup has the complete perpendicular hyperplane as its image. -/
theorem tensorPoint_moved_image_eq (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    m.sectionData.imageSpace ⁅D.fullModule,m.tensorPointResidual v⁆ =
      (pointHyperplane (m.sectionData.coordinates v).toAdd).restrictScalars (ZMod 2) := by
  apply le_antisymm (m.tensorPoint_moved_image_le v hv)
  exact pointHyperplane_le_of_displacements _ hv
    (m.sectionData.imageSpace ⁅D.fullModule,m.tensorPointResidual v⁆).toAddSubgroup
    (m.tensorPoint_displacement_mem_image v hv)

/-- Membership in the literal moved subgroup is precisely the coordinate hyperplane condition. -/
theorem tensorPoint_moved_coordinates_iff (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) (z : D.fullModule) :
    (z : G) ∈ ⁅D.fullModule,m.tensorPointResidual v⁆ ↔
      (m.sectionData.coordinates z).toAdd ∈
        pointHyperplane (m.sectionData.coordinates v).toAdd := by
  constructor
  · intro hz
    exact m.tensorPoint_moved_image_le v hv
      ((m.sectionData.mem_imageSpace_iff _ _).mpr ⟨z,hz,rfl⟩)
  · intro hz
    have hzi : (m.sectionData.coordinates z).toAdd ∈
        m.sectionData.imageSpace ⁅D.fullModule,m.tensorPointResidual v⁆ := by
      rw [m.tensorPoint_moved_image_eq v hv]
      exact hz
    obtain ⟨a,ha,he⟩ := (m.sectionData.mem_imageSpace_iff _ _).mp hzi
    exact (m.coordinates_injective (Multiplicative.toAdd.injective he) : a = z) ▸ ha

/-- The actual moved subgroup has order64, corresponding to dimension three over F₄. -/
theorem tensorPoint_moved_card (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    Nat.card (⁅D.fullModule,m.tensorPointResidual v⁆ : Subgroup G) = 64 := by
  let W := ⁅D.fullModule,m.tensorPointResidual v⁆
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    ((m.tensorPointResidual_le_orbit v).trans m.sectionData.normalized)
  have hcard : Nat.card (m.sectionData.imageSpace W) = Nat.card W := by
    change Nat.card ((W.subgroupOf D.fullModule).map m.sectionData.coordinates) = _
    rw [card_map_of_injective m.coordinates_injective,
      Nat.card_congr (subgroupOfEquivOfLe hWV).toEquiv]
  rw [←hcard]
  change Nat.card (m.sectionData.imageSpace ⁅D.fullModule,m.tensorPointResidual v⁆) = _
  rw [m.tensorPoint_moved_image_eq v hv]
  change Nat.card (pointHyperplane (m.sectionData.coordinates v).toAdd) = _
  rw [pointHyperplane_card _ hv]
  have hF : Nat.card Binary.F = 4 := by
    rw [Nat.card_eq_fintype_card]
    exact Representation.SL2FourNatural.card_field
  rw [hF]
  norm_num

/-- The literal moved subgroup retains at least16 elements modulo any containing center. -/
theorem tensorPoint_containing_quotient_moved_card_ge (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I) :
    16 ≤ Nat.card (((⁅D.fullModule,m.tensorPointResidual v⁆).subgroupOf I).map
      (QuotientGroup.mk' (center I))) := by
  let W := ⁅D.fullModule,m.tensorPointResidual v⁆
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    ((m.tensorPointResidual_le_orbit v).trans m.sectionData.normalized)
  have hWI : W ≤ I := (m.tensorPoint_moved_elementary_and_le v).2.trans hLI
  let q := QuotientGroup.mk' (center I)
  let f : W →* I ⧸ center I := q.comp (inclusion hWI)
  have hk : Nat.card f.ker ≤ 4 := by
    let j : f.ker → (D.fullModule ⊓ centralizer (m.tensorPointResidual v : Set G) : Subgroup G) :=
      fun x => ⟨x.val.val,hWV x.val.property,by
        intro r hr
        have hz : inclusion hWI x.val ∈ center I :=
          (QuotientGroup.eq_one_iff _).mp x.property
        exact congrArg (fun y : I => (y : G))
          (mem_center_iff.mp hz ⟨r,hLI hr⟩)⟩
    have hj : Function.Injective j := by
      intro x y h
      have hxy : (x.val.val : G) = y.val.val :=
        congrArg (fun z : (D.fullModule ⊓ centralizer (m.tensorPointResidual v : Set G) :
          Subgroup G) => (z : G)) h
      exact Subtype.ext (Subtype.ext hxy)
    exact (Nat.card_le_card_of_injective j hj).trans_eq
      (m.tensorPointResidual_fixed_card v hv)
  have hfr : f.range = (W.subgroupOf I).map q := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x,hWI x.property⟩,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  have htotal := f.ker.card_mul_index
  rw [index_ker,m.tensorPoint_moved_card v hv] at htotal
  change 16 ≤ Nat.card ((W.subgroupOf I).map q)
  rw [←hfr]
  nlinarith

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
