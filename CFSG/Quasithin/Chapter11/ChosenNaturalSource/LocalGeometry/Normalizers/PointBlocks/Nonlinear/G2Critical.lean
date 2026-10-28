module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.G2Actions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.G2Covers

/-!
# The critical moving images for every nonbinary exceptional degree

Reciprocal fixed-space bounds identify the critical images as offenders.
Both have rank 3n, and the same index bound holds already on their moving
subgroups. Thus all three root parameters occur on those moving subgroups.
Applying the transported cover-kernel criterion in both directions gives
one common embedded kernel in their original group commutator.

G2Comparison uses the constructed coordinates and common kernel to compare
the reciprocal field actions. This generalizes the checked field-four
LineAction/G2 argument while retaining the degree n of the original quotient.
Source: MS93 (3.2), pp.865--866; Aschbacher--Smith 11.1.5, p.765.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open scoped IsMulCommutative Pointwise commutatorElement
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.Exceptional
variable {n : ℕ}
open Atlas.G2
/-- Reciprocal indices give actual offenders, retaining their full actions. -/
theorem critical_actor_offenders
    {M J₁ J₂ : Type*} [Group M] [Finite M]
    [Group J₁] [Finite J₁] [Group J₂] [Finite J₂]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hC : EdgeCentralizerCondition R)
    {B₁ : Subgroup J₁} {B₂ : Subgroup J₂}
    (Ea : VertexAction n R a B₁) (Ez : VertexAction n R z B₂) :
    IsOffender Ez.action (criticalActor path Ez.quotient).range := by
  have hba : 0 < criticalDistance R a (geometry.exists_critical a path.start_color) := by
    rw [geometry.distance_constant a path.start_color]; exact hb
  have hrev := critical_reverse R geometry hC a path.start_color hba z path.end_color path.critical
  let rev : CriticalPath R geometry z a := CriticalPath.ofPair path.end_color hrev
  have hcomm := critical_noncommutation R geometry hC a path.start_color hba path.critical
  have hcomm' : ⁅Z R z,Z R a⁆ ≠ ⊥ := by rwa [commutator_comm]
  obtain ⟨hAe,hcarde,hbe⟩ := critical_actor_bounds path hb hcomm Ez
  obtain ⟨hAa,hcarda,hba'⟩ := critical_actor_bounds rev hb hcomm' Ea
  have hbe' : 2 ^ fixedCodim Ez.action (criticalActor path Ez.quotient).range ≤
      Nat.card (criticalActor rev Ea.quotient).range := by rwa [hcarda]
  have hba'' : 2 ^ fixedCodim Ea.action (criticalActor rev Ea.quotient).range ≤
      Nat.card (criticalActor path Ez.quotient).range := by rwa [hcarde]
  let := Ea.component_normal
  let := Ez.component_normal
  have hh := reciprocal_natural_offenders Ez.field Ea.field Ez.nonbinary Ea.nonbinary
    Ez.action Ea.action _ _ Ez.componentEquiv Ea.componentEquiv
    Ez.component_apply Ea.component_apply Ez.faithful Ea.faithful _ _ hAe hAa hbe' hba''
  exact hh.1

/-- Every actual critical image has one marking for all three root curves,
with kernel the literal opposite-seed centralizer. -/
theorem critical_root_coordinates
    {M J₁ J₂ : Type*} [Group M] [Finite M]
    [Group J₁] [Finite J₁] [Group J₂] [Finite J₂]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hC : EdgeCentralizerCondition R)
    {B₁ : Subgroup J₁} {B₂ : Subgroup J₂}
    (Ea : VertexAction n R a B₁) (Ez : VertexAction n R z B₂) :
    ∃ p : Z R a →* Multiplicative (Fin 3 → Ez.field.Carrier), Function.Surjective p ∧
      p.ker = (centralizer (Z R z : Set (FreeAmalgam R))).subgroupOf (Z R a) ∧
      ∃ η : Natural.Space Ez.field.Carrier ≃ₗ[Ez.field.Carrier] (Fin 6 → Ez.field.Carrier),
        ∀ x v, η (Ez.action (criticalActor path Ez.quotient x) v) - η v =
          ![rootDisplacement (p x).toAdd ![η v 3,η v 4,η v 5] 0,
            rootDisplacement (p x).toAdd ![η v 3,η v 4,η v 5] 1,
            rootDisplacement (p x).toAdd ![η v 3,η v 4,η v 5] 2,0,0,0] := by
  let := Ez.component_normal
  obtain ⟨p,hp,hk,η,hη⟩ := inner_offender_displacement_coordinates Ez.field Ez.nonbinary Ez.action
    _ Ez.componentEquiv Ez.component_apply Ez.faithful _
    (critical_actor_offenders path hb hC Ea Ez)
  refine ⟨p,hp,hk.trans ?_,η,hη⟩
  exact ChapterC.RankTwo.Sp4Four.SourceComparison.restricted_kernel_of_mapped_centralizer
    _ _ _ _ Ez.quotient Ez.kernel_centralizer


/-- Conjugation and the projection retain the original group commutator. -/
theorem VertexAction.projected_commutator
    {M J : Type*} [Group M] [Group J]
    {R : Subgroup M} {z : Vertex R} {B : Subgroup J}
    (E : VertexAction n R z B) (g : stabilizer R z) (u d : U R z)
    (hd : (d : FreeAmalgam R) = ⁅(g : FreeAmalgam R),(u : FreeAmalgam R)⁆) :
    (E.projection d).toAdd = E.action (E.quotient g) (E.projection u).toAdd -
      (E.projection u).toAdd := by
  let c : U R z := ⟨g.val*u.val*g.val⁻¹,
    (mem_normalizer_iff.mp (U_normalized z g.property) u.val).mp u.property⟩
  have hd' : d = c * u⁻¹ := by
    apply Subtype.ext
    change (d : FreeAmalgam R) = (g : FreeAmalgam R) * u * (g : FreeAmalgam R)⁻¹ * (u : FreeAmalgam R)⁻¹
    simpa only [commutatorElement_def] using hd
  rw [hd',map_mul,map_inv,E.conjugate]
  simp only [toAdd_mul,toAdd_ofAdd,toAdd_inv,sub_eq_add_neg]


/-- The moving subgroup already has the full reciprocal centralizer index;
passing from U to Z adds no element to either critical image. -/
theorem critical_moving_index
    {M J₁ J₂ : Type*} [Group M] [Finite M]
    [Group J₁] [Finite J₁] [Group J₂] [Finite J₂]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hC : EdgeCentralizerCondition R)
    {B₁ : Subgroup J₁} {B₂ : Subgroup J₂}
    (Ea : VertexAction n R a B₁) (Ez : VertexAction n R z B₂) :
    (centralizer (Z R z : Set (FreeAmalgam R))).relIndex (U R a) = 2 ^ (3*n) := by
  let := finite_Z R a
  let : Finite (U R a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  have hba : 0 < criticalDistance R a (geometry.exists_critical a path.start_color) := by
    rw [geometry.distance_constant a path.start_color]; exact hb
  have hrev := critical_reverse R geometry hC a path.start_color hba z path.end_color path.critical
  let rev : CriticalPath R geometry z a := CriticalPath.ofPair path.end_color hrev
  let := Ea.component_normal
  let := Ez.component_normal
  have hae := critical_actor_offenders path hb hC Ea Ez
  have haa := critical_actor_offenders rev hb hC Ez Ea
  obtain ⟨_,hre,_⟩ := ambient_offender_rank Ez.field Ez.nonbinary Ez.action _
    Ez.componentEquiv Ez.component_apply Ez.faithful _ hae
  obtain ⟨_,_,hda⟩ := ambient_offender_rank Ea.field Ea.nonbinary Ea.action _
    Ea.componentEquiv Ea.component_apply Ea.faithful _ haa
  rw [Ez.degree] at hre
  rw [Ea.degree] at hda
  have hcomm := critical_noncommutation R geometry hC a path.start_color hba path.critical
  have hidx := (critical_actor_bounds path hb hcomm Ez).2.1.symm
  have hidx' : (centralizer (Z R z : Set (FreeAmalgam R))).relIndex (Z R a) = 2 ^ (3*n) := by
    rw [hidx,hae.1.card_eq_two_pow_rank,hre]
  have hlo := natural_fixed_index_le Ea.action (U R a) (Z R z)
    ((Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
      hrev.1.le).trans (U_normalized a)) Ea.projection Ea.projection_surjective
    (criticalActor rev Ea.quotient) (fun x u => Ea.conjugate
      (inclusion (Z_le_stabilizer_of_dist_le z
        (geometry.exists_critical z path.end_color) hrev.1.le) x) u)
  rw [hda] at hlo
  have hup := relIndex_le_of_le_right (H := centralizer (Z R z : Set (FreeAmalgam R)))
    (U_le_Z a) index_ne_zero_of_finite
  rw [hidx'] at hup
  exact le_antisymm hup hlo

/-- The three root parameters are already attained by the actual moving
subgroup; this preserves the opposite centralizer as the kernel. -/
theorem critical_moving_parameters_surjective
    {M J₁ J₂ : Type*} [Group M] [Finite M]
    [Group J₁] [Finite J₁] [Group J₂] [Finite J₂]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hC : EdgeCentralizerCondition R)
    {B₁ : Subgroup J₁} {B₂ : Subgroup J₂}
    (Ea : VertexAction n R a B₁) (Ez : VertexAction n R z B₂)
    (p : Z R a →* Multiplicative (Fin 3 → Ez.field.Carrier))
    (hk : p.ker = (centralizer (Z R z : Set (FreeAmalgam R))).subgroupOf (Z R a)) :
    Function.Surjective (p.comp (inclusion (U_le_Z a))) := by
  let := finite_Z R a
  let : Finite (U R a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  let q := p.comp (inclusion (U_le_Z a))
  have hq : q.ker = (centralizer (Z R z : Set (FreeAmalgam R))).subgroupOf (U R a) := by
    ext x
    change inclusion (U_le_Z a) x ∈ p.ker ↔ _
    rw [hk]
    rfl
  have hc : Nat.card q.range = 2 ^ (3*n) := by
    rw [←index_ker,hq]
    exact critical_moving_index path hb hC Ea Ez
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_card_eq
  rw [hc]
  change 2 ^ (3*n) = Nat.card (Fin 3 → Ez.field.Carrier)
  rw [Nat.card_fun,Ez.field.card_eq,Ez.degree,Nat.card_fin,←pow_mul,Nat.mul_comm n 3]


/-- Root coordinates for one actual critical image. The image of U is full,
and the parameters vanish exactly on the original centralizer. -/
structure CriticalRootCoordinates
    {M J : Type*} [Group M] [Group J]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) {B : Subgroup J} (E : VertexAction n R z B) where
  parameters : Z R a →* Multiplicative (Fin 3 → E.field.Carrier)
  surjective : Function.Surjective parameters
  moving_surjective : Function.Surjective (parameters.comp (inclusion (U_le_Z a)))
  kernel : parameters.ker =
    (centralizer (Z R z : Set (FreeAmalgam R))).subgroupOf (Z R a)
  coordinates : Natural.Space E.field.Carrier ≃ₗ[E.field.Carrier] (Fin 6 → E.field.Carrier)
  displacement : ∀ x v,
    coordinates (E.action (criticalActor path E.quotient x) v) - coordinates v =
      ![rootDisplacement (parameters x).toAdd ![coordinates v 3,coordinates v 4,coordinates v 5] 0,
        rootDisplacement (parameters x).toAdd ![coordinates v 3,coordinates v 4,coordinates v 5] 1,
        rootDisplacement (parameters x).toAdd ![coordinates v 3,coordinates v 4,coordinates v 5] 2,0,0,0]

/-- Reciprocal marked actions construct root coordinates on the full moving image. -/
theorem criticalRootCoordinates_nonempty
    {M J₁ J₂ : Type*} [Group M] [Finite M]
    [Group J₁] [Finite J₁] [Group J₂] [Finite J₂]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hC : EdgeCentralizerCondition R)
    {B₁ : Subgroup J₁} {B₂ : Subgroup J₂}
    (Ea : VertexAction n R a B₁) (Ez : VertexAction n R z B₂) :
    Nonempty (CriticalRootCoordinates path Ez) := by
  obtain ⟨p,hp,hk,η,hη⟩ := critical_root_coordinates path hb hC Ea Ez
  exact ⟨⟨p,hp,critical_moving_parameters_surjective path hb hC Ea Ez p hk,hk,η,hη⟩⟩

/-- The root-coordinate formula holds on the original group commutator,
through the original natural projection. -/
theorem CriticalRootCoordinates.projected_commutator
    {M J : Type*} [Group M] [Group J]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    {path : CriticalPath R geometry a z} {B : Subgroup J} {E : VertexAction n R z B}
    (c : CriticalRootCoordinates path E) (x : Z R a) (u d : U R z)
    (hd : (d : FreeAmalgam R) = ⁅(x : FreeAmalgam R),(u : FreeAmalgam R)⁆) :
    c.coordinates (E.projection d).toAdd =
      ![rootDisplacement (c.parameters x).toAdd
          ![c.coordinates (E.projection u).toAdd 3,c.coordinates (E.projection u).toAdd 4,
            c.coordinates (E.projection u).toAdd 5] 0,
        rootDisplacement (c.parameters x).toAdd
          ![c.coordinates (E.projection u).toAdd 3,c.coordinates (E.projection u).toAdd 4,
            c.coordinates (E.projection u).toAdd 5] 1,
        rootDisplacement (c.parameters x).toAdd
          ![c.coordinates (E.projection u).toAdd 3,c.coordinates (E.projection u).toAdd 4,
            c.coordinates (E.projection u).toAdd 5] 2,0,0,0] := by
  let g : stabilizer R z := inclusion (Z_le_stabilizer_of_dist_le a
    (geometry.exists_critical a path.start_color) path.critical.1.le) x
  rw [E.projected_commutator g u d hd,map_sub]
  exact c.displacement x (E.projection u).toAdd


/-- The intrinsic central-kernel criterion for every actual offender at a vertex. -/
def HasOffenderKernel {M J : Type*} [Group M] [Group J]
    {R₀ : Subgroup M} {a : Vertex R₀} {B : Subgroup J}
    (E : VertexAction n R₀ a B) : Prop :=
  ∀ (A : Subgroup (FreeAmalgam R₀)) (hA : A ≤ stabilizer R₀ a),
    BinaryOffender.IsOffender E.action (E.quotient.comp (inclusion hA)).range →
    (U R₀ a ⊓ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀))) ≤ ⁅A,U R₀ a⁆ ∧
    ∀ x ∈ ⁅A,U R₀ a⁆, x ≠ 1 →
      (x ∈ U R₀ a ⊓ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀)) ↔
        ¬ ∃ y ∈ A, ∃ u ∈ U R₀ a, ⁅y,u⁆ = x)

/-- Restricting the critical actor to U preserves its entire image. -/
theorem critical_moving_range
    {M J₁ J₂ : Type*} [Group M] [Finite M]
    [Group J₁] [Finite J₁] [Group J₂] [Finite J₂]
    {R₀ : Subgroup M} {geometry : Geometry R₀} {a z : Vertex R₀}
    (path : CriticalPath R₀ geometry a z) (hb : 0 < geometry.b R₀)
    (hC : EdgeCentralizerCondition R₀)
    {B₁ : Subgroup J₁} {B₂ : Subgroup J₂}
    (Ea : VertexAction n R₀ a B₁) (Ez : VertexAction n R₀ z B₂) :
    ((criticalActor path Ez.quotient).comp (inclusion (U_le_Z a))).range =
      (criticalActor path Ez.quotient).range := by
  let δ := criticalActor path Ez.quotient
  let d := δ.comp (inclusion (U_le_Z a))
  let := finite_Z R₀ a
  let : Finite (U R₀ a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  have hk : d.ker = (centralizer (Z R₀ z : Set (FreeAmalgam R₀))).subgroupOf (U R₀ a) :=
    ChapterC.RankTwo.Sp4Four.SourceComparison.restricted_kernel_of_mapped_centralizer
      _ _ _ ((U_le_Z a).trans (Z_le_stabilizer_of_dist_le a
        (geometry.exists_critical a path.start_color) path.critical.1.le))
      Ez.quotient Ez.kernel_centralizer
  have hc : Nat.card d.range = 2 ^ (3*n) := by
    rw [←index_ker,hk]
    exact critical_moving_index path hb hC Ea Ez
  let := Ez.component_normal
  have hoff := critical_actor_offenders path hb hC Ea Ez
  have hr := (ambient_offender_rank Ez.field Ez.nonbinary Ez.action _
    Ez.componentEquiv Ez.component_apply Ez.faithful _ hoff).2.1
  rw [Ez.degree] at hr
  have hc' : Nat.card δ.range = 2 ^ (3*n) := by
    rw [hoff.1.card_eq_two_pow_rank,hr]
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,rfl⟩
    exact ⟨inclusion (U_le_Z a) x,rfl⟩
  · exact le_of_eq (hc'.trans hc.symm)

/-- The opposite moving subgroup is itself an offender in the full vertex action. -/
theorem critical_moving_offender
    {M J₁ J₂ : Type*} [Group M] [Finite M]
    [Group J₁] [Finite J₁] [Group J₂] [Finite J₂]
    {R₀ : Subgroup M} {geometry : Geometry R₀} {a z : Vertex R₀}
    (path : CriticalPath R₀ geometry a z) (hb : 0 < geometry.b R₀)
    (hC : EdgeCentralizerCondition R₀)
    {B₁ : Subgroup J₁} {B₂ : Subgroup J₂}
    (Ea : VertexAction n R₀ a B₁) (Ez : VertexAction n R₀ z B₂) :
    IsOffender Ez.action ((criticalActor path Ez.quotient).comp (inclusion (U_le_Z a))).range := by
  rw [critical_moving_range path hb hC Ea Ez]
  exact critical_actor_offenders path hb hC Ea Ez

/-- The two actual critical cover kernels are equal inside the original amalgam,
and this common kernel lies in the commutator of the two moving subgroups. -/
theorem critical_kernels_eq
    {M J₁ J₂ : Type*} [Group M] [Finite M]
    [Group J₁] [Finite J₁] [Group J₂] [Finite J₂]
    {R₀ : Subgroup M} {geometry : Geometry R₀} {a z : Vertex R₀}
    (path : CriticalPath R₀ geometry a z) (hb : 0 < geometry.b R₀)
    (hC : EdgeCentralizerCondition R₀)
    {B₁ : Subgroup J₁} {B₂ : Subgroup J₂}
    (Ea : VertexAction n R₀ a B₁) (Ez : VertexAction n R₀ z B₂)
    (ha : HasOffenderKernel Ea) (hz : HasOffenderKernel Ez) :
    U R₀ a ⊓ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀)) =
      U R₀ z ⊓ centralizer (Ltilde R₀ z : Set (FreeAmalgam R₀)) ∧
    U R₀ a ⊓ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀)) ≤ ⁅U R₀ a,U R₀ z⁆ := by
  have hba : 0 < criticalDistance R₀ a (geometry.exists_critical a path.start_color) := by
    rw [geometry.distance_constant a path.start_color]
    exact hb
  have hrev := critical_reverse R₀ geometry hC a path.start_color hba z path.end_color path.critical
  let rev : CriticalPath R₀ geometry z a := CriticalPath.ofPair path.end_color hrev
  have hUa := (U_le_Z a).trans (Z_le_stabilizer_of_dist_le a
    (geometry.exists_critical a path.start_color) path.critical.1.le)
  have hUz := (U_le_Z z).trans (Z_le_stabilizer_of_dist_le z
    (geometry.exists_critical z path.end_color) hrev.1.le)
  obtain ⟨hkz,hcz⟩ := hz (U R₀ a) hUa (critical_moving_offender path hb hC Ea Ez)
  obtain ⟨hka,hca⟩ := ha (U R₀ z) hUz (critical_moving_offender rev hb hC Ez Ea)
  exact ⟨(embedded_kernels_eq (U R₀ a) (U R₀ z) _ _ hkz hcz hka hca).symm,
    by rwa [commutator_comm] at hka⟩


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.Exceptional
