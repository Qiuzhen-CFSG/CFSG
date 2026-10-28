module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.MSRootCoordinates
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.MSCriticalActors

/-!
# Root coordinates on both original critical moving images

The reciprocal natural bounds give offenders on the full vertex actions.
The moving subgroup U already has centralizer index 64, so its image equals
the full critical image of Z. All three root parameters are therefore
attained on U. The quotient kernel stays the literal opposite-seed
centralizer, and the projection of each original group commutator has the
marked root-displacement formula.

The final theorem constructs both systems from Sylow-normalizer escape,
using the same original quotient and critical pair. Compatible invertible
scalar maps tested on these two moving subgroups must be identity. This is
the coordinate obstruction for the field comparison in MS93 (3.2),
pp.865--866; the identification of the two central-cover kernels remains
with qt-d-1222-natural-line-action. Final 11.2.3 assembly belongs to
qt-d-1222-natural-normalizer-source.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement
open Atlas.G2
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

/-- Reciprocal indices give actual offenders, retaining their full actions. -/
theorem critical_actor_offenders
    {M J₁ J₂ : Type*} [Group M] [Finite M]
    [Group J₁] [Finite J₁] [Group J₂] [Finite J₂]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hC : EdgeCentralizerCondition R)
    {B₁ : Subgroup J₁} {B₂ : Subgroup J₂}
    (Ea : VertexAction R a B₁) (Ez : VertexAction R z B₂) :
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
  obtain ⟨_,_,horde,_,hde,_⟩ := reciprocal_natural_indices Ez.field Ea.field Ez.degree Ea.degree
    Ez.action Ea.action _ _ Ez.componentEquiv Ea.componentEquiv
    Ez.component_apply Ea.component_apply Ez.faithful Ea.faithful _ _ hAe hAa hbe' hba''
  exact ⟨hAe,by rw [hde,rank,horde]; decide⟩

/-- Every actual critical image has one marking for all three root curves,
with kernel the literal opposite-seed centralizer. -/
theorem critical_root_coordinates
    {M J₁ J₂ : Type*} [Group M] [Finite M]
    [Group J₁] [Finite J₁] [Group J₂] [Finite J₂]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hC : EdgeCentralizerCondition R)
    {B₁ : Subgroup J₁} {B₂ : Subgroup J₂}
    (Ea : VertexAction R a B₁) (Ez : VertexAction R z B₂) :
    ∃ p : Z R a →* Multiplicative (Fin 3 → Ez.field.Carrier), Function.Surjective p ∧
      p.ker = (centralizer (Z R z : Set (FreeAmalgam R))).subgroupOf (Z R a) ∧
      ∃ η : Natural.Space Ez.field.Carrier ≃ₗ[Ez.field.Carrier] (Fin 6 → Ez.field.Carrier),
        ∀ x v, η (Ez.action (criticalActor path Ez.quotient x) v) - η v =
          ![rootDisplacement (p x).toAdd ![η v 3,η v 4,η v 5] 0,
            rootDisplacement (p x).toAdd ![η v 3,η v 4,η v 5] 1,
            rootDisplacement (p x).toAdd ![η v 3,η v 4,η v 5] 2,0,0,0] := by
  let := Ez.component_normal
  obtain ⟨p,hp,hk,η,hη⟩ := inner_offender_displacement_coordinates Ez.field Ez.degree Ez.action
    _ Ez.componentEquiv Ez.component_apply Ez.faithful _
    (critical_actor_offenders path hb hC Ea Ez)
  refine ⟨p,hp,hk.trans ?_,η,hη⟩
  exact ChapterC.RankTwo.Sp4Four.SourceComparison.restricted_kernel_of_mapped_centralizer
    _ _ _ _ Ez.quotient Ez.kernel_centralizer


/-- Conjugation and the projection retain the original group commutator. -/
theorem VertexAction.projected_commutator
    {M J : Type*} [Group M] [Group J]
    {R : Subgroup M} {z : Vertex R} {B : Subgroup J}
    (E : VertexAction R z B) (g : stabilizer R z) (u d : U R z)
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
    (Ea : VertexAction R a B₁) (Ez : VertexAction R z B₂) :
    (centralizer (Z R z : Set (FreeAmalgam R))).relIndex (U R a) = 64 := by
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
  obtain ⟨_,hre,_⟩ := ambient_offender_rank_six Ez.field Ez.degree Ez.action _
    Ez.componentEquiv Ez.component_apply Ez.faithful _ hae
  obtain ⟨_,_,hda⟩ := ambient_offender_rank_six Ea.field Ea.degree Ea.action _
    Ea.componentEquiv Ea.component_apply Ea.faithful _ haa
  have hcomm := critical_noncommutation R geometry hC a path.start_color hba path.critical
  have hidx := (critical_actor_bounds path hb hcomm Ez).2.1.symm
  have hidx' : (centralizer (Z R z : Set (FreeAmalgam R))).relIndex (Z R a) = 64 := by
    rw [hidx,hae.1.card_eq_two_pow_rank,hre]
    rfl
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
    (Ea : VertexAction R a B₁) (Ez : VertexAction R z B₂)
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
  have hc : Nat.card q.range = 64 := by
    rw [←index_ker,hq]
    exact critical_moving_index path hb hC Ea Ez
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_card_eq
  rw [hc]
  change 64 = Nat.card (Fin 3 → Ez.field.Carrier)
  rw [Nat.card_fun,Ez.field.card_eq,Ez.degree,Nat.card_fin]
  decide


/-- Root coordinates for one actual critical image. The image of U is full,
and the parameters vanish exactly on the original centralizer. -/
structure CriticalRootCoordinates
    {M J : Type*} [Group M] [Group J]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) {B : Subgroup J} (E : VertexAction R z B) where
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
    (Ea : VertexAction R a B₁) (Ez : VertexAction R z B₂) :
    Nonempty (CriticalRootCoordinates path Ez) := by
  obtain ⟨p,hp,hk,η,hη⟩ := critical_root_coordinates path hb hC Ea Ez
  exact ⟨⟨p,hp,critical_moving_parameters_surjective path hb hC Ea Ez p hk,hk,η,hη⟩⟩

/-- The root-coordinate formula holds on the original group commutator,
through the original natural projection. -/
theorem CriticalRootCoordinates.projected_commutator
    {M J : Type*} [Group M] [Group J]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    {path : CriticalPath R geometry a z} {B : Subgroup J} {E : VertexAction R z B}
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


/-- Testing the original two moving subgroups already forces every
invertible compatible scalar map on the actor and displacement to be trivial. -/
theorem CriticalRootCoordinates.compatible_maps_trivial
    {M J : Type*} [Group M] [Group J]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    {path : CriticalPath R geometry a z} {B : Subgroup J} {E : VertexAction R z B}
    (c : CriticalRootCoordinates path E)
    (s t : (Fin 3 → E.field.Carrier) → (Fin 3 → E.field.Carrier))
    (hs : Function.Injective s)
    (h : ∀ (x : U R a) (u : U R z),
      rootDisplacement (s (c.parameters (inclusion (U_le_Z a) x)).toAdd)
          ![c.coordinates (E.projection u).toAdd 3,c.coordinates (E.projection u).toAdd 4,
            c.coordinates (E.projection u).toAdd 5] =
        t (rootDisplacement (c.parameters (inclusion (U_le_Z a) x)).toAdd
          ![c.coordinates (E.projection u).toAdd 3,c.coordinates (E.projection u).toAdd 4,
            c.coordinates (E.projection u).toAdd 5])) :
    s = id ∧ t = id := by
  apply rootDisplacement_compatible_injective s t hs
  intro p v
  obtain ⟨x,hx⟩ := c.moving_surjective (Multiplicative.ofAdd p)
  have hx' : (c.parameters (inclusion (U_le_Z a) x)).toAdd = p :=
    congrArg Multiplicative.toAdd hx
  let w : Fin 6 → E.field.Carrier := ![0,0,0,v 0,v 1,v 2]
  obtain ⟨u,hu⟩ := E.projection_surjective (Multiplicative.ofAdd (c.coordinates.symm w))
  have hw : c.coordinates (E.projection u).toAdd = w := by
    rw [hu,toAdd_ofAdd,c.coordinates.apply_symm_apply]
  have hh := h x u
  rw [hx',hw] at hh
  have hv : ![v 0,v 1,v 2] = v := by ext i; fin_cases i <;> rfl
  simpa [w,hv] using hh

open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
local notation "H" => (L ⊔ (T : Subgroup G) : Subgroup G)
local notation "K" => Subgroup.subgroupOf L (L ⊔ (T : Subgroup G))
local notation "R" => Subgroup.subgroupOf (T : Subgroup G) (L ⊔ (T : Subgroup G))

include D S m in
/-- The original escape constructs all three root coordinates on the actual
critical moving image. It retains the marking, quotient, projection and kernel. -/
theorem source_critical_root_coordinates
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R) :
    ∃ E : VertexAction R z ((K).map (QuotientGroup.mk' (pCore 2 H))),
      Nonempty (CriticalRootCoordinates path E) := by
  obtain ⟨Ea⟩ := source_vertex_action D S m hescape path.start_color
  obtain ⟨Ez⟩ := source_vertex_action D S m hescape path.end_color
  exact ⟨Ez,criticalRootCoordinates_nonempty path hb
    (source_critical_geometry D S m hescape).2 Ea Ez⟩


include D S m in
/-- Both reciprocal root-coordinate systems are constructed from Sylow
normalizer escape alone, on the same literal quotient and original critical pair. -/
theorem source_critical_root_pair
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ g : Geometry R, 0 < g.b R ∧ Even (g.b R) ∧
      ∃ a : Vertex R, ∃ ha : color R a = false,
      ∃ hc : CriticalPair R (alpha R) a (g.exists_critical (alpha R) rfl),
      ∃ hr : CriticalPair R a (alpha R) (g.exists_critical a ha),
        ⁅Z R (alpha R),Z R a⁆ ≠ ⊥ ∧
      ∃ Ea : VertexAction R (alpha R) ((K).map (QuotientGroup.mk' (pCore 2 H))),
      ∃ Ez : VertexAction R a ((K).map (QuotientGroup.mk' (pCore 2 H))),
        Nonempty (CriticalRootCoordinates (CriticalPath.ofPair (geometry := g) rfl hc) Ez) ∧
        Nonempty (CriticalRootCoordinates (CriticalPath.ofPair (geometry := g) ha hr) Ea) := by
  obtain ⟨g,hpos,hev,a,ha,hc,hr,hn⟩ := source_critical_pair D S m hescape
  obtain ⟨Ea⟩ := source_vertex_action D S m hescape (show color R (alpha R) = false from rfl)
  obtain ⟨Ez⟩ := source_vertex_action D S m hescape ha
  have hC := (source_critical_geometry D S m hescape).2
  exact ⟨g,hpos,hev,a,ha,hc,hr,hn,Ea,Ez,
    criticalRootCoordinates_nonempty (CriticalPath.ofPair (geometry := g) rfl hc) hpos hC Ea Ez,
    criticalRootCoordinates_nonempty (CriticalPath.ofPair (geometry := g) ha hr) hpos hC Ez Ea⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
