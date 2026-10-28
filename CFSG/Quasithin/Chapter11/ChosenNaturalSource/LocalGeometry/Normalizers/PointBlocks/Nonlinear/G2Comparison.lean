module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.G2Critical

/-!
# The reciprocal field obstruction for the original exceptional point pair

The original commutator projects onto each three-dimensional displacement
space. Equality of the embedded cover kernels identifies these projections.
Their marked displacement formulas are reciprocal, so the proved scalar
obstruction forces the coefficient field to have at most two elements.
This contradicts the original nonbinary degree, without a field-four bound.
G2Exclusion constructs every hypothesis on the literal point pair LR₁.

The field-independent comparison follows LineAction/G2/MSFieldComparison;
only the general critical-action construction and final degree bound change.
Source: MS93 (3.2), pp.865--866; Aschbacher--Smith 11.1.5, p.765.
Octonion attribution: LICENSES/ATLAS.txt.
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
private def headThree {F : Type*} [Field F] : (Fin 6 → F) →ₗ[F] (Fin 3 → F) where
  toFun v := ![v 0,v 1,v 2]
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

private def tailThree {F : Type*} [Field F] : (Fin 6 → F) →ₗ[F] (Fin 3 → F) where
  toFun v := ![v 3,v 4,v 5]
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

private theorem head_tail_zero {F : Type*} [Field F] {v : Fin 6 → F}
    (hh : headThree v = 0) (ht : tailThree v = 0) : v = 0 := by
  ext i
  fin_cases i
  · exact congrFun hh 0
  · exact congrFun hh 1
  · exact congrFun hh 2
  · exact congrFun ht 0
  · exact congrFun ht 1
  · exact congrFun ht 2

variable {M J : Type*} [Group M] [Group J]
  {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
  {path : CriticalPath R geometry a z} {B : Subgroup J} {E : VertexAction n R z B}

private def coordinateProjection (c : CriticalRootCoordinates path E) :
    U R z →* Multiplicative (Fin 6 → E.field.Carrier) :=
  c.coordinates.toLinearMap.toAddMonoidHom.toMultiplicative.comp E.projection

private def commutatorProjection (c : CriticalRootCoordinates path E)
    (hz : (⁅U R a,U R z⁆ : Subgroup (FreeAmalgam R)) ≤ U R z) :
    (⁅U R a,U R z⁆ : Subgroup (FreeAmalgam R)) →* Multiplicative (Fin 3 → E.field.Carrier) :=
  headThree.toAddMonoidHom.toMultiplicative.comp
    ((coordinateProjection c).comp (inclusion hz))

private theorem commutator_projection_apply (c : CriticalRootCoordinates path E)
    (hz : (⁅U R a,U R z⁆ : Subgroup (FreeAmalgam R)) ≤ U R z) (x : U R a) (y : U R z) :
    (commutatorProjection c hz ⟨⁅x.val,y.val⁆,commutator_mem_commutator x.property y.property⟩).toAdd =
      rootDisplacement (c.parameters (inclusion (U_le_Z a) x)).toAdd
        (tailThree (coordinateProjection c y).toAdd) := by
  have hh := c.projected_commutator (inclusion (U_le_Z a) x) y
    ⟨⁅x.val,y.val⁆,hz (commutator_mem_commutator x.property y.property)⟩ rfl
  have h := congrArg (fun v => headThree v) hh
  change headThree (c.coordinates (E.projection ⟨⁅x.val,y.val⁆,_⟩).toAdd) = _
  exact h

private theorem commutator_tail_zero (c : CriticalRootCoordinates path E)
    (hz : (⁅U R a,U R z⁆ : Subgroup (FreeAmalgam R)) ≤ U R z) (w : (⁅U R a,U R z⁆ : Subgroup (FreeAmalgam R))) :
    tailThree (coordinateProjection c (inclusion hz w)).toAdd = 0 := by
  let N : Subgroup (U R z) := (tailThree.ker.toAddSubgroup.toSubgroup).comap (coordinateProjection c)
  have hn : (⁅U R a,U R z⁆ : Subgroup (FreeAmalgam R)) ≤ N.map (U R z).subtype := by
    apply commutator_le.mpr
    intro x hx y hy
    refine ⟨⟨⁅x,y⁆,hz (commutator_mem_commutator hx hy)⟩,?_,rfl⟩
    have hh := c.projected_commutator (inclusion (U_le_Z a) ⟨x,hx⟩) ⟨y,hy⟩
      ⟨⁅x,y⁆,hz (commutator_mem_commutator hx hy)⟩ rfl
    change tailThree (c.coordinates (E.projection ⟨⁅x,y⁆,_⟩).toAdd) = 0
    rw [hh]
    ext i
    fin_cases i <;> rfl
  obtain ⟨v,hv,he⟩ := hn w.property
  have he' : v = inclusion hz w := Subtype.ext he
  exact he' ▸ hv

private theorem commutator_projection_kernel (c : CriticalRootCoordinates path E)
    (hz : (⁅U R a,U R z⁆ : Subgroup (FreeAmalgam R)) ≤ U R z) (w : (⁅U R a,U R z⁆ : Subgroup (FreeAmalgam R))) :
    commutatorProjection c hz w = 1 ↔ E.projection (inclusion hz w) = 1 := by
  change headThree (coordinateProjection c (inclusion hz w)).toAdd = 0 ↔ _
  constructor
  · intro hh
    have he := head_tail_zero hh (commutator_tail_zero c hz w)
    change c.coordinates (E.projection (inclusion hz w)).toAdd = 0 at he
    exact Multiplicative.toAdd.injective ((c.coordinates.map_eq_zero_iff).mp he)
  · intro he
    change headThree (c.coordinates (E.projection (inclusion hz w)).toAdd) = 0
    rw [he]
    simp only [toAdd_one,map_zero]

private theorem commutator_projection_surjective (c : CriticalRootCoordinates path E)
    (hz : (⁅U R a,U R z⁆ : Subgroup (FreeAmalgam R)) ≤ U R z) : Function.Surjective (commutatorProjection c hz) := by
  intro w
  obtain ⟨x,hx⟩ := c.moving_surjective (Multiplicative.ofAdd (![0,0,1] : Fin 3 → E.field.Carrier))
  let v : Fin 6 → E.field.Carrier := ![0,0,0,w.toAdd 1,w.toAdd 2,w.toAdd 0]
  obtain ⟨y,hy⟩ := E.projection_surjective (Multiplicative.ofAdd (c.coordinates.symm v))
  refine ⟨⟨⁅x.val,y.val⁆,commutator_mem_commutator x.property y.property⟩,?_⟩
  apply Multiplicative.toAdd.injective
  rw [commutator_projection_apply]
  have hx' : c.parameters (inclusion (U_le_Z a) x) = Multiplicative.ofAdd ![0,0,1] := hx
  change rootDisplacement _ (tailThree (c.coordinates (E.projection y).toAdd)) = _
  rw [hx',hy]
  simp only [toAdd_ofAdd,c.coordinates.apply_symm_apply]
  ext i
  fin_cases i <;> simp [rootDisplacement,tailThree,v]

private theorem tail_projection_surjective (c : CriticalRootCoordinates path E) :
    Function.Surjective (fun y => tailThree (coordinateProjection c y).toAdd) := by
  intro w
  let v : Fin 6 → E.field.Carrier := ![0,0,0,w 0,w 1,w 2]
  obtain ⟨y,hy⟩ := E.projection_surjective (Multiplicative.ofAdd (c.coordinates.symm v))
  refine ⟨y,?_⟩
  change tailThree (c.coordinates (E.projection y).toAdd) = w
  rw [hy,toAdd_ofAdd,c.coordinates.apply_symm_apply]
  ext i
  fin_cases i <;> rfl

private theorem projection_one_iff
    {M J : Type*} [Group M] [Group J] {R : Subgroup M}
    {a : Vertex R} {B : Subgroup J} (E : VertexAction n R a B) (w : U R a) :
    E.projection w = 1 ↔ w.val ∈ U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
  rw [←E.projection_kernel]
  constructor
  · intro h
    exact ⟨w,h,rfl⟩
  · rintro ⟨v,hv,he⟩
    have he' : v = w := Subtype.ext he
    rwa [he'] at hv

private theorem surjective_equiv_of_kernel_eq
    {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : A →* C) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : f.ker = g.ker) : ∃ e : B ≃* C, ∀ x, e (f x) = g x := by
  let e := (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg))
  refine ⟨e,?_⟩
  intro x
  have he : (QuotientGroup.quotientKerEquivOfSurjective f hf) (QuotientGroup.mk x) = f x := rfl
  change (QuotientGroup.quotientKerEquivOfSurjective g hg)
    ((QuotientGroup.quotientMulEquivOfEq h)
      ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f x))) = _
  rw [←he,MulEquiv.symm_apply_apply,QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

private theorem reciprocal_projections_binary
    {F E W X Y : Type*} [Field F] [Field E] [Group W]
    (fz : W →* Multiplicative (Fin 3 → F)) (fa : W →* Multiplicative (Fin 3 → E))
    (hfz : Function.Surjective fz) (hfa : Function.Surjective fa)
    (hk : ∀ w, fz w = 1 ↔ fa w = 1)
    (p : X → (Fin 3 → F)) (u : X → (Fin 3 → E))
    (r : Y → (Fin 3 → E)) (v : Y → (Fin 3 → F))
    (hp : Function.Surjective p) (hu : Function.Surjective u)
    (hr : Function.Surjective r) (hv : Function.Surjective v)
    (d : X → Y → W)
    (hdz : ∀ x y, (fz (d x y)).toAdd = rootDisplacement (p x) (v y))
    (hda : ∀ x y, (fa (d x y)).toAdd = rootDisplacement (r y) (u x))
    (c : E) : c = 0 ∨ c = 1 := by
  obtain ⟨em,hem⟩ := surjective_equiv_of_kernel_eq fz fa hfz hfa (SetLike.ext hk)
  let e : (Fin 3 → F) ≃ (Fin 3 → E) :=
    Multiplicative.ofAdd.trans (em.toEquiv.trans Multiplicative.toAdd)
  apply rootDisplacement_reciprocal_binary p u r v hp hu hr hv e _ c
  intro x y
  have hh := congrArg Multiplicative.toAdd (hem (d x y))
  change e (fz (d x y)).toAdd = (fa (d x y)).toAdd at hh
  rwa [hdz,hda] at hh

private theorem card_le_two_of_binary (E : Type*) [Field E]
    (hbinary : ∀ c : E, c = 0 ∨ c = 1) : Nat.card E ≤ 2 := by
  have hsur : Function.Surjective (fun b : Bool => if b then (0 : E) else 1) := by
    intro c
    rcases hbinary c with rfl | rfl
    · exact ⟨true,rfl⟩
    · exact ⟨false,rfl⟩
  exact (Nat.card_le_card_of_surjective _ hsur).trans_eq (by simp)

private def commonCoordinateProjection
    {M J : Type*} [Group M] [Group J]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    {path : CriticalPath R geometry a z} {B : Subgroup J} {E : VertexAction n R z B}
    (c : CriticalRootCoordinates path E)
    (W : Subgroup (FreeAmalgam R)) (hW : W ≤ U R z) :
    W →* Multiplicative (Fin 3 → E.field.Carrier) :=
  headThree.toAddMonoidHom.toMultiplicative.comp ((coordinateProjection c).comp (inclusion hW))

private theorem commonCoordinateProjection_one_iff
    {M J : Type*} [Group M] [Group J]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    {path : CriticalPath R geometry a z} {B : Subgroup J} {E : VertexAction n R z B}
    (c : CriticalRootCoordinates path E)
    (W : Subgroup (FreeAmalgam R)) (hW : W ≤ U R z)
    (he : W = (⁅U R a,U R z⁆ : Subgroup (FreeAmalgam R))) (w : W) :
    commonCoordinateProjection c W hW w = 1 ↔
      w.val ∈ U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
  subst W
  exact (commutator_projection_kernel c hW w).trans (projection_one_iff E (inclusion hW w))

private theorem commonCoordinateProjection_surjective
    {M J : Type*} [Group M] [Group J]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    {path : CriticalPath R geometry a z} {B : Subgroup J} {E : VertexAction n R z B}
    (c : CriticalRootCoordinates path E)
    (W : Subgroup (FreeAmalgam R)) (hW : W ≤ U R z)
    (he : W = (⁅U R a,U R z⁆ : Subgroup (FreeAmalgam R))) :
    Function.Surjective (commonCoordinateProjection c W hW) := by
  subst W
  exact commutator_projection_surjective c hW

private theorem commonCoordinateProjection_reverse
    {M J : Type*} [Group M] [Group J]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    {rev : CriticalPath R geometry z a} {B : Subgroup J} {Ea : VertexAction n R a B}
    (ca : CriticalRootCoordinates rev Ea)
    (ha : (⁅U R a,U R z⁆ : Subgroup (FreeAmalgam R)) ≤ U R a)
    (x : U R a) (y : U R z) :
    (commonCoordinateProjection ca _ ha
      ⟨⁅x.val,y.val⁆,commutator_mem_commutator x.property y.property⟩).toAdd =
      rootDisplacement (ca.parameters (inclusion (U_le_Z z) y)).toAdd
        (tailThree (coordinateProjection ca x).toAdd) := by
  have ha' : (⁅U R z,U R a⁆ : Subgroup (FreeAmalgam R)) ≤ U R a := by rwa [commutator_comm]
  have hh := commutator_projection_apply ca ha' y x
  let d : U R a := ⟨⁅y.val,x.val⁆,ha' (commutator_mem_commutator y.property x.property)⟩
  have he : (⟨⁅x.val,y.val⁆,ha (commutator_mem_commutator x.property y.property)⟩ : U R a) = d⁻¹ := by
    apply Subtype.ext
    exact (commutatorElement_inv y.val x.val).symm
  change headThree (coordinateProjection ca ⟨⁅x.val,y.val⁆,_⟩).toAdd = _
  rw [he,map_inv,toAdd_inv,map_neg]
  change -headThree (coordinateProjection ca d).toAdd = _
  change headThree (coordinateProjection ca d).toAdd = _ at hh
  rw [hh]
  ext i
  exact CharTwo.neg_eq _

private theorem reciprocal_coordinates_card_le_two
    {M J₁ J₂ : Type*} [Group M] [Group J₁] [Group J₂]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    {path : CriticalPath R geometry a z} {rev : CriticalPath R geometry z a}
    {B₁ : Subgroup J₁} {B₂ : Subgroup J₂}
    {Ea : VertexAction n R a B₁} {Ez : VertexAction n R z B₂}
    (ca : CriticalRootCoordinates rev Ea) (cz : CriticalRootCoordinates path Ez)
    (ha : (⁅U R a,U R z⁆ : Subgroup (FreeAmalgam R)) ≤ U R a)
    (hz : (⁅U R a,U R z⁆ : Subgroup (FreeAmalgam R)) ≤ U R z)
    (hk : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) =
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))) :
    Nat.card Ea.field.Carrier ≤ 2 := by
  let W : Subgroup (FreeAmalgam R) := ⁅U R a,U R z⁆
  let fz := commonCoordinateProjection cz W hz
  let fa := commonCoordinateProjection ca W ha
  have hmem (w : W) : fz w = 1 ↔ fa w = 1 :=
    (commonCoordinateProjection_one_iff cz W hz rfl w).trans
      ((Iff.of_eq (congrArg (fun K : Subgroup (FreeAmalgam R) => w.val ∈ K) hk.symm)).trans
        (commonCoordinateProjection_one_iff ca W ha (commutator_comm _ _) w).symm)
  apply card_le_two_of_binary
  exact reciprocal_projections_binary fz fa
    (commonCoordinateProjection_surjective cz W hz rfl)
    (commonCoordinateProjection_surjective ca W ha (commutator_comm _ _)) hmem
    (fun x : U R a => (cz.parameters (inclusion (U_le_Z a) x)).toAdd)
    (fun x : U R a => tailThree (coordinateProjection ca x).toAdd)
    (fun y : U R z => (ca.parameters (inclusion (U_le_Z z) y)).toAdd)
    (fun y : U R z => tailThree (coordinateProjection cz y).toAdd)
    (Multiplicative.toAdd.surjective.comp cz.moving_surjective)
    (tail_projection_surjective ca)
    (Multiplicative.toAdd.surjective.comp ca.moving_surjective)
    (tail_projection_surjective cz)
    (fun x y => ⟨⁅x.val,y.val⁆,commutator_mem_commutator x.property y.property⟩)
    (commutator_projection_apply cz hz) (commonCoordinateProjection_reverse ca ha)

/-- The common embedded kernel is incompatible with two reciprocal natural
nonbinary G₂ root actions. The original commutator supplies the output comparison. -/
theorem critical_root_actions_incompatible
    {M J₁ J₂ : Type*} [Group M] [Finite M]
    [Group J₁] [Finite J₁] [Group J₂] [Finite J₂]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hC : EdgeCentralizerCondition R)
    {B₁ : Subgroup J₁} {B₂ : Subgroup J₂}
    (Ea : VertexAction n R a B₁) (Ez : VertexAction n R z B₂)
    (hk : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) =
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))) : False := by
  have hba : 0 < criticalDistance R a (geometry.exists_critical a path.start_color) := by
    rw [geometry.distance_constant a path.start_color]
    exact hb
  have hrev := critical_reverse R geometry hC a path.start_color hba z path.end_color path.critical
  let rev : CriticalPath R geometry z a := CriticalPath.ofPair path.end_color hrev
  obtain ⟨cz⟩ := criticalRootCoordinates_nonempty path hb hC Ea Ez
  obtain ⟨ca⟩ := criticalRootCoordinates_nonempty rev hb hC Ez Ea
  have ha : (⁅U R a,U R z⁆ : Subgroup (FreeAmalgam R)) ≤ U R a :=
    le_normalizer_iff_commutator_le_left.mp ((U_le_Z z).trans
      ((Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color) hrev.1.le).trans
        (U_normalized a)))
  have hz : (⁅U R a,U R z⁆ : Subgroup (FreeAmalgam R)) ≤ U R z :=
    le_normalizer_iff_commutator_le_right.mp ((U_le_Z a).trans
      ((Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le).trans
        (U_normalized z)))
  have hcard := reciprocal_coordinates_card_le_two ca cz ha hz hk
  have hlo : 2 < Nat.card Ea.field.Carrier := by
    rw [Ea.field.card_eq]
    exact (show (2:ℕ)^1 < 2^Ea.field.degree from
      Nat.pow_lt_pow_right (by decide) Ea.nonbinary)
  omega

open CFSG.Quasithin.Chapter12.Section02


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.Exceptional
