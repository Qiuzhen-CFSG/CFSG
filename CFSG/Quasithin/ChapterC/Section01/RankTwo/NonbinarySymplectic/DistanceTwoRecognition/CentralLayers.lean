module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.Graph
public import Theory.GroupTheory.CComponent.SimpleNormalCentralizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Paths

/-!
# Central attachments in the distance-two argument

A normal subgroup of the moving layer contained in the opposite kernel is
fixed by the component. The faithful simple quotient detects this fixation
from the opposite critical Z-layer. Its image under the actual natural-cover
projection is therefore zero. The subgroup itself is retained: no triviality
of the central fixed attachment is assumed.

Source: MS93 (3.6), pp.870--872. This is the central-layer step used when
comparing secondary orbits; it does not assert the whole-core conclusion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource MSCentralOrbit

section Detection
variable {M J : Type*} [Group M] [Finite M] [Group J]
variable {R : Subgroup M} {a z : Vertex R}

private theorem normal_central_layer_le_fixed_of_opposite_kernel
    (N : Subgroup (FreeAmalgam R)) (hNX : N ≤ X R a) (hNQ : N ≤ Q R z)
    (hn : stabilizer R a ≤ normalizer N)
    (hzS : Z R z ≤ stabilizer R a) (hzQ : ¬ Z R z ≤ Q R a)
    (hz : color R z = false)
    (κ : stabilizer R a →* J) (hκ : Function.Surjective κ)
    (hk : κ.ker.map (stabilizer R a).subtype = Q R a)
    [(((Ltilde R a).subgroupOf (stabilizer R a)).map κ).Normal]
    [IsSimpleGroup (((Ltilde R a).subgroupOf (stabilizer R a)).map κ)]
    (hna : ¬ IsMulCommutative (((Ltilde R a).subgroupOf (stabilizer R a)).map κ))
    (hc : centralizer (((Ltilde R a).subgroupOf (stabilizer R a)).map κ : Set J) = ⊥) :
    N ≤ X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
  let S := stabilizer R a
  let P := N.subgroupOf S
  let C := centralizer (P : Set S)
  let : P.Normal := normal_subgroupOf_of_le_normalizer hn
  let : (C.map κ).Normal := Normal.map inferInstance κ hκ
  have hkC : κ.ker ≤ C := by
    intro x hx n hn
    apply Subtype.ext
    exact Q_le_centralizer_X R a (hk ▸ mem_map_of_mem S.subtype hx) n (hNX hn)
  have hEC : (Z R z).subgroupOf S ≤ C := by
    intro x hx n hn
    apply Subtype.ext
    exact (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R z hz)) hx n (hNQ hn)
  have hCne : C.map κ ≠ ⊥ := by
    intro he
    have hCk := (map_eq_bot_iff C).mp he
    apply hzQ
    intro x hx
    exact hk ▸ mem_map_of_mem S.subtype
      (hCk (hEC (show (⟨x,hzS hx⟩ : S) ∈ (Z R z).subgroupOf S from hx)))
  have hLC := simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot
    (((Ltilde R a).subgroupOf S).map κ) hna hc (C.map κ) hCne
  have hpre := comap_mono (f := κ) hLC
  rw [comap_map_eq,comap_map_eq,sup_of_le_left hkC] at hpre
  have hL : (Ltilde R a).subgroupOf S ≤ C := le_sup_left.trans hpre
  refine le_inf hNX ?_
  intro n hn k hk
  have hnS : n ∈ S := (hNX.trans ((omegaCenter_le _).trans (fun _ hx => hx.1))) hn
  have hh := hL (show (⟨k,(map_subtype_le _) hk⟩ : S) ∈
      (Ltilde R a).subgroupOf S from hk) ⟨n,hnS⟩ hn
  exact (congrArg Subtype.val hh).symm
end Detection

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R) (g : Geometry d.radical)
variable {a z : Vertex d.radical}
include h

/-- In the actual replacement graph, an opposite-kernel attachment in X
lies in its full fixed layer. The original input supplies every actor premise. -/
theorem replacement_critical_X_layer_le_fixed
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (N : Subgroup (FreeAmalgam d.radical)) (hNX : N ≤ X d.radical a)
    (hNQ : N ≤ Q d.radical z)
    (hn : stabilizer d.radical a ≤ normalizer N) :
    N ≤ X d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
  have hpos : 0 < criticalDistance d.radical a (g.exists_critical a path.start_color) := by
    rw [g.distance_constant a path.start_color]
    change 0 < g.b d.radical
    omega
  have hC := edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  have hzQ : ¬ Z d.radical z ≤ Q d.radical a :=
    (critical_reverse d.radical g hC a path.start_color hpos z path.end_color path.critical).2
  have hzS : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  obtain ⟨⟨E,hE,e,hcover,j,hj,hjU,κ,hκ,hk,hkC,him,hfaith,hsemi,hact,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.start_color
  let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
  let : (((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ).Normal := by
    rw [him]
    exact (replacement_component_image_structure h d).2.1
  let : IsSimpleGroup (((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ) := by
    rw [him]
    exact (replacement_component_image_structure h d).2.2.1
  let : IsQuasisimple C := (replacement_component_image_structure h d).2.2.2.1
  let : IsSimpleGroup C := (replacement_component_image_structure h d).2.2.1
  have hna : ¬ IsMulCommutative
      (((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ) := by
    rw [him]
    exact Group.IsPerfect.not_isMulCommutative C
  have hc : centralizer
      (((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ :
        Set (d.overgroup ⧸ pCore 2 d.overgroup)) = ⊥ := by
    rw [him]
    exact (replacement_component_image_structure h d).2.2.2.2
  exact normal_central_layer_le_fixed_of_opposite_kernel N hNX hNQ hn
    hzS hzQ path.end_color κ hκ hk hna hc

/-- The same detection applied to the actual moving subgroup, retaining its
full central attachment. -/
theorem replacement_critical_layer_le_fixed
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (N : Subgroup (FreeAmalgam d.radical)) (hNU : N ≤ U d.radical a)
    (hNQ : N ≤ Q d.radical z)
    (hn : stabilizer d.radical a ≤ normalizer N) :
    N ≤ U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
  have hNX : N ≤ X d.radical a := hNU.trans
    ((DistanceEight.U_le_Z d.radical a).trans (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]
      change 0 < g.b d.radical
      omega)))
  exact le_inf hNU ((replacement_critical_X_layer_le_fixed h d g path hb N hNX hNQ hn).trans
    inf_le_right)

section CoverKernel
variable {M : Type*} [Group M]

/-- A natural cover of the literal U layer, retaining its whole kernel and a
specified attachment in that kernel. -/
structure FixedLayerCover (T : Subgroup M) (a : Vertex T) (n : ℕ)
    (N : Subgroup (FreeAmalgam T)) [IsElementaryAbelian 2 (U T a)] where
  field : BinaryField
  degree : field.degree = n
  action : Representation (ZMod 2)
    (commutator (Matrix.symplecticGroup (Fin 2) field.Carrier)) (Additive (U T a))
  projection : action.IntertwiningMap (binaryNatural (K := field.Carrier))
  cover : IsCover projection
  actor : Ltilde T a →* commutator (Matrix.symplecticGroup (Fin 2) field.Carrier)
  onto : Function.Surjective actor
  conjugation : ∀ (k : Ltilde T a) (u : U T a),
    ((action (actor k) (Additive.ofMul u)).toMul : FreeAmalgam T) =
      (k : FreeAmalgam T) * u * (k : FreeAmalgam T)⁻¹
  kernel : projection.toLinearMap.ker.toAddSubgroup.toSubgroup'.map (U T a).subtype =
    U T a ⊓ centralizer (Ltilde T a : Set (FreeAmalgam T))
  attachment : N ≤ projection.toLinearMap.ker.toAddSubgroup.toSubgroup'.map (U T a).subtype

end CoverKernel

/-- The same attachment vanishes under the actual cover projection, while
its central kernel remains part of the intrinsic moving group. -/
theorem replacement_critical_layer_in_cover_kernel
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (N : Subgroup (FreeAmalgam d.radical)) (hNU : N ≤ U d.radical a)
    (hNQ : N ≤ Q d.radical z)
    (hn : stabilizer d.radical a ≤ normalizer N) :
    let := replacement_vertex_moving_elementary h d path.start_color
    Nonempty (FixedLayerCover d.radical a n N) := by
  let := replacement_vertex_moving_elementary h d path.start_color
  obtain ⟨E,hE,σ,p,hp,f,hf,hact,hker⟩ :=
    replacement_initial_subgroup_cover_at_vertex h d path.start_color
  exact ⟨⟨E,hE,σ,p,hp,f,hf,hact,hker,hker.symm ▸
    replacement_critical_layer_le_fixed h d g path hb N hNU hNQ hn⟩⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
