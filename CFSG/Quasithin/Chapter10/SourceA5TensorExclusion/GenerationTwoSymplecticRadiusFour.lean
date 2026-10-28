module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticDistanceBound
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.RadiusFour
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank

/-!
# The full original radius at distance four

The literal natural action sends every original radius to an elementary
symplectic subgroup. Its image has order at most 64, including the distance-four
boundary. The entire derived radius lies in each nearby full kernel and hence
centralizes the radius. At the actual midpoint of a critical path, the critical
commutator is a nontrivial central subgroup of that derived radius.

The original radius order bound now makes the full penultimate kernel have at
least 1024 elements, so it cannot lie in the order-256 starting seed. All maps,
kernels and vertices are those of the original overgroup. These results do not
identify X with Z or assert that [V_a,Q_a] centralizes V_a. That stronger source
claim, the terminal distance-four exclusion and original plane recognition
remain with the tensor symplectic owner.

Source: Meierfrankenfeld--Stellmacher (1993), (5.2) and (5.12), pp.914--915,
924--927; Aschbacher--Smith 9.3.10 and its concluding paragraph, pp.734--735.
-/

open scoped commutatorElement IsMulCommutative
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

/-- Every radius image in range has order at most 64, also when b = 4. -/
theorem original_radius_image_index_le_64_at_four
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R}, color R a = false → color R z = false →
      (cosetGraph R).dist a z + 2 ≤ geometry.b R →
      (Q R z).relIndex (V R a) ≤ 64 ∧ ⁅V R a,V R a⁆ ≤ Q R z := by
  intro R geometry a z ha hz hd
  obtain ⟨F,hF,f,hf,π,hact⟩ := c.original_radius_natural_action eK geometry ha hz hd
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hFc : Nat.card F.Carrier = 2^2 := by rw [F.card_eq,hF]
  let he := radius_image_elementary_of_natural_action hFc (by decide)
    (lt_of_lt_of_le (by decide : 2 < 4) (c.original_geometry_four_le eK geometry))
    (Q_isPGroup R hodd.isPGroup hodd.twoCore_le a ha) ha hd f hf
    π.toMonoidHom π.surjective hact
  let := he
  have hr := EvenTwoRank.rank hFc (by decide : 0 < 2)
  have hc := (primeRank_le_iff_elementary_card_le (Sp F.Carrier)).mp hr.le f.range inferInstance
  refine ⟨?_,?_⟩
  · change ((Q R z).subgroupOf (V R a)).index ≤ 64
    rw [←hf,index_ker]
    exact hc
  · apply commutator_le.mpr
    intro x hx y hy
    let xx : V R a := ⟨x,hx⟩
    let yy : V R a := ⟨y,hy⟩
    have hcomm : f xx*f yy=f yy*f xx := by
      exact congrArg Subtype.val (mul_comm (f.rangeRestrict xx) (f.rangeRestrict yy))
    have hk : ⁅xx,yy⁆ ∈ f.ker := by
      change f ⁅xx,yy⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
    rw [hf] at hk
    exact hk

/-- The whole original radius is of nilpotence class at most two at distance four.
This centralizes its derived subgroup, without identifying X with Z. -/
theorem original_radius_derived_central
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (_geometry : Geometry R) (a : Vertex R), color R a = false →
      ⁅V R a,V R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
  intro R geometry a ha
  apply le_centralizer_iff.mp
  apply (V_le_iff R ha _).mpr
  intro z hz hza
  have hd : (cosetGraph R).dist a z + 2 ≤ geometry.b R := by
    rw [SimpleGraph.dist_comm]
    have hh := c.original_geometry_four_le eK geometry
    change 4 ≤ geometry.b R at hh
    omega
  have hk := (c.original_radius_image_index_le_64_at_four eK geometry ha hz hd).2
  exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z hz)).trans
    (centralizer_le hk)

/-- The full penultimate kernel has at least 1024 elements at distance four. -/
theorem original_truncated_radius_kernel_card_ge_1024_at_four
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (path : CriticalPath R geometry a z),
      1024 ≤ Nat.card (V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)) :
        Subgroup (FreeAmalgam R)) := by
  intro R geometry a z path
  have hb := c.original_geometry_eq_four eK geometry
  change geometry.b R = 4 at hb
  have hl : path.walk.length = 4 := path.length_eq_b.trans hb
  have hw : color R (path.walk.getVert (path.walk.length-2)) = false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    rw [hl]
    decide
  have hd : (cosetGraph R).dist a (path.walk.getVert (path.walk.length-2)) + 2 ≤ geometry.b R := by
    rw [path.dist_start (Nat.sub_le _ _),hl,hb]
  have hi := (c.original_radius_image_index_le_64_at_four eK geometry path.start_color hw hd).1
  have hc := c.original_radius_card_ge_65536 eK geometry a path.start_color
  have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (V R a ⊓ Q R (path.walk.getVert (path.walk.length-2))) (V R a) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left] at hm
  change (Q R (path.walk.getVert (path.walk.length-2))).relIndex (V R a) ≤ 64 at hi
  change 65536 ≤ Nat.card (V R a) at hc
  nlinarith

/-- At the literal midpoint of a critical path, the critical commutator is a
nontrivial central subgroup of the full radius. Thus the distance-four
argument must retain the nonabelian radius. -/
theorem original_midpoint_radius_nonabelian
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (path : CriticalPath R geometry a z),
      ⁅Z R a,Z R z⁆ ≠ ⊥ ∧
      ⁅Z R a,Z R z⁆ ≤ ⁅V R (path.walk.getVert 2),V R (path.walk.getVert 2)⁆ ∧
      ⁅Z R a,Z R z⁆ ≤ centralizer (V R (path.walk.getVert 2) : Set (FreeAmalgam R)) := by
  intro R geometry a z path
  have hb := c.original_geometry_eq_four eK geometry
  change geometry.b R = 4 at hb
  have hl : path.walk.length = 4 := path.length_eq_b.trans hb
  have hd : color R (path.walk.getVert 2) = false :=
    (path.vertex_color (by omega)).mpr (by decide)
  have haV : Z R a ≤ V R (path.walk.getVert 2) := by
    have hdist : (cosetGraph R).dist a (path.walk.getVert 2) ≤ 2 := by
      rw [path.dist_start (by omega)]
    exact le_iSup_of_le a (le_iSup_of_le hdist le_rfl)
  have hzV : Z R z ≤ V R (path.walk.getVert 2) := by
    have hdist : (cosetGraph R).dist z (path.walk.getVert 2) ≤ 2 := by
      rw [SimpleGraph.dist_comm,path.dist_end,hl]
    exact le_iSup_of_le z (le_iSup_of_le hdist le_rfl)
  have hroot := commutator_mono haV hzV
  refine ⟨?_,hroot,hroot.trans (c.original_radius_derived_central eK geometry _ hd)⟩
  intro hzero
  have hc := commutator_eq_bot_iff_le_centralizer.mp hzero
  have hk := c.original_critical_seed_kernel_eq_centralizer eK geometry path
  have hle : Z R a ≤ Q R z := by
    rw [inf_eq_left.mpr hc] at hk
    exact hk ▸ inf_le_right
  exact path.critical.2 hle

/-- The penultimate full kernel is strictly larger than the original seed,
also in the terminal distance-four case. -/
theorem original_truncated_radius_kernel_not_le_Z_at_four
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (path : CriticalPath R geometry a z),
      ¬ V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)) ≤ Z R a := by
  intro R geometry a z path hle
  let := finite_Z R a
  have hc := c.original_truncated_radius_kernel_card_ge_1024_at_four eK geometry path
  have hbound := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  have hZ := c.original_Z_card eK a path.start_color
  change Nat.card (Z R a) = 256 at hZ
  rw [hZ] at hbound
  change 1024 ≤ Nat.card (V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)) :
    Subgroup (FreeAmalgam R)) at hc
  omega

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
