module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SharpImages
public import Theory.SpecificGroups.SymplecticFour.MaximalElementary

/-!
# Whole-kernel control by the secondary orbit

The sharp secondary image has order q cubed and is self-centralizing in
Sp₄(q). The full opposite-kernel image centralizes it, hence equals it.
This gives the literal factorization Q_a = A (Q_a ∩ Q_z) and equality of
their displacements on Z_z. Normal-section detection then places the entire
intrinsic core in A and identifies it with [A,Ltilde_a]. The secondary
quotient coordinates send this actual core onto the canonical moved space;
all kernel and fixed supplements remain explicit.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.6), printed p.871. This does not yet prove that A/Z_a is fully
moved, the paired-orbit contradiction, or the (3.7) field restriction.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

theorem replacement_kernel_image_eq_secondary
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    (E : BinaryField) (hE : E.degree = n)
    (f : Q d.radical a →* Sp E.Carrier)
    (hk : f.ker.map (Q d.radical a).subtype = Q d.radical a ⊓ Q d.radical z) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    f.range = (A.subgroupOf (Q d.radical a)).map f := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  have hAQ := (replacement_secondary_orbit_bounds h d path hb hat hzt hlarge).1
  let fA := f.comp (inclusion hAQ)
  have hAm : fA.range = (A.subgroupOf (Q d.radical a)).map f := by
    rw [MonoidHom.range_comp,inclusion_range]
  have hfk (x : Q d.radical a) : f x = 1 ↔ x.val ∈ Q d.radical z := by
    constructor
    · intro hx
      exact (hk ▸ mem_map_of_mem (Q d.radical a).subtype (show x ∈ f.ker from hx)).2
    · intro hx
      obtain ⟨y,hy,he⟩ := (hk.symm ▸ ⟨x.property,hx⟩ : x.val ∈ f.ker.map (Q d.radical a).subtype)
      exact (Subtype.ext he : y = x) ▸ hy
  obtain ⟨E',hE',β,hβk,hβe,hβc,_⟩ := replacement_secondary_image h d path hb hat hzt hlarge
  have hker : fA.ker = β.ker := by
    apply map_injective A.subtype_injective
    rw [hβk]
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.property,(hfk (inclusion hAQ u)).mp hu⟩
    · rintro ⟨ha,hz⟩
      exact ⟨⟨x,ha⟩,(hfk (inclusion hAQ ⟨x,ha⟩)).mpr hz,rfl⟩
  let e := (QuotientGroup.quotientKerEquivRange fA).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange β))
  let := hβe
  let : IsElementaryAbelian 2 fA.range :=
    IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hc : Nat.card fA.range = Nat.card E.Carrier^3 := by
    rw [Nat.card_congr e.toEquiv,hβc,(replacement_paired_secondary_orders h d path hb hat hzt hlarge).1,
      E.card_eq,hE]
  have hcomm : ⁅A,Q d.radical a⁆ ≤ Q d.radical z :=
    ((replacement_secondary_commutator_eq_seed h d path hb hat hzt hlarge).2.trans inf_le_left).trans
      ((Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt).trans
        ((g.omega_bound z path.end_color (by
          rw [g.distance_constant z path.end_color]
          change 0 < g.b d.radical
          omega)).trans (omegaCenter_le _)))
  have hcentral : f.range ≤ centralizer (fA.range : Set (Sp E.Carrier)) := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
    apply commutatorElement_eq_one_iff_mul_comm.mp
    change ⁅f (inclusion hAQ y),f x⁆ = 1
    rw [←map_commutatorElement]
    apply (hfk _).mpr
    exact hcomm (commutator_mem_commutator y.property x.property)
  change f.range = (A.subgroupOf (Q d.radical a)).map f
  rw [←hAm]
  exact le_antisymm (hcentral.trans
    (MaximalElementary.selfCentralizing (E.card_eq.trans (congrArg (2^·) hE)) h.nonbinary fA.range hc))
    (by rintro _ ⟨x,rfl⟩; exact ⟨inclusion hAQ x,rfl⟩)


theorem replacement_kernel_eq_secondary_sup_intersection
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    Q d.radical a = A ⊔ (Q d.radical a ⊓ Q d.radical z) := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  obtain ⟨E,hE,f,hk,_⟩ := replacement_nonfrattini_kernel_root_action h d path hb hlarge
  have him := replacement_kernel_image_eq_secondary h d path hb hat hzt hlarge E hE f hk
  have hcom := congrArg (Subgroup.comap f) him
  have hr : f.range.comap f = ⊤ := by
    ext x
    exact iff_of_true ⟨x,rfl⟩ (mem_top x)
  rw [hr,comap_map_eq] at hcom
  have hmap := congrArg (Subgroup.map (Q d.radical a).subtype) hcom
  rw [Subgroup.map_sup,hk,map_subgroupOf_eq_of_le
    (replacement_secondary_orbit_bounds h d path hb hat hzt hlarge).1] at hmap
  simpa only [←MonoidHom.range_eq_map,range_subtype] using hmap


private theorem secondary_core_detection
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (V W : Subgroup (FreeAmalgam d.radical))
    (hVS : V ≤ stabilizer d.radical a)
    (hVN : stabilizer d.radical a ≤ normalizer V)
    (hWN : stabilizer d.radical a ≤ normalizer W)
    (hcomm : ⁅V,Z d.radical z⁆ ≤ W) : ⁅V,Ltilde d.radical a⁆ ≤ W := by
  let S := stabilizer d.radical a
  let : Finite S := finite_stabilizer d.radical a
  let V₀ := V.subgroupOf S
  let W₀ := W.subgroupOf S
  let E₀ := (Z d.radical z).subgroupOf S
  let : V₀.Normal := normal_subgroupOf_of_le_normalizer hVN
  let : W₀.Normal := normal_subgroupOf_of_le_normalizer hWN
  have hzS : Z d.radical z ≤ S := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  have hzQ : ¬ Z d.radical z ≤ Q d.radical a :=
    (critical_reverse d.radical g
      (MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
        (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d))
      a path.start_color (by
        rw [g.distance_constant a path.start_color]
        change 0 < g.b d.radical
        omega)
      z path.end_color path.critical).2
  obtain ⟨⟨E,hE,e,hcover,j,hj,hjU,κ,hκ,hk,hkC,him,hfaith,hsemi,hact,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.start_color
  have hLm : (pResidual 2 S).map S.subtype = Ltilde d.radical a := rfl
  have hLi : (pResidual 2 S).map κ = replacementComponent d := by
    have he : (Ltilde d.radical a).subgroupOf S = pResidual 2 S := by
      change ((pResidual 2 S).map S.subtype).comap S.subtype = _
      exact comap_map_eq_self_of_injective S.subtype_injective _
    rwa [he] at him
  let : IsSimpleGroup ((pResidual 2 S).map κ) := by
    rw [hLi]
    exact (replacement_component_image_structure h d).2.2.1
  have hc : centralizer ((pResidual 2 S).map κ : Set (d.overgroup ⧸ pCore 2 d.overgroup)) = ⊥ := by
    rw [hLi]
    exact (replacement_component_image_structure h d).2.2.2.2
  have hkernel : IsPGroup 2 κ.ker := by
    have he : κ.ker = (Q d.radical a).subgroupOf S := by
      apply map_injective S.subtype_injective
      rw [hk,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
    rw [he]
    exact (Q_isPGroup d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) a path.start_color).comap_subtype
  have hescape : ¬ E₀ ≤ κ.ker := by
    intro hh
    apply hzQ
    intro x hx
    exact hk ▸ mem_map_of_mem S.subtype (hh (show (⟨x,hzS hx⟩ : S) ∈ E₀ from hx))
  have hVm : V₀.map S.subtype = V := map_subgroupOf_eq_of_le hVS
  have hEm : E₀.map S.subtype = Z d.radical z := map_subgroupOf_eq_of_le hzS
  have hm : ⁅V₀,E₀⁆ ≤ W₀ := by
    apply map_le_iff_le_comap.mp
    simpa only [map_commutator,hVm,hEm] using hcomm
  have hh := map_mono (f := S.subtype)
    (commutator_pResidual_le_of_monolithic_kernel_escape 2 κ hκ hkernel hc V₀ W₀ E₀ hescape hm)
  rw [map_commutator,hLm,map_subgroupOf_eq_of_le hVS] at hh
  exact hh.trans (map_comap_le _ _)


/-- The full opposite-kernel displacement is already supplied by the secondary
orbit; the remaining literal kernel intersection centralizes the opposite Z. -/
theorem replacement_kernel_displacement_eq_secondary
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    ⁅Q d.radical a,Z d.radical z⁆ = ⁅A,Z d.radical z⁆ := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  have hAQ := (replacement_secondary_orbit_bounds h d path hb hat hzt hlarge).1
  have hAS := hAQ.trans (Q_le_stabilizer_of_dist_two d.radical a z path.start_color
    (path.critical.1.trans ((g.distance_constant a path.start_color).trans hb)))
  have hcover : Q d.radical a ≤ A ⊔ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) := by
    rw [replacement_kernel_eq_secondary_sup_intersection h d path hb hat hzt hlarge]
    exact sup_le_sup_left (inf_le_right.trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical z path.end_color)))) A
  apply le_antisymm
  · rw [commutator_comm (Q d.radical a),commutator_comm A]
    exact commutator_le_moving_of_inner_mod_centralizer _ A _
      (hAS.trans (Z_normalized d.radical z)) hcover
  · exact commutator_mono hAQ le_rfl

/-- The actual whole commutator core lies in the secondary orbit. This follows
from its full displacement, not from movement of a quotient alone. -/
theorem replacement_core_le_secondary_orbit
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    core d.radical a ≤
      Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z) := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  have hzS : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  apply secondary_core_detection h d path hb (Q d.radical a) A
    (fun _ hx => hx.1) (Q_normalized d.radical a) (conjugatesIn_normalized _ _)
  rw [replacement_kernel_displacement_eq_secondary h d path hb hat hzt hlarge]
  exact le_normalizer_iff_commutator_le_left.mp
    (hzS.trans (conjugatesIn_normalized _ _))

/-- The secondary orbit's component commutator is precisely the whole intrinsic
graph core, with every central attachment retained. -/
theorem replacement_secondary_component_commutator_eq_core
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    ⁅A,Ltilde d.radical a⁆ = core d.radical a := by
  let S := stabilizer d.radical a
  let : Finite S := finite_stabilizer d.radical a
  have hQ : Q d.radical a ≤ S := fun _ hx => hx.1
  have hLm : (pResidual 2 S).map S.subtype = Ltilde d.radical a := rfl
  have hQm : ((Q d.radical a).subgroupOf S).map S.subtype = Q d.radical a :=
    map_subgroupOf_eq_of_le hQ
  let : ((Q d.radical a).subgroupOf S).Normal := Q_normal d.radical a
  have hid := congrArg (Subgroup.map S.subtype)
    (commutator_isPPerfect_idempotent (pResidual 2 S) ((Q d.radical a).subgroupOf S)
      (isPPerfect_pResidual 2)
      (Q_isPGroup d.radical (replacement_isPGroup h d) (replacement_core_le h d)
        a path.start_color).comap_subtype le_normalizer_of_normal)
  have hid' : ⁅core d.radical a,Ltilde d.radical a⁆ = core d.radical a := by
    simpa only [core,map_commutator,hLm,hQm] using hid
  apply le_antisymm
  · exact commutator_mono (replacement_secondary_orbit_bounds h d path hb hat hzt hlarge).1 le_rfl
  · rw [←hid']
    exact commutator_mono (replacement_core_le_secondary_orbit h d path hb hat hzt hlarge) le_rfl


/-- The full secondary orbit is the actual core times its opposite-kernel
intersection and Z. This states exactly the retained supplement. -/
theorem replacement_secondary_core_supplement
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    A = core d.radical a ⊔ ((A ⊓ Q d.radical z) ⊔ Z d.radical a) := by
  have he := replacement_secondary_moved_kernel_supplement h d path hb hat hzt hlarge
  dsimp only at he ⊢
  rwa [replacement_secondary_component_commutator_eq_core h d path hb hat hzt hlarge] at he

/-- Under the original secondary coordinates, the actual intrinsic core maps
onto exactly the canonical moved space at the original field degree. -/
theorem replacement_core_secondary_image
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (κ : stabilizer d.radical a →* (d.overgroup ⧸ pCore 2 d.overgroup))
    (hL : ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ =
      replacementComponent d)
    (σ : Representation (ZMod 2) (d.overgroup ⧸ pCore 2 d.overgroup) V)
    (c : BinaryConjugationSection (stabilizer d.radical a)
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z))
      (Z d.radical a) (σ.comp κ)) :
    let := replacementComponent_normal h d
    c.imageSpace (core d.radical a) =
      (MovedSection.ofNormal σ (replacementComponent d)).space.toSubmodule := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let := replacementComponent_normal h d
  let s := MovedSection.ofNormal σ (replacementComponent d)
  have him : c.imageSpace A = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨u,hu⟩ := c.onto (Multiplicative.ofAdd v)
    exact (c.mem_imageSpace_iff A v).mpr ⟨u,u.property,congrArg Multiplicative.toAdd hu⟩
  rw [←replacement_secondary_component_commutator_eq_core h d path hb hat hzt hlarge,
    commutator_comm,c.imageSpace_commutator _ _ (Ltilde_le_stabilizer a) le_rfl,
    him,BinaryOffender.subspaceCommutator_comp_map,hL]
  exact s.space_eq.symm

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
