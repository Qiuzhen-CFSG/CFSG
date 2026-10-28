module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.StarDualCover
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SecondaryPlane
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StarCut
public import Theory.Representation.SymplecticFourOrthogonalCover.DualFixed

/-!
# Inner edge action on the characteristic replacement

The star centralizes the critical endpoint. Dual-cover fixedness therefore
puts its image in the moving natural submodule. Lifting through the literal
kernel gives the second star inclusion with the entire fixed core retained.
The characteristic cut proves M=M* at every positive critical distance.

At distance two this puts the whole common edge inside the opposite component
and two-core. The marked-plane argument now proves nontrivial component action
on the actual secondary quotient, with no extra inner-edge premise.
The paired-orbit contradiction and the field restriction remain separate.
Source: MS93 (3.4) and (3.6), printed pp.869--871.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The second source star bound, for the actual minimum replacement at
arbitrary nonbinary degree. The entire fixed core is retained. -/
theorem replacement_starSpan_le_moving_fixed
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical))) :
    (starSpan d.radical Y).map (embedS d.radical) ≤
      U d.radical (alpha d.radical) ⊔ fixedCore d.radical (alpha d.radical) := by
  obtain ⟨E,hE,s,γ,hγ,hγC,hmap,i,hi,hdual,hrange,hcritical⟩ :=
    replacement_sourceStarDualCover h d geometry hb Y P hY hn
  obtain ⟨z,path,hfirst⟩ := exists_replacement_critical_path_through_beta d geometry (by omega)
  obtain ⟨β,hβ,hno⟩ := hcritical z path
  have hc := h.replacement_starSpan_centralizes_endpoint d geometry (by omega)
    path hfirst Y P hY hn
  have hBA : (starSpan d.radical Y).map (embedS d.radical) ≤ sourceStarAlpha d.radical Y := by
    have hh := (sourceStarAlpha_le_iff d.radical Y (sourceStarAlpha d.radical Y)).mp
      le_rfl (1 : Mbar d.radical)
    have he : (MulAut.conj (1 : FreeAmalgam d.radical)).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change 1*x*1⁻¹=x
      simp
    simpa only [OneMemClass.coe_one,he,Subgroup.map_id] using hh
  have hZS : Z d.radical z ≤ stabilizer d.radical (alpha d.radical) := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant _ rfl,
      geometry.distance_constant _ path.end_color]
  intro b hbB
  let bA : sourceStarAlpha d.radical Y := ⟨b,hBA hbB⟩
  have hfix : (s.sectionData.coordinates bA).toAdd ∈
      OneCohomology.fixed ((s.action.comp γ).comp β.range.subtype) := by
    rintro ⟨a,⟨x,rfl⟩⟩
    change s.action (γ (β x)) (s.sectionData.coordinates bA).toAdd = _
    rw [hβ x (hZS x.property)]
    have he := s.sectionData.equivariant ⟨x,hZS x.property⟩ bA
    change (s.sectionData.coordinates ⟨(x : FreeAmalgam d.radical)*b*
      (x : FreeAmalgam d.radical)⁻¹,_⟩).toAdd =
        s.action (s.quotient ⟨x,hZS x.property⟩) (s.sectionData.coordinates bA).toAdd at he
    rw [←he]
    congr 2
    apply Subtype.ext
    have hcomm := hc hbB x x.property
    exact (congrArg (fun t => t*(x : FreeAmalgam d.radical)⁻¹) hcomm).trans
      (mul_inv_cancel_right b (x : FreeAmalgam d.radical))
  have hmem := dualCover_fixed_le_natural_of_no_refinement i hi hdual β.range hno hfix
  obtain ⟨u,hu,he⟩ := (hrange _).mp hmem
  have hdiff : (u⁻¹*bA : sourceStarAlpha d.radical Y) ∈ s.sectionData.coordinates.ker := by
    change s.sectionData.coordinates (u⁻¹*bA) = 1
    rw [map_mul,map_inv,show s.sectionData.coordinates u = s.sectionData.coordinates bA
      from Multiplicative.toAdd.injective he,inv_mul_cancel]
  rw [s.sectionData.kernel_eq] at hdiff
  have hd : ((u⁻¹*bA : sourceStarAlpha d.radical Y) : FreeAmalgam d.radical) ∈
      fixedCore d.radical (alpha d.radical) := hdiff.2
  have hmul := mul_mem (mem_sup_left hu) (mem_sup_right hd)
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_cancel_left] using hmul

/-- The two proved star bounds remove all outer action in the positive-distance
branch, on the same characteristic replacement. -/
theorem replacement_inner_of_positive
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical) :
    K.subgroupOf d.overgroup ⊔ pCore 2 d.overgroup = ⊤ := by
  obtain ⟨P,Y,hY,hn,_,_⟩ := h.exists_replacement_source_seed d
  apply h.replacement_inner_of_seed_star_inclusion d P Y hY
  simpa only [Subgroup.map_map,embedM_comp_subtype] using
    replacement_starSpan_le_moving_fixed h d geometry hb Y P hY hn


/-- Positive-distance star control gives the full inner action of the edge at
the opposite endpoint, with the original residual and two-core embeddings. -/
theorem replacement_inner_edge
    {g : Geometry d.radical} {z t : Vertex d.radical}
    (hb : 0 < g.b d.radical) (hz : color d.radical z = false)
    (hzt : Adjacent d.radical z t) :
    Q d.radical t ≤ Ltilde d.radical z ⊔ Q d.radical z :=
  replacement_inner_edge_of_component_core h d hz hzt
    (replacement_inner_of_positive h d g hb)

/-- At distance two, the component acts nontrivially on the secondary quotient
in the non-Frattini branch. No inner-edge or marked-plane premise remains. -/
theorem replacement_secondary_moves
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    ¬ ⁅Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z),
      Ltilde d.radical a⁆ ≤ Z d.radical a :=
  replacement_secondary_moves_of_inner_edge h d path hb hat hzt hlarge
    (replacement_inner_edge h d (g := g) (by omega) path.end_color hzt)

/-- The literal secondary quotient has nontrivial component action, quadratic
opposite action and fixed codimension at most twice the original field degree.
The characteristic cut discharges the full inner-edge premise. -/
theorem replacement_secondary_section_nontrivial
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
    let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
    ∃ (κ : stabilizer d.radical a →* (d.overgroup ⧸ pCore 2 d.overgroup)),
      Function.Surjective κ ∧
      κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
      ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ =
        replacementComponent d ∧
      ∃ (σ : Representation (ZMod 2) (d.overgroup ⧸ pCore 2 d.overgroup)
          (Additive (A ⧸ (Z d.radical a).subgroupOf A)))
        (c : BinaryConjugationSection (stabilizer d.radical a) A (Z d.radical a) (σ.comp κ)),
        (∀ u : A, (c.coordinates u).toAdd =
          Additive.ofMul (QuotientGroup.mk' ((Z d.radical a).subgroupOf A) u)) ∧
        Representation.BinaryOffender.IsQuadratic σ
          ((A'.subgroupOf (stabilizer d.radical a)).map κ) ∧
        Representation.BinaryOffender.fixedCodim σ
          ((A'.subgroupOf (stabilizer d.radical a)).map κ) ≤ 2*n ∧
        ∃ b : replacementComponent d, ∃ v, σ b.val v ≠ v := by
  exact replacement_secondary_section_of_inner_edge h d path hb hat hzt hlarge
    (replacement_inner_edge_of_component_core h d path.end_color hzt
      (replacement_inner_of_positive h d g (by omega)))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
