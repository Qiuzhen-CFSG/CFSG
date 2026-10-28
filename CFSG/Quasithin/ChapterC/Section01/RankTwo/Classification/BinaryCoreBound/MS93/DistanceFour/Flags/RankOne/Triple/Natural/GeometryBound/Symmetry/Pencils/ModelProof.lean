module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Symmetry.Pencils.Intersections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.DualGeometry.ModelProof.Standard
/-!
# Three-core selection in the binary projective plane

Two different incident-core intersections yield point-parabolic representatives
whose relative actor is outside the line parabolic. Moving each representative
by the standard cubic line actor gives the required neighbors. The first two
point cores contain a conjugate Borel; one transvection in the third core
escapes both parabolics containing that Borel, so the three cores generate SL₃(2).
The finite certificates check only explicit matrices and words of length two.

The inner-or-graph description of an arbitrary marking reduces fixed-space
inequality to the known distinct lines or distinct planes. An automorphism
mapping the standard incident pair to the prescribed pair then transports
incidence, intrinsic cores, and generation together, including the dual case.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the selection in the proof of (4.6.8), printed p.905.
-/

open Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Pencils
private abbrev G := Matrix.PSL3Two.SL
private abbrev C {X : Type*} [Group X] (P : Subgroup X) (g : X) := P.map (MulAut.conj g).toMonoidHom
private theorem conj_mul {X : Type*} [Group X] (P : Subgroup X) (g h : X) : C P (g*h) = C (C P h) g := by
  unfold C
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
  group
private theorem map_conj {X : Type*} [Group X] (P : Subgroup X) (g : X) (α : MulAut X) :
    (C P g).map α.toMonoidHom = C (P.map α.toMonoidHom) (α g) := by
  unfold C
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
private theorem map_aut_mul {X : Type*} [Group X] (P : Subgroup X) (α β : MulAut X) :
    P.map (α*β).toMonoidHom = (P.map β.toMonoidHom).map α.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl
private theorem core_normalized (P : Subgroup G) (g : G) (hg : g ∈ P) : C (P.pCoreIn 2) g = P.pCoreIn 2 := by
  exact mem_normalizer_iff_map_conj_eq.mp
    ((P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))) hg)
private theorem point_normalized (g : G) (hg : g ∈ pointParabolicSL) : C pointV g = pointV := by
  rw [← MarkedProduct.pointParabolic_core]
  exact core_normalized _ _ hg
private theorem line_core : lineParabolicSL.pCoreIn 2 = lineV := by
  rw [← pointParabolic_map_diagram, ← map_pCoreIn_of_injective 2 _ _ diagram.injective,
    MarkedProduct.pointParabolic_core, pointV_map_diagram]
private theorem lineV_R : lineV = BinaryLinearThree.R := by
  rw [← line_core, lineParabolicSL_pCoreIn_two_eq_R]
private theorem cycle_fixed_ne (σ : MulAut G) :
    fixedSpace ((C pointV lineCycle).map σ.toMonoidHom) ≠ fixedSpace (pointV.map σ.toMonoidHom) := by
  obtain ⟨k,hk|hk⟩ := inner_or_graph σ
  · simp only [hk, C, fixedSpace_conj, fixed_pointCore]
    intro he
    have hh := Subgroup.map_injective (f := (vectorAction k).toMonoidHom) (vectorAction k).injective he
    have hz := line_neighbors.1
    rw [hh, inf_idem] at hz
    have hc := line_card
    rw [hz, card_bot] at hc
    omega
  · rw [hk, map_aut_mul, map_aut_mul, fixedSpace_conj, fixedSpace_conj]
    intro he
    have hh := Subgroup.map_injective (f := (vectorAction k).toMonoidHom) (vectorAction k).injective he
    rw [map_conj, pointV_map_diagram, lineV_R, fixedSpace_conj, fixed_lineCore,
      RankOnePairing.Incidence.DualGeometry.ModelProof.diagram_c] at hh
    have hz := RankOnePairing.Incidence.DualGeometry.ModelProof.opposite_one
    rw [hh, sup_idem] at hz
    exact plane_ne_top hz
private theorem moved_fixed_ne (σ : MulAut G) (a : G) (ha : a ∈ pointParabolicSL) :
    fixedSpace ((C pointV (a*lineCycle)).map σ.toMonoidHom) ≠ fixedSpace (pointV.map σ.toMonoidHom) := by
  have hh := cycle_fixed_ne (σ * MulAut.conj a)
  rw [map_aut_mul, map_aut_mul] at hh
  change fixedSpace ((C (C pointV lineCycle) a).map σ.toMonoidHom) ≠
    fixedSpace ((C pointV a).map σ.toMonoidHom) at hh
  rw [← conj_mul, point_normalized a ha] at hh
  exact hh
private def r : G := lineCycle
private def vgens : Fin 4 → G := ![1, Bruhat.upper 1, Bruhat.upper 2, Bruhat.upper 1 * Bruhat.upper 2]
private theorem vgen_mem : ∀ j : Fin 4, vgens j ∈ pointV := by decide +kernel
private def gens (j : Fin 8) : G := if h : j.val < 4 then vgens ⟨j.val, h⟩ else (MulAut.conj r) (vgens ⟨j.val-4, by omega⟩)
private def word (w : Fin 2 → Fin 8) : G := gens (w 0) * gens (w 1)
private theorem borel_cert (i : Fin 8) : ∃ w : Fin 2 → Fin 8, word w = (MulAut.conj r) (Bruhat.upper i) := by decide +kernel +revert
private theorem borel_cases (x : G) (hx : x ∈ borelSL) : ∃ i : Fin 8, x = Bruhat.upper i := by decide +kernel +revert
private theorem escape (b : {x : G // x ∈ pointParabolicSL})
    (h : b.val ∉ lineParabolicSL) : ∃ j : Fin 4,
      (MulAut.conj r⁻¹) ((MulAut.conj (b.val*r)) (vgens j)) ∉ pointParabolicSL ∧
      (MulAut.conj r⁻¹) ((MulAut.conj (b.val*r)) (vgens j)) ∉ lineParabolicSL := by
  refine ⟨2, ?_⟩
  revert b h
  decide +kernel
-- After conjugating back by the cubic actor, use the Borel overgroup theorem.
private theorem std_point (b : {x : G // x ∈ pointParabolicSL})
    (h : b.val ∉ lineParabolicSL) :
    ((pointV ⊔ pointV.map (MulAut.conj r).toMonoidHom) ⊔
      pointV.map (MulAut.conj (b.val*r)).toMonoidHom) = ⊤ := by
  let H : Subgroup G := ((pointV ⊔ pointV.map (MulAut.conj r).toMonoidHom) ⊔
      pointV.map (MulAut.conj (b.val*r)).toMonoidHom)
  let H' := H.map (MulAut.conj r⁻¹).toMonoidHom
  have hB : borelSL ≤ H' := by
    intro x hx
    obtain ⟨i, rfl⟩ := borel_cases x hx
    obtain ⟨w, hw⟩ := borel_cert i
    have hgen (j : Fin 8) : gens j ∈ H := by
      by_cases hj : j.val < 4
      · simp only [gens, dif_pos hj]
        exact mem_sup_left (mem_sup_left (vgen_mem _))
      · simp only [gens, dif_neg hj]
        exact mem_sup_left (mem_sup_right (mem_map_of_mem _ (vgen_mem _)))
    have hwmem : word w ∈ H := by
      simpa only [word] using H.mul_mem (hgen (w 0)) (hgen (w 1))
    refine ⟨word w, hwmem, ?_⟩
    rw [hw]
    change r⁻¹ * (r * Bruhat.upper i * r⁻¹) * (r⁻¹)⁻¹ = Bruhat.upper i
    group
  obtain ⟨j, hjp, hjl⟩ := escape b h
  have he : (MulAut.conj r⁻¹) ((MulAut.conj (b.val*r)) (vgens j)) ∈ H' := by
    apply mem_map_of_mem
    exact mem_sup_right (mem_map_of_mem _ (vgen_mem _))
  have hnp : ¬ H' ≤ pointParabolicSL := by
    intro hh
    exact hjp (hh he)
  have hnl : ¬ H' ≤ lineParabolicSL := by
    intro hh
    exact hjl (hh he)
  have htop' : H' = ⊤ := by
    by_contra hn
    rcases overgroup_borelSL H' hB hn with hp | hl
    · exact hnp hp
    · exact hnl hl
  have hmap : H.map (MulAut.conj r⁻¹).toMonoidHom = ⊤ := by
    change H' = ⊤
    exact htop'
  apply (Subgroup.map_injective (f := (MulAut.conj r⁻¹).toMonoidHom) (MulAut.conj r⁻¹).injective)
  simpa only [H, Subgroup.map_top_of_surjective (MulAut.conj r⁻¹).toMonoidHom (MulAut.conj r⁻¹).surjective] using hmap
private theorem line_normalized (g : G) (hg : g ∈ lineParabolicSL) : C lineV g = lineV := by
  rw [← line_core]
  exact core_normalized _ _ hg

private theorem point_selection (σ : MulAut G) (a a' : G)
    (ha : a ∈ pointParabolicSL) (ha' : a' ∈ pointParabolicSL)
    (hne : pointV ⊓ C lineV a ≠ pointV ⊓ C lineV a') :
    ∃ g g' : G, a⁻¹*g ∈ lineParabolicSL ∧ a'⁻¹*g' ∈ lineParabolicSL ∧
      fixedSpace ((C pointV g).map σ.toMonoidHom) ≠ fixedSpace (pointV.map σ.toMonoidHom) ∧
      fixedSpace ((C pointV g').map σ.toMonoidHom) ≠ fixedSpace (pointV.map σ.toMonoidHom) ∧
      (pointV ⊔ C pointV g) ⊔ C pointV g' = ⊤ := by
  have hb : a⁻¹*a' ∈ pointParabolicSL := mul_mem (inv_mem ha) ha'
  -- A relative actor in the line parabolic would preserve the opposite core.
  have hn : a⁻¹*a' ∉ lineParabolicSL := by
    intro h
    apply hne
    conv_rhs => rw [show a' = a*(a⁻¹*a') by group, conj_mul, line_normalized _ h]
  refine ⟨a*lineCycle, a'*lineCycle, ?_, ?_, moved_fixed_ne σ a ha,
    moved_fixed_ne σ a' ha', ?_⟩
  · simpa only [inv_mul_cancel_left] using lineCycle_mem
  · simpa only [inv_mul_cancel_left] using lineCycle_mem
  have hh := congrArg (Subgroup.map (MulAut.conj a).toMonoidHom) (std_point ⟨a⁻¹*a',hb⟩ hn)
  simp only [Subgroup.map_sup, Subgroup.map_top_of_surjective (MulAut.conj a).toMonoidHom (MulAut.conj a).surjective] at hh
  change (C pointV a ⊔ C (C pointV lineCycle) a) ⊔ C (C pointV ((a⁻¹*a')*lineCycle)) a = ⊤ at hh
  rw [point_normalized a ha, ← conj_mul, ← conj_mul] at hh
  simpa only [mul_inv_cancel_left, mul_assoc] using hh

private theorem mapped_core (t : G) (i : Bool) (e : MulAut G) (P : Subgroup G)
    (he : P.map e.toMonoidHom = modelParabolic t i) (g : G) :
    matrixCore t i (e g) = (C (P.pCoreIn 2) g).map e.toMonoidHom := by
  unfold matrixCore
  rw [← he, ← map_pCoreIn_of_injective 2 _ _ e.injective]
  exact (map_conj (P.pCoreIn 2) g e).symm

private theorem mapped_base (t : G) (i : Bool) (e : MulAut G) (P : Subgroup G)
    (he : P.map e.toMonoidHom = modelParabolic t i) :
    matrixCore t i 1 = (P.pCoreIn 2).map e.toMonoidHom := by
  rw [matrixCore_one, ← he, ← map_pCoreIn_of_injective 2 _ _ e.injective]

private theorem mapping (t : G) (i : Bool) : ∃ e : MulAut G,
    pointParabolicSL.map e.toMonoidHom = modelParabolic t i ∧
    lineParabolicSL.map e.toMonoidHom = modelParabolic t (!i) := by
  cases i
  · exact ⟨MulAut.conj t, rfl, rfl⟩
  · refine ⟨MulAut.conj t * diagram, ?_, ?_⟩
    · rw [map_aut_mul, pointParabolic_map_diagram]
      rfl
    · have hl : lineParabolicSL.map diagram.toMonoidHom = pointParabolicSL := by
        ext x
        constructor
        · rintro ⟨x,hx,rfl⟩
          exact (RankOnePairing.Incidence.DualGeometry.ModelProof.diagram_line x).mpr hx
        · intro hx
          exact ⟨diagram x, (diagram_point_line x).mpr hx, diagram_involutive x⟩
      rw [map_aut_mul, hl]
      rfl

/-- The literal three-core pencil selection, for either color and every
marking of the natural binary three-space. -/
public theorem matrixSeparation (σ : MulAut SL) (t : SL) (i : Bool) :
    MatrixSeparation σ t i := by
  obtain ⟨e,hP,hQ⟩ := mapping t i
  constructor
  intro d d' hd hd' hne
  obtain ⟨m,hm,hdm⟩ := hd
  obtain ⟨m',hm',hdm'⟩ := hd'
  simp only [inv_one, one_mul] at hm hm'
  obtain ⟨a,rfl⟩ := e.surjective m
  obtain ⟨a',rfl⟩ := e.surjective m'
  have ha : a ∈ pointParabolicSL :=
    (mem_map_iff_mem e.injective).mp (hP.symm ▸ hm)
  have ha' : a' ∈ pointParabolicSL :=
    (mem_map_iff_mem e.injective).mp (hP.symm ▸ hm')
  have hdcore : matrixCore t (!i) (e a) = matrixCore t (!i) d := by
    simpa only [mul_inv_cancel_left] using matrixCore_right_mul t (!i) d (d⁻¹*e a) hdm
  have hdcore' : matrixCore t (!i) (e a') = matrixCore t (!i) d' := by
    simpa only [mul_inv_cancel_left] using matrixCore_right_mul t (!i) d' (d'⁻¹*e a') hdm'
  have hp (g : G) : matrixCore t i (e g) = (C pointV g).map e.toMonoidHom := by
    rw [mapped_core t i e _ hP, MarkedProduct.pointParabolic_core]
  have hp1 : matrixCore t i 1 = pointV.map e.toMonoidHom := by
    rw [mapped_base t i e _ hP, MarkedProduct.pointParabolic_core]
  have hq (g : G) : matrixCore t (!i) (e g) = (C lineV g).map e.toMonoidHom := by
    rw [mapped_core t (!i) e _ hQ, line_core]
  have hneq : pointV ⊓ C lineV a ≠ pointV ⊓ C lineV a' := by
    intro heq
    apply hne
    rw [← hdcore, ← hdcore', hp1, hq, hq,
      ← map_inf _ _ _ e.injective, ← map_inf _ _ _ e.injective, heq]
  obtain ⟨g,g',hg,hg',hf,hf',htop⟩ := point_selection (σ*e) a a' ha ha' hneq
  refine ⟨e g, e g', ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨e g, ?_, ?_⟩
    · simp only [inv_mul_cancel, one_mem]
    · have hh : e (a⁻¹*g) ∈ modelParabolic t (!i) := hQ ▸ mem_map_of_mem _ hg
      have heq : d⁻¹*e g = (d⁻¹*e a)*e (a⁻¹*g) := by
        rw [map_mul, map_inv]
        group
      rw [heq]
      exact mul_mem hdm hh
  · refine ⟨e g', ?_, ?_⟩
    · simp only [inv_mul_cancel, one_mem]
    · have hh : e (a'⁻¹*g') ∈ modelParabolic t (!i) := hQ ▸ mem_map_of_mem _ hg'
      have heq : d'⁻¹*e g' = (d'⁻¹*e a')*e (a'⁻¹*g') := by
        rw [map_mul, map_inv]
        group
      rw [heq]
      exact mul_mem hdm' hh
  · unfold matrixFixed
    rw [hp, hp1]
    simpa only [map_aut_mul] using hf
  · unfold matrixFixed
    rw [hp, hp1]
    simpa only [map_aut_mul] using hf'
  · rw [hp1, hp, hp, ← Subgroup.map_sup, ← Subgroup.map_sup, htop,
      Subgroup.map_top_of_surjective _ e.surjective]
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Pencils
