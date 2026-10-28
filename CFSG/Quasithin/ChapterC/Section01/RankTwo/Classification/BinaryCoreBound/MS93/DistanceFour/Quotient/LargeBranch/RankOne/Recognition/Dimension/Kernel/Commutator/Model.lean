module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Parabolics.Model
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Standard
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Transport
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Coverage

/-!
# The incident cores and their natural fixed subgroups

The two intrinsic parabolic cores generate the Borel: its eight upper
matrices are products of one element from each core. Conjugation transports
this equality to any marked flag.

On the natural binary three-space the point core fixes a line and the line
core fixes a plane. The inner-or-graph description of an arbitrary marking
preserves the product of their orders, which is eight. The source consumer
knows that the first core fixes a plane and therefore obtains order two for
the second fixed subgroup, without bounding the whole source Z_delta2.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the incident flag on p.905 and the last paragraph of (4.6.12)(5),
printed p.912.
-/

public section
open Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
namespace CommutatorModel
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof

private theorem line_core : lineParabolicSL.pCoreIn 2 = lineV := by
  rw [← pointParabolic_map_diagram, ← map_pCoreIn_of_injective 2 _ _ diagram.injective,
    MarkedProduct.pointParabolic_core, pointV_map_diagram]

private theorem lineV_R : lineV = BinaryLinearThree.R := by
  rw [← line_core, lineParabolicSL_pCoreIn_two_eq_R]

private theorem lineV_diagram : lineV.map diagram.toMonoidHom = pointV := by
  rw [← pointV_map_diagram, map_map]
  have he : diagram.toMonoidHom.comp diagram.toMonoidHom = MonoidHom.id SL := by
    ext x : 1
    exact diagram_involutive x
  rw [he, map_id]

/-- Each intrinsic core lies in the Borel of the same incident flag. -/
theorem core_le_borel (g : SL) (i : Bool) :
    (modelParabolic g i).pCoreIn 2 ≤ modelBorel g := by
  have hB : (modelBorelSylow g : Subgroup SL) ≤ modelParabolic g i := by
    rw [coe_modelBorelSylow]
    exact modelParabolic_borel_le g i
  have h := pCoreIn_le_sylow (modelParabolic g i) ((modelBorelSylow g).subtype hB)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hB, coe_modelBorelSylow] at h
  exact h

private theorem core_sup : pointV ⊔ lineV = borelSL := by
  apply le_antisymm
  · have he : (MulAut.conj (1 : SL)).toMonoidHom = MonoidHom.id SL := by
      ext x; simp
    have hP (i : Bool) : modelParabolic 1 i =
        (if i then lineParabolicSL else pointParabolicSL) := by
      unfold modelParabolic
      rw [he, map_id]
    have hB : modelBorel 1 = borelSL := by
      unfold modelBorel
      rw [hP, hP]
      rfl
    have hp := core_le_borel 1 false
    have hl := core_le_borel 1 true
    rw [hP, if_neg Bool.false_ne_true, MarkedProduct.pointParabolic_core, hB] at hp
    rw [hP, if_pos rfl, line_core, hB] at hl
    exact sup_le hp hl
  · intro g hg
    have hcase : ∀ g : SL, g ∈ borelSL → ∃ i : Fin 8, g = Bruhat.upper i := by
      decide +kernel
    obtain ⟨i, rfl⟩ := hcase g hg
    have hw : ∀ i : Fin 8, ∃ j k : Fin 8,
        Bruhat.upper j ∈ pointV ∧ Bruhat.upper k ∈ lineV ∧
        Bruhat.upper i = Bruhat.upper j * Bruhat.upper k := by decide +kernel
    obtain ⟨j,k,hj,hk,he⟩ := hw i
    rw [he]
    exact mul_mem (mem_sup_left hj) (mem_sup_right hk)

private theorem point_conj_core (g : SL) :
    (modelParabolic g false).pCoreIn 2 = pointV.map (MulAut.conj g).toMonoidHom := by
  have h := map_pCoreIn_of_injective 2 pointParabolicSL
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  rw [MarkedProduct.pointParabolic_core] at h
  exact h.symm

private theorem line_conj_core (g : SL) :
    (modelParabolic g true).pCoreIn 2 = lineV.map (MulAut.conj g).toMonoidHom := by
  have h := map_pCoreIn_of_injective 2 lineParabolicSL
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  rw [line_core] at h
  exact h.symm

/-- The opposite intrinsic cores generate the literal incident Borel. -/
theorem model_core_sup (g : SL) :
    (modelParabolic g false).pCoreIn 2 ⊔ (modelParabolic g true).pCoreIn 2 = modelBorel g := by
  rw [point_conj_core, line_conj_core, ← Subgroup.map_sup, core_sup]
  exact map_inf _ _ _ (MulAut.conj g).injective

private theorem plane_card : Nat.card incidentPlane = 4 := by
  let e : incidentPlane ≃ (ZMod 2 × ZMod 2) := {
    toFun v := (v.val.toAdd 0, v.val.toAdd 1)
    invFun v := ⟨Multiplicative.ofAdd ![v.1, v.2, 0], rfl⟩
    left_inv v := by
      apply Subtype.ext
      change ![v.val.toAdd 0, v.val.toAdd 1, 0] = v.val.toAdd
      ext j
      fin_cases j
      · rfl
      · rfl
      · exact v.property.symm
    right_inv v := rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod]

private theorem fixed_pair (σ : MulAut SL) :
    Nat.card (fixedSpace (pointV.map σ.toMonoidHom)) *
      Nat.card (fixedSpace (lineV.map σ.toMonoidHom)) = 8 := by
  obtain ⟨g,hg|hg⟩ := inner_or_graph σ
  · rw [hg, fixedSpace_conj, fixedSpace_conj,
      card_map_of_injective (f := (vectorAction g).toMonoidHom) (vectorAction g).injective,
      card_map_of_injective (f := (vectorAction g).toMonoidHom) (vectorAction g).injective,
      fixed_pointCore, lineV_R, fixed_lineCore, line_card, plane_card]
  · have hmap (A : Subgroup SL) : A.map (MulAut.conj g * diagram).toMonoidHom =
        (A.map diagram.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      rw [map_map]; rfl
    rw [hg, hmap, hmap, pointV_map_diagram, lineV_diagram,
      fixedSpace_conj, fixedSpace_conj,
      card_map_of_injective (f := (vectorAction g).toMonoidHom) (vectorAction g).injective,
      card_map_of_injective (f := (vectorAction g).toMonoidHom) (vectorAction g).injective,
      fixed_pointCore, lineV_R, fixed_lineCore, line_card, plane_card]

/-- Both natural fixed subgroups use the same arbitrary automorphism marking. -/
theorem fixed_core_pair (σ : MulAut SL) (g : SL) (i : Bool) :
    Nat.card (fixedSpace (((modelParabolic g i).pCoreIn 2).map σ.toMonoidHom)) *
      Nat.card (fixedSpace (((modelParabolic g (!i)).pCoreIn 2).map σ.toMonoidHom)) = 8 := by
  have h := fixed_pair (σ * MulAut.conj g)
  have hmap (A : Subgroup SL) : A.map (σ * MulAut.conj g).toMonoidHom =
      (A.map (MulAut.conj g).toMonoidHom).map σ.toMonoidHom := by rw [map_map]; rfl
  rw [hmap, hmap, ← point_conj_core, ← line_conj_core] at h
  cases i
  · exact h
  · simpa only [Bool.not_true, Nat.mul_comm] using h
end CommutatorModel
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
