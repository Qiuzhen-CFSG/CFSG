module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.NaturalGeneration.Model

/-!
# Natural coordinates on the opposite parabolic orbit

A nonzero vector fixed by one marked parabolic selects the point member
of the incident point–line pair. In standard coordinates it is the first
basis vector, whose orbit under the line parabolic spans exactly the plane
with last coordinate zero. The upper-left block gives a surjective map to
SL₂(2), and the first two coordinates intertwine its natural matrix action.
Conjugation transports both maps and the literal orbit closure back to the
arbitrary marking, including markings involving the graph automorphism.

This is the concrete natural two-space calculation needed in the application
of Meierfrankenfeld–Stellmacher (1993), (1.7), printed pp.847–848, on p.883.
-/

public section

open Matrix Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof
open Matrix.PSL3Two
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.NaturalGeneration

private theorem last_entry (g : lineParabolicSL) : g.val.val 2 2 = 1 := by
  obtain ⟨h20, h21⟩ := (mem_lineParabolicSL_iff g.val).mp g.property
  have hd := g.val.property
  rw [det_fin_three] at hd
  have hn : g.val.val 2 2 ≠ 0 := by
    intro hz
    simp [h20, h21, hz] at hd
  exact (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hn

private def lineProjection : lineParabolicSL →* SL2 where
  toFun g := ⟨!![g.val.val 0 0, g.val.val 0 1; g.val.val 1 0, g.val.val 1 1], by
    obtain ⟨h20, h21⟩ := (mem_lineParabolicSL_iff g.val).mp g.property
    have hd := g.val.property
    rw [det_fin_three] at hd
    simpa [det_fin_three, det_fin_two, h20, h21, last_entry g] using hd⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' g h := by
    apply Subtype.ext
    obtain ⟨h20, h21⟩ := (mem_lineParabolicSL_iff h.val).mp h.property
    change !![(g.val.val * h.val.val) 0 0, (g.val.val * h.val.val) 0 1;
      (g.val.val * h.val.val) 1 0, (g.val.val * h.val.val) 1 1] =
      !![g.val.val 0 0, g.val.val 0 1; g.val.val 1 0, g.val.val 1 1] *
      !![h.val.val 0 0, h.val.val 0 1; h.val.val 1 0, h.val.val 1 1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h20, h21]

private theorem lineProjection_surjective : Function.Surjective lineProjection := by
  intro a
  let g : SL := ⟨!![a.val 0 0, a.val 0 1, 0; a.val 1 0, a.val 1 1, 0; 0, 0, 1], by
    have hd := a.property
    rw [det_fin_two] at hd
    simpa [det_fin_three] using hd⟩
  refine ⟨⟨g, (mem_lineParabolicSL_iff g).mpr ⟨rfl, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private def planeEquiv : incidentPlane ≃* Multiplicative (Fin 2 → ZMod 2) where
  toFun v := Multiplicative.ofAdd ![v.val.toAdd 0, v.val.toAdd 1]
  invFun v := ⟨Multiplicative.ofAdd ![v.toAdd 0, v.toAdd 1, 0], rfl⟩
  left_inv v := by
    apply Subtype.ext
    change ![v.val.toAdd 0, v.val.toAdd 1, 0] = v.val.toAdd
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact v.property.symm
  right_inv v := by
    change ![v.toAdd 0, v.toAdd 1] = v.toAdd
    ext i
    fin_cases i <;> rfl
  map_mul' v w := by
    change (![v.val.toAdd 0 + w.val.toAdd 0, v.val.toAdd 1 + w.val.toAdd 1] : Fin 2 → ZMod 2) = _
    ext i
    fin_cases i <;> rfl

private theorem plane_action (g : lineParabolicSL) (x y : incidentPlane)
    (h : (y : VectorGroup) = vectorAction (g : SL) (x : VectorGroup)) :
    (planeEquiv y).toAdd = (lineProjection g).val.mulVec (planeEquiv x).toAdd := by
  have hx : x.val.toAdd 2 = 0 := x.property
  change y.val.toAdd = g.val.val.mulVec x.val.toAdd at h
  change ![y.val.toAdd 0, y.val.toAdd 1] =
    !![g.val.val 0 0, g.val.val 0 1; g.val.val 1 0, g.val.val 1 1].mulVec
      ![x.val.toAdd 0, x.val.toAdd 1]
  rw [h]
  ext i
  fin_cases i <;>
    simp [mulVec, dotProduct, Fin.sum_univ_three,
      Fin.sum_univ_two, hx]

private def seed : VectorGroup := Multiplicative.ofAdd ![1, 0, 0]

private theorem fixed_seed (w : VectorGroup) (hw : w ≠ 1)
    (hf : w ∈ fixedSpace pointParabolicSL) : w = seed := by
  have hc : w ∈ fixedSpace Matrix.PSL3Two.MarkedAutomorphisms.pointV := by
    intro a ha
    apply hf a
    rw [← MarkedProduct.pointParabolic_core] at ha
    exact Subgroup.pCoreIn_le 2 pointParabolicSL ha
  rw [fixed_pointCore] at hc
  have test : ∀ w : Fin 3 → ZMod 2,
      w ≠ 0 → w 1 = 0 ∧ w 2 = 0 → w = ![1, 0, 0] := by decide
  exact test w.toAdd hw hc

private theorem standard_span :
    closure (Set.range fun g : lineParabolicSL => vectorAction (g : SL) seed) =
      incidentPlane := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨g, rfl⟩
    have hg := ((mem_lineParabolicSL_iff g.val).mp g.property).1
    change (g.val.val.mulVec ![1, 0, 0]) 2 = 0
    simpa [mulVec, dotProduct, Fin.sum_univ_three] using hg
  · let T := closure (Set.range fun g : lineParabolicSL => vectorAction (g : SL) seed)
    have h0 : seed ∈ T := by
      have := subset_closure (Set.mem_range_self (f := fun g : lineParabolicSL =>
        vectorAction (g : SL) seed) 1)
      simpa using this
    have h1 : vectorAction lineCycle seed ∈ T :=
      subset_closure ⟨⟨lineCycle, lineCycle_mem⟩, rfl⟩
    intro w hw
    have test : ∀ w : Fin 3 → ZMod 2, w 2 = 0 →
        w = 0 ∨ w = ![1, 0, 0] ∨ w = lineCycle.val.mulVec ![1, 0, 0] ∨
          w = ![1, 0, 0] + lineCycle.val.mulVec ![1, 0, 0] := by decide
    obtain h|h|h|h := test w.toAdd hw
    · rw [show w = 1 from h]; exact T.one_mem
    · rw [show w = seed from h]; exact h0
    · rw [show w = vectorAction lineCycle seed from h]; exact h1
    · rw [show w = seed * vectorAction lineCycle seed from h]; exact T.mul_mem h0 h1

private noncomputable def actorEquiv (σ : MulAut SL) (P : Subgroup SL) (k : SL)
    (hq : P.map σ.toMonoidHom = lineParabolicSL.map (MulAut.conj k).toMonoidHom) :
    P ≃* lineParabolicSL :=
  ((σ.subgroupMap P).trans (MulEquiv.subgroupCongr hq)).trans
    ((MulAut.conj k).subgroupMap lineParabolicSL).symm

private theorem actorEquiv_spec (σ : MulAut SL) (P : Subgroup SL) (k : SL)
    (hq : P.map σ.toMonoidHom = lineParabolicSL.map (MulAut.conj k).toMonoidHom)
    (g : P) : MulAut.conj k (actorEquiv σ P k hq g : SL) = σ (g : SL) := by
  exact (MulAut.conj k).apply_symm_apply _

private theorem orbit_span (σ : MulAut SL) (P : Subgroup SL) (k : SL)
    (hq : P.map σ.toMonoidHom = lineParabolicSL.map (MulAut.conj k).toMonoidHom) :
    closure (Set.range fun g : P => vectorAction (σ g) (vectorAction k seed)) =
      incidentPlane.map (vectorAction k).toMonoidHom := by
  rw [← standard_span, MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext w
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨vectorAction (actorEquiv σ P k hq g : SL) seed, ⟨_, rfl⟩, ?_⟩
    change vectorAction k (vectorAction (actorEquiv σ P k hq g : SL) seed) =
      vectorAction (σ (g : SL)) (vectorAction k seed)
    rw [← actorEquiv_spec σ P k hq g, action_conj]
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    obtain ⟨g, rfl⟩ := (actorEquiv σ P k hq).surjective a
    refine ⟨g, ?_⟩
    change vectorAction (σ (g : SL)) (vectorAction k seed) =
      vectorAction k (vectorAction (actorEquiv σ P k hq g : SL) seed)
    rw [← actorEquiv_spec σ P k hq g, action_conj]

private noncomputable def plane_of_conjugate (σ : MulAut SL) (P : Subgroup SL)
    (T : Subgroup VectorGroup) (k : SL)
    (hq : P.map σ.toMonoidHom = lineParabolicSL.map (MulAut.conj k).toMonoidHom)
    (hT : T = incidentPlane.map (vectorAction k).toMonoidHom) : NaturalPlane σ P T := by
  let e := actorEquiv σ P k hq
  let c : T ≃* incidentPlane := (MulEquiv.subgroupCongr hT).trans
    ((vectorAction k).subgroupMap incidentPlane).symm
  have hc (x : T) : vectorAction k (c x : VectorGroup) = (x : VectorGroup) :=
    (vectorAction k).apply_symm_apply _
  refine ⟨lineProjection.comp e.toMonoidHom,
    lineProjection_surjective.comp e.surjective, c.trans planeEquiv, ?_⟩
  intro g x y h
  apply plane_action (e g) (c x) (c y)
  apply (vectorAction k).injective
  rw [hc, ← action_conj, actorEquiv_spec, hc]
  exact h

/-- A nonidentity vector fixed by the first marked parabolic generates the
natural binary two-space under the opposite parabolic. The coordinates are
on the exact orbit closure, and their actor homomorphism is surjective. -/
theorem planeCoordinates_nonempty (σ : MulAut SL) (flag : SL) (i : Bool)
    (v : VectorGroup) (hv : v ≠ 1)
    (hfixed : ∀ g ∈ modelParabolic flag i, (σ g).val.mulVec v.toAdd = v.toAdd) :
    Nonempty (PlaneCoordinates σ flag i v) := by
  have hf : v ∈ fixedSpace (markedParabolic σ flag i) := by
    rintro a ⟨g, hg, rfl⟩
    exact hfixed g hg
  obtain ⟨k, ⟨hp, hq⟩|⟨hp, hq⟩⟩ := marked_pair σ flag i
  · rw [hp, fixedSpace_conj] at hf
    obtain ⟨w, hw, rfl⟩ := hf
    have hw1 : w ≠ 1 := by
      intro he
      apply hv
      rw [he, map_one]
    rw [fixed_seed w hw1 hw]
    exact ⟨plane_of_conjugate σ (modelParabolic flag (!i))
      (oppositeSpan σ flag i (vectorAction k seed)) k hq
      (orbit_span σ (modelParabolic flag (!i)) k hq)⟩
  · rw [hp, fixedSpace_conj, line_fixed_bot, Subgroup.map_bot] at hf
    exact (hv (Subgroup.mem_bot.mp hf)).elim

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.NaturalGeneration
