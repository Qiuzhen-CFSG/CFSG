module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalBranches
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CrossSelectedPaths

/-!
# Kernel saturation at the actual unequal-mover selected neighbor

Apply the equal-order saturation argument before making the existing
residual root selection. Conjugation fixes the original Q-kernel and takes
each individual mover to its literal mover at the selected common edge.
The same selected neighbor therefore retains the complete kernel, both
exact square image orders, and the intersection bound, together with the
original B-relative index, whole edge-Z fixed subgroup, and every overlap
of the backward critical path or its full trapped-root alternative.

Source: MS93 (5.5)(c) and (5.7), printed pp.915--919. Generation here still
uses the join of both movers. Individual generation, the nonsplitting
exception, trapped-root exclusion and terminal exclusions remain open.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h
/-- The actual root-selected neighbor retains the full kernel and both
square image orders. No quotient kernel or central attachment is dropped. -/
theorem Input.replacement_unequal_selected_root_small_image
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (himage : (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical c)
      (Q d.radical c) (Q d.radical t) (Nat.card F^2)) ≤ Nat.card F^2) :
    ∃ g ∈ Ltilde d.radical a,
      let w := act d.radical g⁻¹ t
      let v := act d.radical g⁻¹ c
      let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) ⊔
        Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
          (Q d.radical t) (Nat.card F^2)
      let Ja := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical w) (Nat.card F^2)
      let Ec := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical w) (Nat.card F^2)
      Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) =
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
      J.map (MulAut.conj g).toMonoidHom =
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical w) (Nat.card F^2) ⊔
        Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2) ∧
      J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical a ∧
      Z d.radical t ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      Q d.radical a ≤ Ja ⊓ Ec ∧
      (Q d.radical a).relIndex Ja = Nat.card F^2 ∧
      (Q d.radical a).relIndex Ec = Nat.card F^2 ∧
      (Q d.radical a).relIndex (Ja ⊓ Ec) ≤ Nat.card F^2 ∧
      ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ((∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = w ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∨
      (Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
        (Q d.radical z).relIndex (Z d.radical a) = Nat.card F ∧
        (Q d.radical a).relIndex (Z d.radical z) = Nat.card F ∧
        Nat.card F ≤ (centralizer (Z d.radical v : Set (FreeAmalgam d.radical))).relIndex
          (Z d.radical z ⊓ Q d.radical a) ∧
        X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical v : Set _) ∧
        ⁅⁅X d.radical z ⊓ Q d.radical a,Z d.radical v⁆,Z d.radical v⁆ = ⊥)) := by
  obtain ⟨g,hg,haw,hvw,hindex,htransport,hgen,hfixed,hn,hback⟩ :=
    h.replacement_unequal_join_selected_root_at_neighbor d path hb hat hfirst hct
      hnormal hsmall hne
  obtain ⟨hQ,hJi,hEi,hcap⟩ := h.replacement_unequal_small_image_saturated d geometry hb
    path.start_color hat hct himage
  let S := stabilizer d.radical a
  let w := act d.radical g⁻¹ t
  let v := act d.radical g⁻¹ c
  let J₀ := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let E₀ := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  have hgS : g ∈ S := Ltilde_le_stabilizer a hg
  have hUa : (U d.radical a).map (MulAut.conj g).toMonoidHom = U d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (U_normalized a hgS)
  have hQa : (Q d.radical a).map (MulAut.conj g).toMonoidHom = Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hgS)
  have hJa : J₀.map (MulAut.conj g).toMonoidHom =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical w) (Nat.card F^2) := by
    dsimp only [J₀]
    rw [Subgroup.SmallMover.join_map _ (MulAut.conj g).injective,hUa,hQa]
    simp only [w,Q_act,inv_inv]
  have hEc : E₀.map (MulAut.conj g).toMonoidHom =
      Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical w) (Nat.card F^2) := by
    dsimp only [E₀]
    rw [Subgroup.SmallMover.join_map _ (MulAut.conj g).injective]
    simp only [v,w,U_act,Q_act,inv_inv]
  have hQm := map_mono (f := (MulAut.conj g).toMonoidHom) hQ
  change (Q d.radical a).map (MulAut.conj g).toMonoidHom ≤
    (J₀ ⊓ E₀).map (MulAut.conj g).toMonoidHom at hQm
  rw [map_inf _ _ _ (MulAut.conj g).injective,hQa,hJa,hEc] at hQm
  have hJm := (relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) (Q d.radical a) J₀
    (MulAut.conj g).injective).trans hJi
  rw [hQa,hJa] at hJm
  have hEm := (relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) (Q d.radical a) E₀
    (MulAut.conj g).injective).trans hEi
  rw [hQa,hEc] at hEm
  have hIm := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) (Q d.radical a) (J₀ ⊓ E₀)
    (MulAut.conj g).injective
  rw [map_inf _ _ _ (MulAut.conj g).injective,hQa,hJa,hEc] at hIm
  exact ⟨g,hg,haw,hvw,hindex,htransport,hgen,hfixed,hQm,hJm,hEm,
    hIm.le.trans hcap,hn,hback⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
