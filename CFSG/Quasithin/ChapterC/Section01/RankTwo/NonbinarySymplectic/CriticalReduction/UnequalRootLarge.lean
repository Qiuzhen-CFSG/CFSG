module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootSplitting
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalNonsplitting

/-!
# Unequal movers above the square bound in the critical-root case

The small critical root gives X = U C_X(G_alpha). An unequal neighboring
mover containing the original Q-kernel would force X != U C_X(G_alpha)
by the genuine nonsplitting calculation. Thus it misses Q. Small-image
saturation then forces its image order to be strictly greater than q squared.

The application retains the actual selected g, w = g inverse t and
v = g inverse c. Conjugation fixes the original Q and transports the
individual mover, so the strict image bound and missing-kernel conclusion
hold at that same neighbor. The full edge-Z fixed equalities, B-relative
U-index, quadratic own-layer actions, and backward-path or trapped-root
alternative are retained. Generation here still uses the two movers together;
individual residual generation and the trapped-root exclusion remain open.

Source: MS93 (3.3)(ii)(2) and (5.5)(c), printed pp.867, 915--917.
The nonsplitting alternative for larger critical images is not removed.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A small critical root excludes full-kernel containment in every unequal
neighboring mover. Equal mover orders then force its image above q squared. -/
theorem Input.replacement_root_unequal_mover_large
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2)) :
    let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)
    ¬ Q d.radical a ≤ E ∧ Nat.card F^2 < (Q d.radical a).relIndex E := by
  dsimp only
  have hsplit := h.replacement_root_X_decomposition_center d path hb hsmall
  have hnot : ¬ Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) := by
    intro hQE
    exact h.replacement_unequal_kernel_nonsplitting d geometry hb path.start_color
      hat hct hne hQE hsplit
  refine ⟨hnot,lt_of_not_ge ?_⟩
  intro hle
  exact hnot ((h.replacement_unequal_small_image_saturated d geometry hb
    path.start_color hat hct hle).1.trans inf_le_right)

/-- The actual root-selected neighbor has strictly large individual image
and misses the original kernel, with the same full-layer and path data. -/
theorem Input.replacement_unequal_large_root_at_neighbor
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2)) :
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
      Z d.radical t ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      ⁅⁅U d.radical a,Ja⁆,Ja⁆ = ⊥ ∧ ⁅⁅U d.radical v,Ec⁆,Ec⁆ = ⊥ ∧
      (centralizer (Ec : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = Nat.card F^3 ∧
      ¬ Q d.radical a ≤ Ec ∧ Nat.card F^2 < (Q d.radical a).relIndex Ec ∧
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
  obtain ⟨g,hg,haw,hvw,hindex,htransport,hgen,hfixed,hindividual,
    hquadA,hquadC,hcube,_hbranch,hn,hback⟩ :=
      h.replacement_unequal_individual_fixed_root_at_neighbor d path hb hat hfirst hct
        hnormal hsmall hne
  obtain ⟨hnot,hlarge⟩ := h.replacement_root_unequal_mover_large d path hb hat hct hsmall hne
  have hgS := Ltilde_le_stabilizer a hg
  have hQa : (Q d.radical a).map (MulAut.conj g).toMonoidHom = Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hgS)
  have hEc : (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)).map (MulAut.conj g).toMonoidHom =
      Subgroup.SmallMover.join (U d.radical (act d.radical g⁻¹ c))
        (Q d.radical (act d.radical g⁻¹ c)) (Q d.radical (act d.radical g⁻¹ t))
        (Nat.card F^2) := by
    rw [Subgroup.SmallMover.join_map _ (MulAut.conj g).injective]
    simp only [U_act,Q_act,inv_inv]
  refine ⟨g,hg,haw,hvw,hindex,htransport,hgen,hfixed,hindividual,
    hquadA,hquadC,hcube,?_,?_,hn,hback⟩
  · intro hle
    apply hnot
    apply (map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).mp
    rwa [hQa,hEc]
  · rw [←hEc,←hQa,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hlarge

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
