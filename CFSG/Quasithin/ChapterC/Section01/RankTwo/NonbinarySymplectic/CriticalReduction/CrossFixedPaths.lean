module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CrossFixedSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootEscape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.PairedChoice
/-!
# The individual fixed-layer clause at the actual root-selected edge

The same selector gives generation by the two unequal movers together and
ambient fixedness on the whole original edge Z for the original mover
alone. Transport identifies this mover with the literal mover at the
selected edge. The nonnormal neighbor, its exact B-relative U-index, and
all overlaps of the backward critical path or trapped-root alternative
are retained for this very conjugator. The individual movement and
small-image saturation conclusions are proved at the same selected pair,
including its entire Q-kernel and literal intersection.

Source: MS93 (5.5)(a,b) and (5.7), printed pp.915--919, root-image branch.
Individual generation with the genuine nonsplitting exception, contained
large-image selection, trapped-root exclusion, and terminal distance
exclusions remain unproved; the selected path retains its original length.
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
/-- The prescribed unequal neighbor has one root selector carrying the
individual whole-edge-Z fixed equality, exact own-layer quadratic actions,
and the full-kernel small-image alternative, together with every overlap
of its backward path or the complete trapped-root alternative. -/
theorem Input.replacement_unequal_individual_fixed_root_at_neighbor
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
      ((Nat.card F^2 < (Q d.radical a).relIndex Ec) ∨
        (Q d.radical a ≤ Ja ⊓ Ec ∧
          (Q d.radical a).relIndex Ja = Nat.card F^2 ∧
          (Q d.radical a).relIndex Ec = Nat.card F^2 ∧
          (Q d.radical a).relIndex (Ja ⊓ Ec) ≤ Nat.card F^2)) ∧
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
  obtain ⟨g,hg,hgen,hindividual⟩ := h.replacement_unequal_root_individual_fixed_selector
    d path hb hat hfirst hct hsmall hne
  let S := stabilizer d.radical a
  let w := act d.radical g⁻¹ t
  let v := act d.radical g⁻¹ c
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2) ⊔
    Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)
  have hgS : g ∈ S := Ltilde_le_stabilizer a hg
  have hga : act d.radical g⁻¹ a = a := S.inv_mem hgS
  have haw : Adjacent d.radical a w := by
    rw [←hga]
    exact (adjacent_act_iff d.radical g⁻¹ _ _).mpr hat
  have hvw : Adjacent d.radical v w := (adjacent_act_iff d.radical g⁻¹ _ _).mpr hct
  have hJw : J.map (MulAut.conj g).toMonoidHom ≤ Q d.radical w := by
    simpa only [w,Q_act,inv_inv] using map_mono (f := (MulAut.conj g).toMonoidHom)
      (sup_le (Subgroup.SmallMover.join_le (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2))
        (Subgroup.SmallMover.join_le (U d.radical c) (Q d.radical c)
          (Q d.radical t) (Nat.card F^2)))
  have hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hbad
    have hwhole : S ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      change stabilizer d.radical a ≤ _
      rw [←hgen]
      exact sup_le (hJw.trans (edge_normalizes_neighbor_seed_join haw hvw)) hbad
    have hZa : (Z d.radical a).map (MulAut.conj g⁻¹).toMonoidHom = Z d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a (S.inv_mem hgS))
    have hZv : (Z d.radical v).map (MulAut.conj g⁻¹).toMonoidHom = Z d.radical c := by
      rw [show Z d.radical v = (Z d.radical c).map (MulAut.conj g).toMonoidHom by
        simp only [v,Z_act,inv_inv],Subgroup.map_map]
      have hh : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          MonoidHom.id (FreeAmalgam d.radical) := by
        apply MonoidHom.ext
        intro x
        change g⁻¹*(g*x*g⁻¹)*(g⁻¹)⁻¹=x
        group
      rw [hh,Subgroup.map_id]
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hwhole
    have hS : S.map (MulAut.conj g⁻¹).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer (S.inv_mem hgS))
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective,
      Subgroup.map_sup,hZv,hZa,hS] at hm
    exact hnormal hm
  have hindex := movingIndex_act geometry (d := c) (by omega) path.start_color g⁻¹ (S.inv_mem hgS)
  have ht : color d.radical t ≠ false := by
    have hh := adjacent_color_ne d.radical hat
    rw [path.start_color] at hh
    exact Ne.symm hh
  have hzT : Z d.radical z ≤ Q d.radical t := by
    rw [←hfirst]
    apply Z_le_Q_of_dist_lt d.radical z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.dist_end,geometry.distance_constant z path.end_color]
    change path.walk.length - 1 < geometry.b d.radical
    rw [path.length_eq_b]
    omega
  have hfix : Z d.radical t ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) := by
    intro v hv y hy
    rw [Z,if_neg ht] at hv
    exact (mem_omegaCenter_iff.mp hv).2.2 y (hzT hy)
  have hfixed : Z d.radical t ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set _) =
      Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set _) := by
    apply le_antisymm
    · refine le_inf inf_le_left (le_centralizer_iff.mpr ?_)
      rw [←hgen]
      exact sup_le (le_centralizer_iff.mp inf_le_right)
        (le_centralizer_iff.mp (inf_le_left.trans hfix))
    · have hle : J.map (MulAut.conj g).toMonoidHom ≤ stabilizer d.radical a :=
        le_sup_left.trans_eq hgen
      exact inf_le_inf_left _ (centralizer_le hle)
  have hUa : (U d.radical a).map (MulAut.conj g).toMonoidHom = U d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (U_normalized a hgS)
  have hQa : (Q d.radical a).map (MulAut.conj g).toMonoidHom = Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hgS)
  have htransport : J.map (MulAut.conj g).toMonoidHom =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical w) (Nat.card F^2) ⊔
      Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2) := by
    dsimp only [J,v,w]
    rw [Subgroup.map_sup,Subgroup.SmallMover.join_map _ (MulAut.conj g).injective,
      Subgroup.SmallMover.join_map _ (MulAut.conj g).injective,hUa,hQa]
    simp only [U_act,Q_act,inv_inv]
  have hJa : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).map (MulAut.conj g).toMonoidHom =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical w) (Nat.card F^2) := by
    rw [Subgroup.SmallMover.join_map _ (MulAut.conj g).injective,hUa,hQa]
    simp only [w,Q_act,inv_inv]
  have hEc : (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)).map (MulAut.conj g).toMonoidHom =
      Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical w) (Nat.card F^2) := by
    rw [Subgroup.SmallMover.join_map _ (MulAut.conj g).injective]
    simp only [v,w,U_act,Q_act,inv_inv]
  have hne' : Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
      (Q d.radical w) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical w) (Nat.card F^2) := by
    rw [←hEc,←hJa]
    intro he
    exact hne (Subgroup.map_injective (MulAut.conj g).injective he)
  obtain ⟨hquadA,hquadC,hcube,hbranch⟩ :=
    h.replacement_unequal_branch_data d geometry hb path.start_color haw hvw hne'
  rw [hJa] at hindividual
  refine ⟨g,hg,haw,hvw,hindex,htransport,hgen,hfixed,hindividual,
    hquadA,hquadC,hcube,hbranch,hn,?_⟩
  by_cases hk : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2))
  · right
    have hYV : Z d.radical v ≤ V d.radical a :=
      le_sup_left.trans (neighbor_seed_join_le_radius haw hvw)
    have hYS : Z d.radical v ≤ stabilizer d.radical z :=
      (le_inf hYV hk).trans (truncated_radius_le_endpoint_stabilizer path (by omega))
    have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
    obtain ⟨hi,hi'⟩ := h.replacement_critical_indices_eq_field_of_seed_escape d path
      (by omega) (Z d.radical v) hYS hYQ hn
    have hindex := h.replacement_seed_actor_centralizer_index_ge_field d path (by omega)
      (Z d.radical v) hYS hYQ hn (Z d.radical v) le_rfl hYS
    have hcolor : color d.radical v = false := by
      have hn₁ := adjacent_color_ne d.radical haw
      have hn₂ := adjacent_color_ne d.radical hvw
      rw [path.start_color] at hn₁
      cases ht : color d.radical w <;> cases hv : color d.radical v <;> simp_all
    have hAY : X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical v : Set _) :=
      (inf_le_right.trans (Q_le_stabilizer_of_dist_le_two a v path.start_color hcolor
        (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two haw hvw))).trans
          (Z_normalized d.radical v)
    have htrip := (h.replacement_radius_commutator_bounds d geometry hb path.start_color z
      (path.walk.getVert (path.walk.length-2))).2
    exact ⟨hk,hi,hi',hindex,hAY,le_bot_iff.mp
      ((commutator_mono (commutator_mono le_rfl (le_inf hYV hk)) (le_inf hYV hk)).trans_eq htrip)⟩
  · exact Or.inl (exists_backward_path_of_not_le geometry (by omega) path haw hvw hk)


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
