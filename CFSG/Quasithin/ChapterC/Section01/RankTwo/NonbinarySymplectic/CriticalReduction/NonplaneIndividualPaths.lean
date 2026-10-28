module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NonplaneIndividualSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootEscape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.PairedChoice
/-!
# Individual generation on the actual nonplane backward path

The selector at unequal neighboring movers now generates the vertex
residual using the individual mover and full critical endpoint in both
kernel branches. The same selected neighbor retains joined generation,
both whole-edge-Z fixed subgroups, the exact B-relative U-index,
quadratic own-layer actions and every backward-path overlap.

Trapping would force the critical image to have order q, contradicting
its proved order q squared. Kernel containment still yields the genuine
whole-X nonsplitting conclusion; it no longer prevents individual
generation in this nonplane-image branch. No central factor is removed.

Source: MS93 (5.5)(b,c) and (5.7), printed pp.915--919. The path retains
its original distance. Contained large-image selection, root trapping,
terminal exclusions and the distance-two witness remain unproved.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h
/-- The actual nonplane selector always gives a backward path and individual
residual generation. All original fixed-layer, index and nonsplitting
conclusions hold at that same neighbor, with every overlap retained. -/
theorem Input.replacement_unequal_nonplane_individual_backward_path
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hTn : unipotent ≤ normalizer
      (((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f : Set (Sp B.Carrier)))
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hcritical : ¬ ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
      (CentralRootGeometry.wing true).map unipotent.subtype) :
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
      Ltilde d.radical a ≤ Ec ⊔ Z d.radical z ∧
      Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) =
        (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
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
      ((¬ Q d.radical a ≤ Ec ∧ Nat.card F^2 < (Q d.radical a).relIndex Ec ∧
        Ltilde d.radical a ≤ Ec ⊔ Z d.radical z) ∨
       (Q d.radical a ≤ Ec ∧ X d.radical a ≠ U d.radical a ⊔
        (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))))) ∧
      ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = w ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i := by
  obtain ⟨g,hg,hresidual,hbranch,hgen,hindividual⟩ := h.replacement_unequal_nonplane_individual_selector
    d path hb hat hfirst hct hne B hB f hf hfQ hTf hTn hindex hcritical
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
  have hUindex := movingIndex_act geometry (d := c) (by omega) path.start_color g⁻¹ (S.inv_mem hgS)
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
  obtain ⟨hquadA,hquadC,hcube,_hbranch⟩ :=
    h.replacement_unequal_branch_data d geometry hb path.start_color haw hvw hne'
  have hselected :
      (¬ Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical v)
          (Q d.radical v) (Q d.radical w) (Nat.card F^2) ∧
        Nat.card F^2 < (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical v)
          (Q d.radical v) (Q d.radical w) (Nat.card F^2)) ∧
        Ltilde d.radical a ≤ Subgroup.SmallMover.join (U d.radical v)
          (Q d.radical v) (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical z) ∨
      (Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical v)
          (Q d.radical v) (Q d.radical w) (Nat.card F^2) ∧
        X d.radical a ≠ U d.radical a ⊔ (X d.radical a ⊓
          centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))) := by
    rcases hbranch with ⟨hnotQ,hres⟩ | ⟨hQE,hnonsplit⟩
    ·
      have hnot : ¬ Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical v)
          (Q d.radical v) (Q d.radical w) (Nat.card F^2) := by
        intro hh
        apply hnotQ
        apply (map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
          (MulAut.conj g).injective).mp
        rwa [hQa,hEc]
      have hlarge : Nat.card F^2 < (Q d.radical a).relIndex
          (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2)) := by
        apply lt_of_not_ge
        intro hh
        exact hnot ((h.replacement_unequal_small_image_saturated d geometry hb
          path.start_color haw hvw hh).1.trans inf_le_right)
      rw [hEc] at hres
      exact Or.inl ⟨hnot,hlarge,hres⟩
    · refine Or.inr ⟨?_,hnonsplit⟩
      have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hQE
      rwa [hQa,hEc] at hm
  rw [hJa] at hindividual
  rw [hEc] at hresidual
  refine ⟨g,hg,hresidual,haw,hvw,hUindex,htransport,hgen,hfixed,hindividual,
    hquadA,hquadC,hcube,hselected,hn,?_⟩
  apply exists_backward_path_of_not_le geometry (by omega) path haw hvw
  intro hk
  have hYV : Z d.radical v ≤ V d.radical a :=
    le_sup_left.trans (neighbor_seed_join_le_radius haw hvw)
  have hYS : Z d.radical v ≤ stabilizer d.radical z :=
    (le_inf hYV hk).trans (truncated_radius_le_endpoint_stabilizer path (by omega))
  have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hi := (h.replacement_critical_indices_eq_field_of_seed_escape d path
    (by omega) (Z d.radical v) hYS hYQ hn).2
  have hcard := (h.replacement_nonplane_critical_coordinates d path hb hfirst
    B hB f hfQ hTf hindex hcritical).1
  rw [hcard] at hi
  have hq : 1 < Nat.card F := Finite.one_lt_card
  nlinarith

/-- Compatibility form of the selected path, with its original alternatives. -/
theorem Input.replacement_unequal_nonplane_backward_path
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hTn : unipotent ≤ normalizer
      (((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f : Set (Sp B.Carrier)))
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hcritical : ¬ ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
      (CentralRootGeometry.wing true).map unipotent.subtype) :
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
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) =
        (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
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
      ((¬ Q d.radical a ≤ Ec ∧ Nat.card F^2 < (Q d.radical a).relIndex Ec ∧
        Ltilde d.radical a ≤ Ec ⊔ Z d.radical z) ∨
       (Q d.radical a ≤ Ec ∧ X d.radical a ≠ U d.radical a ⊔
        (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))))) ∧
      ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = w ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i := by
  obtain ⟨g,hg,_,hrest⟩ := h.replacement_unequal_nonplane_individual_backward_path d path hb
    hat hfirst hct hnormal hne B hB f hf hfQ hTf hTn hindex hcritical
  exact ⟨g,hg,hrest⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
