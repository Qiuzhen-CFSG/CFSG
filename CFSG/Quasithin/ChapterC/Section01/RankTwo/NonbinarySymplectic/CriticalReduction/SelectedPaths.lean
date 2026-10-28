module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.LargeSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ShiftedPaths

/-!
# Actual selected neighbors and the cubic large-image backward path

In the equal-mover case, transport the selector to both literal neighboring
vertices and edges. Their movers retain the two generation identities and
the full common fixed subgroup of Z. This respects the graph's right action,
which conjugates subgroups by the inverse element.

For a cubic-order mover and large critical image, one-conjugate generation
is enough for a selected backward path, even without equality of neighboring
movers. The original MS3 construction chooses a neighbor whose joined seed
is not locally normal. Conjugate it by the actual residual generator. If
that seed lay in the penultimate kernel, radius displacement would make the
endpoint normalize its join with Z. The generating edge and endpoint would
then make that join locally normal, a contradiction. The native path
construction preserves the common edge and every overlapping vertex.

Source: MS93 (5.6)--(5.8), printed pp.917--920, cubic-mover large-image branch.
The branch keeps its literal cubic-order and small-fixed-index hypotheses.
Proper movers, the root-image path selection and terminal exclusions remain
necessary for the minimum-replacement distance-two witness.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open MSCentralOrbit

private theorem mover_act {M : Type*} [Group M] [Finite M]
    (R : Subgroup M) (g : FreeAmalgam R) (a t : Vertex R) (q : ℕ) :
    Subgroup.SmallMover.join (U R (act R g a)) (Q R (act R g a))
      (Q R (act R g t)) q =
      (Subgroup.SmallMover.join (U R a) (Q R a) (Q R t) q).map
        (MulAut.conj g⁻¹).toMonoidHom := by
  rw [U_act,Q_act,Q_act,Subgroup.SmallMover.join_map _ (MulAut.conj g⁻¹).injective]

private theorem selected_ne {M : Type*} [Group M]
    (R : Subgroup M) {a c : Vertex R} (hne : c ≠ a)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a) : act R g c ≠ a := by
  intro he
  have hh := congrArg (act R g⁻¹) (he.trans (show act R g a = a from hg).symm)
  apply hne
  simpa only [←act_mul,mul_inv_cancel,act_one] using hh

private theorem nonnormal_map_conj {G : Type*} [Group G]
    (S W : Subgroup G) (hn : ¬ S ≤ normalizer (W : Set G))
    {g : G} (hg : g ∈ S) :
    ¬ S ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G) := by
  intro he
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) he
  rw [map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective] at hh
  have hs : S.map (MulAut.conj g⁻¹).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer (S.inv_mem hg))
  have hc : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
    apply MonoidHom.ext
    intro y
    change g⁻¹*(g*y*g⁻¹)*(g⁻¹)⁻¹ = y
    group
  rw [hs,Subgroup.map_map,hc,Subgroup.map_id] at hh
  exact hn hh

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The cubic equal-mover branch gives two actual nonbacktracking neighbor
choices, with generation and the whole Z fixed subgroup for their literal
movers. Both choices use the same source selector and full quotient kernel. -/
theorem Input.replacement_equal_cubic_selected_neighbors
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) (hca : c ≠ a)
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2))
    (hJc : (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2)) = Nat.card F^3)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let t₁ := act d.radical g⁻¹ t
      let c₁ := act d.radical g⁻¹ c
      let t₂ := act d.radical x t₁
      let c₂ := act d.radical x c₁
      let J₁ := Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
        (Q d.radical t₁) (Nat.card F^2)
      let J₂ := Subgroup.SmallMover.join (U d.radical c₂) (Q d.radical c₂)
        (Q d.radical t₂) (Nat.card F^2)
      Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧ c₁ ≠ a ∧
      Adjacent d.radical a t₂ ∧ Adjacent d.radical c₂ t₂ ∧ c₂ ≠ a ∧
      (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical a ∧
      (J₂ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom =
        stabilizer d.radical a ∧
      ((Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₂ : Set (FreeAmalgam d.radical)) =
        Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
  obtain ⟨g,hg,x,hx,hgen,hfixed,_⟩ :=
    h.replacement_cubic_small_mover_selection d path hb hat hJc hJm
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  have hgS : g ∈ S := Ltilde_le_stabilizer a hg
  have hxS : x ∈ S := Ltilde_le_stabilizer a hx
  have hga : act d.radical g⁻¹ a = a := S.inv_mem hgS
  have hxa : act d.radical x a = a := hxS
  have ha₁ : Adjacent d.radical a (act d.radical g⁻¹ t) := by
    rw [←hga]
    exact (adjacent_act_iff d.radical g⁻¹ _ _).mpr hat
  have hc₁ := (adjacent_act_iff d.radical g⁻¹ _ _).mpr hct
  have hn₁ := selected_ne d.radical hca (S.inv_mem hgS)
  refine ⟨g,hg,x,hx,ha₁,hc₁,hn₁,?_,
    (adjacent_act_iff d.radical x _ _).mpr hc₁,selected_ne d.radical hn₁ hxS,?_,?_,?_⟩
  · rw [←hxa]
    exact (adjacent_act_iff d.radical x _ _).mpr ha₁
  · simpa only [mover_act,inv_inv,hequal] using hgen
  · have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hgen
    have hs : S.map (MulAut.conj x⁻¹).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer (S.inv_mem hxS))
    rw [Subgroup.map_sup,Subgroup.map_sup,hs] at hh
    have hc : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
        MonoidHom.id (FreeAmalgam d.radical) := by
      apply MonoidHom.ext
      intro y
      change x⁻¹*(x*y*x⁻¹)*(x⁻¹)⁻¹ = y
      group
    have hz : ((Z d.radical z).map (MulAut.conj x).toMonoidHom).map
        (MulAut.conj x⁻¹).toMonoidHom = Z d.radical z := by
      rw [Subgroup.map_map,hc,Subgroup.map_id]
    rw [hz] at hh
    simp only [mover_act,inv_inv,hequal]
    rw [sup_assoc,sup_comm (Z d.radical z),←sup_assoc]
    exact hh
  · simpa only [mover_act,inv_inv,hequal] using hfixed

/-- In the cubic-mover, large-image branch, the actual residual
selector gives a shortest backward critical path. The first source
nonnormality is the one constructed by `replacement_exists_critical_neighbor_escape`. -/
theorem Input.replacement_cubic_large_selected_path
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hJc : (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2)) = Nat.card F^3)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2)
    (hlarge : Nat.card F^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical a ∧
      (J.map (MulAut.conj g).toMonoidHom ⊔
        (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom =
        stabilizer d.radical a) ∧
      (∃ back : CriticalPath d.radical geometry (act d.radical g⁻¹ c)
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = act d.radical g⁻¹ t ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
      ¬ V d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
  dsimp only
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
  have hJT : J ≤ Q d.radical t := Subgroup.SmallMover.join_le _ _ _ _
  have hTS : Q d.radical t ≤ stabilizer d.radical a := by
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hQJ : Q d.radical a ≤ J := by
    have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
      (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
      (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
      (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
        (h.replacement_two_group d) (h.replacement_core_le d)))
    rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh
  have hpT : IsPGroup 2 (Q d.radical t) := hjR ▸ (h.replacement_two_group d).map j
  have hpJ : IsPGroup 2 J := hpT.of_injective (inclusion hJT) (inclusion_injective _)
  have hrev := h.replacement_large_critical_reverse_index d path (by omega) hlarge
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hlarge' : Nat.card F < (Q d.radical a).relIndex (Z d.radical z) :=
    lt_of_lt_of_le (by nlinarith : Nat.card F < Nat.card F^2) hrev
  obtain ⟨g,hg,x,hx,hgen,hpair⟩ := h.replacement_cubic_mover_large_selection d
    path hb hlarge' J (hJT.trans hTS) hQJ hpJ hJc hJm
  have hgS := Ltilde_le_stabilizer a hg
  have hga : act d.radical g⁻¹ a = a := (stabilizer d.radical a).inv_mem hgS
  have ha₁ : Adjacent d.radical a (act d.radical g⁻¹ t) := by
    rw [←hga]
    exact (adjacent_act_iff d.radical g⁻¹ _ _).mpr hat
  have hc₁ := (adjacent_act_iff d.radical g⁻¹ _ _).mpr hct
  let Y := Z d.radical (act d.radical g⁻¹ c)
  have hYV : Y ≤ V d.radical a := le_sup_left.trans (neighbor_seed_join_le_radius ha₁ hc₁)
  have hn : ¬ stabilizer d.radical a ≤ normalizer
      ((Y ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    have hh := nonnormal_map_conj (stabilizer d.radical a) (Z d.radical c ⊔ Z d.radical a)
      hnormal hgS
    have hZa : (Z d.radical a).map (MulAut.conj g).toMonoidHom = Z d.radical a := by
      simpa only [hga,inv_inv] using (Z_act d.radical g⁻¹ a).symm
    have hY : Y = (Z d.radical c).map (MulAut.conj g).toMonoidHom := by
      simp only [Y,Z_act,inv_inv]
    rwa [Subgroup.map_sup,←hY,hZa] at hh
  have hJedge : J.map (MulAut.conj g).toMonoidHom ≤ Q d.radical (act d.radical g⁻¹ t) := by
    simpa only [Q_act,inv_inv] using map_mono (f := (MulAut.conj g).toMonoidHom) hJT
  have hnot : ¬ Y ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
    intro htrap
    apply hn
    have hdisp := h.replacement_large_critical_radius_commutator d path hb hlarge
    have hd : ⁅Z d.radical z,Y⁆ ≤ Z d.radical a := by
      rw [commutator_comm]
      exact (commutator_mono (le_inf hYV htrap) le_rfl).trans hdisp
    have hzN := (path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)).trans
      (Z_normalized d.radical a)
    have hzW : Z d.radical z ≤ normalizer ((Y ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      apply le_normalizer_iff.mpr
      intro v hv y hy
      have hm : (Y ⊔ Z d.radical a).map (MulAut.conj v).toMonoidHom ≤ Y ⊔ Z d.radical a := by
        rw [Subgroup.map_sup]
        apply sup_le
        · rintro _ ⟨w,hw,rfl⟩
          have hh := hd (commutator_mem_commutator hv hw)
          change v*w*v⁻¹ ∈ Y ⊔ Z d.radical a
          rw [show v*w*v⁻¹ = ⁅v,w⁆*w by simp [commutatorElement_def,mul_assoc]]
          exact mul_mem (mem_sup_right hh) (mem_sup_left hw)
        · rw [MulEquiv.toMonoidHom_eq_coe,mem_normalizer_iff_map_conj_eq.mp (hzN hv)]
          exact le_sup_right
      exact hm (mem_map_of_mem (MulAut.conj v).toMonoidHom hy)
    rw [←hgen]
    exact sup_le (hJedge.trans (edge_normalizes_neighbor_seed_join ha₁ hc₁)) hzW
  exact ⟨g,hg,x,hx,hgen,hpair,
    exists_backward_path_of_not_le geometry (by omega) path ha₁ hc₁ hnot,
    fun hv => hnot (hYV.trans hv)⟩

/-- The original MS3 neighbor construction discharges nonnormality and
produces the selected backward path in the cubic-mover large-image branch.
No equality of neighboring movers, root restriction or path witness is assumed. -/
theorem Input.replacement_large_cubic_selected_backward_path
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t)
    (hJc : (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2)) = Nat.card F^3)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2)
    (hlarge : Nat.card F^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    ∃ c, Adjacent d.radical c t ∧
      ¬ stabilizer d.radical a ≤ normalizer
        ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical a ∧
      (J.map (MulAut.conj g).toMonoidHom ⊔
        (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom =
        stabilizer d.radical a) ∧
      (∃ back : CriticalPath d.radical geometry (act d.radical g⁻¹ c)
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = act d.radical g⁻¹ t ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
      ¬ V d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
  obtain ⟨c,hct,hn,_,_,_⟩ :=
    h.replacement_exists_critical_neighbor_escape d path (by omega) hat
  exact ⟨c,hct,hn,h.replacement_cubic_large_selected_path d path hb hat hct hn hJc hJm hlarge⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
