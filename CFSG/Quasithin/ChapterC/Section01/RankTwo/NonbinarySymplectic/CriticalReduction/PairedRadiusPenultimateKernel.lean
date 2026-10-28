module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusFixedActor

/-!
# The actual paired penultimate kernel under the small radius budget

Keep the original pair and its source conjugator from the full fixed-actor
construction. Its intersection with the penultimate Q-kernel lies in the
original endpoint stabilizer by the literal path. The exact full root-fixer
formula therefore places this whole kernel in Z_a Q_z. It is unnecessary to
place the whole pair in that stabilizer.

If the same pair had penultimate image at most q, full-cover duality would
put its first kernel in the conjugated second kernel. The actual smaller
mover and both original endpoint conjugates would normalize the first
kernel joined with Z_a, contradicting the retained strict B-index. Thus
this very pair has penultimate image greater than q.

This supplies the full kernel containment in MS93 (5.11), printed p.923.
The source's complementary upper image bound, and hence the strict q-squared
radius exclusion, remain open. Every fixed attachment and the original
pair, field, quotient and smaller movers are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem penultimate_fixed_kernel_le
    {geometry : Geometry d.radical} (p p' : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical)
    (hl : BackwardLink geometry (pairedRadiusChoice geometry (Nat.card F)) p p')
    (hi : (Q d.radical p.last).relIndex (V d.radical p.first) ≤ Nat.card F^2)
    (Y : Subgroup (FreeAmalgam d.radical)) (hY : Y ≤ V d.radical p.first)
    (hfixed : ⁅Y,X d.radical p.last ⊓ Q d.radical p.first⁆=⊥) :
    Y ⊓ Q d.radical p'.last ≤ Z d.radical p.first ⊔ Q d.radical p.last := by
  let W := Z d.radical p.first ⊔ (Y ⊓ Q d.radical p'.last)
  have hK : Y ⊓ Q d.radical p'.last ≤ stabilizer d.radical p.last := by
    apply le_trans ?_ (truncated_radius_le_endpoint_stabilizer p.path (by omega))
    rw [p.path.length_eq_b,←hl.last_eq]
    exact inf_le_inf_right _ hY
  have hZa : Z d.radical p.first ≤ stabilizer d.radical p.last :=
    Z_le_stabilizer_of_dist_le p.first (geometry.exists_critical p.first p.path.start_color)
      p.path.critical.1.le
  have hWC : W ≤ centralizer
      ((X d.radical p.last ⊓ Q d.radical p.first : Subgroup (FreeAmalgam d.radical)) : Set _) :=
    sup_le ((commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes p.first p.path.start_color)).trans (centralizer_le inf_le_right))
      (inf_le_left.trans (commutator_eq_bot_iff_le_centralizer.mp hfixed))
  have hs : (Q d.radical p.last).relIndex (Z d.radical p.first)<Nat.card F^2 := by
    rw [(h.replacement_small_radius_critical_indices d p.path hb hi).1]
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  have he := h.replacement_root_X_intersection_centralizer d p.path (by omega) hs
    W le_sup_left (sup_le hZa hK)
  rw [inf_eq_left.mpr hWC] at he
  exact le_sup_right.trans (he.le.trans (sup_le le_sup_left (inf_le_right.trans le_sup_right)))

/-- On the original paired source selection, the full penultimate kernel
lies in the original seed-kernel product, and that very pair has image
strictly larger than q. Its conjugator, both generating triples, full
fixed equality and original moving index are retained together. -/
theorem Input.replacement_paired_small_radius_penultimate_kernel_and_image
    {geometry : Geometry d.radical} (p p' : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical)
    (hl : BackwardLink geometry (pairedRadiusChoice geometry (Nat.card F)) p p')
    (hi : (Q d.radical p.last).relIndex (V d.radical p.first) ≤ Nat.card F^2) :
    ∃ x ∈ Ltilde d.radical p.first,
      let t := p'.path.walk.getVert 1
      let v := p'.first
      let w := act d.radical x v
      let Y := Z d.radical v ⊔ Z d.radical w
      let J := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical t) (Nat.card F^2)
      let J' := Subgroup.SmallMover.join (U d.radical w) (Q d.radical w)
        (Q d.radical (act d.radical x t)) (Nat.card F^2)
      Adjacent d.radical p.first (act d.radical x t) ∧ Adjacent d.radical w (act d.radical x t) ∧
      (B d.radical p.first (geometry.Z_normal p.first)).relIndex (U d.radical w)=nextMovingIndex p ∧
      (J ⊔ Z d.radical p.last) ⊔ (Z d.radical p.last).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical p.first ∧
      (J' ⊔ Z d.radical p.last) ⊔ (Z d.radical p.last).map (MulAut.conj x⁻¹).toMonoidHom =
        stabilizer d.radical p.first ∧
      (Z d.radical p.first ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓ centralizer (J' : Set _) =
        Z d.radical p.first ⊓ centralizer (stabilizer d.radical p.first : Set (FreeAmalgam d.radical)) ∧
      ⁅Y,X d.radical p.last ⊓ Q d.radical p.first⁆=⊥ ∧
      Y ⊓ Q d.radical p'.last ≤ Z d.radical p.first ⊔ Q d.radical p.last ∧
      Nat.card F < (Q d.radical p'.last).relIndex Y := by
  obtain ⟨x,hx,hatx,hvtx,hix,hgen,hgen',hfixed,hA⟩ :=
    h.replacement_paired_small_radius_fixed_actor d p p' hb hl hi
  refine ⟨x,hx,hatx,hvtx,hix,hgen,hgen',hfixed,hA,?_⟩
  let a := p.first
  let z := p.last
  let v := p'.first
  let w := act d.radical x v
  let e := p'.last
  let Y := Z d.radical v ⊔ Z d.radical w
  let K₁ := Z d.radical v ⊓ Q d.radical e
  let K₂ := Z d.radical w ⊓ Q d.radical e
  let f := (MulAut.conj x).toMonoidHom
  obtain ⟨t,hchoice,hat,hvt,hfirst⟩ := hl.choice
  have hat₀ : Adjacent d.radical a (p'.path.walk.getVert 1) := by rwa [hfirst]
  have hvt₀ : Adjacent d.radical v (p'.path.walk.getVert 1) := by rwa [hfirst]
  have hYV : Y ≤ V d.radical a := sup_le
    (le_sup_left.trans (neighbor_seed_join_le_radius hat₀ hvt₀))
    (le_sup_left.trans (neighbor_seed_join_le_radius hatx hvtx))
  have hplace : Y ⊓ Q d.radical e ≤ Z d.radical a ⊔ Q d.radical z :=
    penultimate_fixed_kernel_le h d p p' hb hl hi Y hYV hA
  refine ⟨hplace,?_⟩
  by_contra! hsmall
  have hxS : x ∈ stabilizer d.radical a := Ltilde_le_stabilizer a hx
  have hZa : (Z d.radical a).map f=Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a hxS)
  have hSa : (stabilizer d.radical a).map f=stabilizer d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical a).le_normalizer hxS)
  let := finite_stabilizer d.radical a
  let : Finite Y := Finite.of_injective
    (inclusion (hYV.trans ((geometry.V_le_Q (by omega) a p.path.start_color).trans
      (fun _ hy => hy.1)))) (inclusion_injective _)
  have hi₁ : (Q d.radical e).relIndex (Z d.radical v) ≤ Nat.card F :=
    (relIndex_le_of_le_right (show Z d.radical v ≤ Y from le_sup_left)
      index_ne_zero_of_finite).trans hsmall
  obtain ⟨hKmap,_⟩ := h.replacement_paired_radius_kernel_conjugate_containment
    d p p' hb hl x hxS hfixed hsmall
  have hK₁ : K₁ ≤ Z d.radical a ⊔ Q d.radical z :=
    (inf_le_inf le_sup_left le_rfl).trans hplace
  have hK₂ : K₂ ≤ Z d.radical a ⊔ Q d.radical z :=
    (inf_le_inf le_sup_right le_rfl).trans hplace
  have haS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a p.path.start_color)
      p.path.critical.1.le
  have hproduct : ⁅Z d.radical a ⊔ Q d.radical z,Z d.radical z⁆ ≤ Z d.radical a := by
    apply commutator_le.mpr
    intro y hy z' hz'
    have hy' : y ∈ (Z d.radical a : Set (FreeAmalgam d.radical))*(Q d.radical z : Set _) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _ (haS.trans (Q_normalized _ z))]
      exact hy
    obtain ⟨u,hu,k,hk,rfl⟩ := hy'
    have hkc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes z p.path.end_color)) hk
    have he : ⁅k,z'⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hkc z' hz').symm
    rw [commutatorElement_mul_left_eq_conj_mul,he,mul_one,mul_inv_cancel,one_mul]
    exact critical_commutator_le_start_seed p.path (commutator_mem_commutator hu hz')
  have hd₁ := (commutator_mono hK₁ le_rfl).trans hproduct
  have hd₂ := map_mono (f := f) ((commutator_mono hK₂ le_rfl).trans hproduct)
  rw [map_commutator,hZa] at hd₂
  have hdmap := (commutator_mono hKmap le_rfl).trans hd₂
  have hzS := p.path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hzmapS : (Z d.radical z).map f ≤ stabilizer d.radical a := by
    have hh := map_mono hzS (f := f)
    rwa [hSa] at hh
  have hn₁ := normalizes_sup_of_displacement _ _ _ (hzS.trans (Z_normalized d.radical a)) hd₁
  have hn₂ := normalizes_sup_of_displacement _ _ _ (hzmapS.trans (Z_normalized d.radical a)) hdmap
  have hJn := h.replacement_backward_small_mover_normalizes_kernel d p p' hb hl hi₁
  have hnormal := hgen ▸ sup_le (sup_le hJn hn₁) hn₂
  exact h.replacement_paired_radius_kernel_not_normal d p hb hchoice hat hvt
    (Q d.radical e) hi₁ hnormal

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
