module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators.Preliminary.Interface
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry.Planes
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct
public import Theory.SpecificGroups.PSL3Two.Parabolics.Actions

/-!
# The line-parabolic displacement on the actual binary natural module

Transitivity on the seven nonzero vectors carries an arbitrary binary line
to the first coordinate axis. The known two-core of its point stabilizer is
the literal translation four-group; its matrices have displacement only in
that axis. Conjugation transports this calculation to every line.

For a marked natural factor, the subgroup of order two is the image of E/N
under the given coordinate homomorphism. Maximality identifies its stabilizer
preimage with P. The image of the normal two-subgroup T lies in the point
radical, and the coordinate kernel pulls the displacement back into E.
Thus the final theorem proves the finite obligation used by Preliminary.

Source: the natural-module consequence in Meierfrankenfeld--Stellmacher
(1993), (4.5.3)(ii), printed p.898; the point-radical model is the existing
Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct calculation.
-/

public section

open Subgroup Matrix
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators
open Escape.Propagation.Backward.Products.Selection.Choices
open FiniteGeometry
namespace NaturalAction

private def line : Subgroup Space where
  carrier := {v | v.toAdd 1 = 0 ∧ v.toAdd 2 = 0}
  one_mem' := by simp
  mul_mem' := by intro x y hx hy; exact ⟨by change x.toAdd 1 + y.toAdd 1 = 0; rw [hx.1,hy.1,add_zero], by change x.toAdd 2 + y.toAdd 2 = 0; rw [hx.2,hy.2,add_zero]⟩
  inv_mem' := by intro x hx; exact ⟨by change -x.toAdd 1 = 0; rw [hx.1,neg_zero], by change -x.toAdd 2 = 0; rw [hx.2,neg_zero]⟩

private theorem line_shape (v : Space) : v ∈ line ↔ v = 1 ∨ v = e0 := by
  have h : ∀ v : Space, (v.toAdd 1 = 0 ∧ v.toAdd 2 = 0) ↔ v = 1 ∨ v = e0 := by decide
  exact h v

private instance : DecidablePred (· ∈ line) := fun v =>
  inferInstanceAs (Decidable (v.toAdd 1 = 0 ∧ v.toAdd 2 = 0))

private theorem line_card : Nat.card line = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem line_stabilizer : planeStabilizer line = PSL3Two.pointParabolicSL := by
  ext g
  rw [mem_planeStabilizer_iff, PSL3Two.mem_pointParabolicSL_iff]
  constructor
  · intro h
    have h0 := h e0 ((line_shape _).mpr (Or.inr rfl))
    have he : ∀ i, (modelAction g e0).toAdd i = g.val i 0 := by
      intro i; simp [e0, mulVec, dotProduct, Fin.sum_univ_three]
    exact ⟨(he 1).symm.trans h0.1, (he 2).symm.trans h0.2⟩
  · intro h v hv
    rcases (line_shape v).mp hv with rfl | rfl
    · rw [map_one]; exact line.one_mem
    · constructor
      · simpa [e0, mulVec, dotProduct, Fin.sum_univ_three] using h.1
      · simpa [e0, mulVec, dotProduct, Fin.sum_univ_three] using h.2

private theorem line_transitive (E : Subgroup Space) (hE : Nat.card E = 2) :
    ∃ g : SL, move g line = E := by
  obtain ⟨u, hune, hunique⟩ := (Nat.card_eq_two_iff' (1 : E)).mp hE
  have hu0 : u.val.toAdd ≠ 0 := fun h => hune (Subtype.ext h)
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq PSL3Two.PSL
    PSL3Two.flagPoint (⟨u.val.toAdd, hu0⟩ : PSL3Two.Fano.Point)
  obtain ⟨g, rfl⟩ := PSL3Two.project_surjective k
  rw [PSL3Two.Fano.project_smul_point] at hk
  have hg : modelAction g e0 = u.val := congrArg Subtype.val hk
  refine ⟨g, eq_of_le_of_card_ge ?_ ?_⟩
  · rintro v ⟨w, hw, rfl⟩
    rcases (line_shape w).mp hw with rfl | rfl
    · simpa only [MonoidHom.coe_coe, map_one] using E.one_mem
    · exact hg ▸ u.property
  · rw [move_card, line_card, hE]

private theorem line_stabilizer_ne_top (E : Subgroup Space) (hE : Nat.card E = 2) :
    planeStabilizer E ≠ ⊤ := by
  obtain ⟨g, rfl⟩ := line_transitive E hE
  rw [planeStabilizer_move, line_stabilizer]
  intro h
  have he := congrArg (Subgroup.comap (MulAut.conj g).toMonoidHom) h
  rw [comap_map_eq_self_of_injective (MulAut.conj g).injective, comap_top] at he
  exact PSL3Two.pointParabolicSL_ne_top he

private theorem core_displacement (T : Subgroup SL) (hT : T ≤ PSL3Two.pointParabolicSL)
    (hn : PSL3Two.pointParabolicSL ≤ normalizer T) (hp : IsPGroup 2 T)
    (t : SL) (ht : t ∈ T) (v : Space) : modelAction t v * v⁻¹ ∈ line := by
  have hc := le_pCoreIn_of_normalizes hp hT hn ht
  rw [PSL3Two.MarkedProduct.pointParabolic_core] at hc
  change PSL3Two.MarkedAutomorphisms.pointCorePred t at hc
  rcases hc with ⟨_, h10, h20, h11, h12, h21, h22⟩
  constructor
  · change t.val.mulVec v.toAdd 1 + -(v.toAdd 1) = 0
    simp [mulVec, dotProduct, Fin.sum_univ_three, h10, h11, h12, CharTwo.add_self_eq_zero]
  · change t.val.mulVec v.toAdd 2 + -(v.toAdd 2) = 0
    simp [mulVec, dotProduct, Fin.sum_univ_three, h20, h21, h22, CharTwo.add_self_eq_zero]

private theorem model_displacement (E : Subgroup Space) (hE : Nat.card E = 2)
    (T : Subgroup SL) (hT : T ≤ planeStabilizer E)
    (hn : planeStabilizer E ≤ normalizer T) (hp : IsPGroup 2 T)
    (t : SL) (ht : t ∈ T) (v : Space) : modelAction t v * v⁻¹ ∈ E := by
  obtain ⟨g, rfl⟩ := line_transitive E hE
  let T₀ := T.map (MulAut.conj g⁻¹).toMonoidHom
  have hmove : (planeStabilizer (move g line)).map (MulAut.conj g⁻¹).toMonoidHom =
      PSL3Two.pointParabolicSL := by
    rw [planeStabilizer_move, line_stabilizer]
    change ((PSL3Two.pointParabolicSL).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = _
    rw [Subgroup.map_map]
    have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id SL := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [he, Subgroup.map_id]
  have hT₀ : T₀ ≤ PSL3Two.pointParabolicSL := (map_mono hT).trans hmove.le
  have hn₀ : PSL3Two.pointParabolicSL ≤ normalizer T₀ := by
    rw [← hmove]
    exact (map_mono hn).trans (le_normalizer_map _)
  have h := core_displacement T₀ hT₀ hn₀ (hp.map _) _
    (mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom ht) (modelAction g⁻¹ v)
  have hm := mem_map_of_mem (modelAction g).toMonoidHom h
  change modelAction g (modelAction (MulAut.conj g⁻¹ t) (modelAction g⁻¹ v) *
    (modelAction g⁻¹ v)⁻¹) ∈ move g line at hm
  have he : modelAction g (modelAction (MulAut.conj g⁻¹ t) (modelAction g⁻¹ v)) =
      modelAction t v := by simp [map_mul, map_inv, MulAut.mul_apply]
  have hcancel : modelAction g (modelAction g⁻¹ v) = v := by
    rw [map_inv, MulAut.apply_inv_self]
  rw [(modelAction g).map_mul, (modelAction g).map_inv, he, hcancel] at hm
  exact hm

end NaturalAction

universe u
/-- The normal two-subgroup of a line parabolic displaces a natural factor only into that line. -/
theorem naturalLineAction : NaturalLineAction.{u} := by
  intro G _ _ π A N P T E hπ hker hP n hNE hEA hindex hPN hTP hPT hp
  let ρ : G →* SL := n.marking.toMonoidHom.comp π
  have hρ : Function.Surjective ρ := n.marking.surjective.comp hπ
  let E₀ := (E.subgroupOf A).map n.coordinates
  have hE₀ : Nat.card E₀ = 2 := by
    rw [← relIndex_ker, n.kernel, relIndex_subgroupOf hEA]
    exact hindex
  have hPB : P ≤ (planeStabilizer E₀).comap ρ := by
    intro g hg
    apply (mem_planeStabilizer_iff _ _).mpr
    rintro v ⟨x, hx, rfl⟩
    let y : A := ⟨g * (x : G) * g⁻¹,
      le_normalizer_iff.mp n.normalized g (mem_top _) x x.property⟩
    have hy : y ∈ E.subgroupOf A := le_normalizer_iff.mp hPN g hg x hx
    have he : modelAction (ρ g) (n.coordinates x) = n.coordinates y :=
      (congrArg Multiplicative.ofAdd (n.action g (mem_top _) x y rfl)).symm
    rw [he]
    exact mem_map_of_mem _ hy
  have hB : (planeStabilizer E₀).comap ρ ≠ ⊤ := by
    intro h
    have he := congrArg (Subgroup.map ρ) h
    rw [map_comap_eq_self_of_surjective hρ, map_top_of_surjective _ hρ] at he
    exact NaturalAction.line_stabilizer_ne_top E₀ hE₀ he
  have hPeq : P = (planeStabilizer E₀).comap ρ := by
    by_contra h
    exact hB (hP.2 _ (lt_of_le_of_ne hPB h))
  have himage : P.map ρ = planeStabilizer E₀ := by
    rw [hPeq, map_comap_eq_self_of_surjective hρ]
  have hTimage : T.map ρ ≤ planeStabilizer E₀ := (map_mono hTP).trans himage.le
  have hnimage : planeStabilizer E₀ ≤ normalizer (T.map ρ) := by
    rw [← himage]
    exact (map_mono hPT).trans (le_normalizer_map ρ)
  have hkernel : n.coordinates.ker ≤ E.subgroupOf A := by
    rw [n.kernel]
    exact subgroupOf_mono A hNE
  have hpre : E₀.comap n.coordinates = E.subgroupOf A := comap_map_eq_self hkernel
  apply commutator_le.mpr
  intro x hx t ht
  let xA : A := ⟨x, hx⟩
  let yA : A := ⟨t * x * t⁻¹,
    le_normalizer_iff.mp n.normalized t (mem_top _) x hx⟩
  have he : n.coordinates yA = modelAction (ρ t) (n.coordinates xA) :=
    congrArg Multiplicative.ofAdd (n.action t (mem_top _) xA yA rfl)
  have hmove := NaturalAction.model_displacement E₀ hE₀ (T.map ρ) hTimage hnimage
    (hp.map ρ) (ρ t) (mem_map_of_mem ρ ht) (n.coordinates xA)
  have hm : n.coordinates (xA * yA⁻¹) ∈ E₀ := by
    rw [map_mul, map_inv, he]
    simpa only [_root_.mul_inv_rev, inv_inv] using E₀.inv_mem hmove
  have hz : xA * yA⁻¹ ∈ E.subgroupOf A := hpre ▸ hm
  change x * (t * x * t⁻¹)⁻¹ ∈ E at hz
  simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc, commutatorElement_def] using hz

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators
