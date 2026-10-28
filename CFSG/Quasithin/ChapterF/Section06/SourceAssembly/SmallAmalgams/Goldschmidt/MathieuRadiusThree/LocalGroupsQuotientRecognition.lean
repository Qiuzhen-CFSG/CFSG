module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsQuotient

/-!
# The faithful symmetric-four quotient of the radius-four label group

The six radius-two groups centered on the second sphere have images of
order two in the quotient by the radius-two group at the center. Each contains
an involution acting as a transposition, and source conjugation permutes
these six groups. Their generation of the radius-four group lets the
six-transposition recognition theorem identify the literal quotient action
with S₄. Thus the source action has exactly the radius-two group as kernel,
and the radius-four label group has order 8 · 24 = 192.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(6.12.6), printed p.405.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup SimpleGraph Theory.GroupAction.CubicTree Subgroup.CosetGeometry
open Theory.SpecificGroups.SymmetricSix.SynthemeCalculation
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

/-- The actual radius-four action, with an arbitrary marking of the even
three-block action by S₄. -/
def LocalRelations.radiusFour_actionHom
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (_r : LocalRelations h d) (hr : d.radius = 3)
    (a : RankTwo.Vertex F) (_ha : a.type = d.side) (f : BranchFrame F a)
    (e : (f.blockAction h.action.toCubicTreeAction).range ≃* Equiv.Perm (Fin 4)) :
    d.labelBall a 4 →* Equiv.Perm (Fin 4) :=
  e.toMonoidHom.comp ((f.blockAction h.action.toCubicTreeAction).rangeRestrict.comp
    (Subgroup.inclusion (d.labelBall_le_stabilizer a 4 (by omega)
      (by have := h.five_le; omega))))

/-- The radius-four labels induce the entire marked symmetric-four action. -/
theorem LocalRelations.radiusFour_actionHom_surjective
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (a : RankTwo.Vertex F) (ha : a.type = d.side) (f : BranchFrame F a)
    (e : (f.blockAction h.action.toCubicTreeAction).range ≃* Equiv.Perm (Fin 4)) :
    Function.Surjective (r.radiusFour_actionHom hr a ha f e) := by
  intro σ
  obtain ⟨u, hu⟩ := e.surjective σ
  obtain ⟨g, hg⟩ := u.property
  obtain ⟨k, hk, he⟩ := r.radiusFour_action_surjective hr ha f g
  refine ⟨⟨k.val,hk⟩, ?_⟩
  change e _ = σ
  rw [← hu]
  congr 1
  apply Subtype.ext
  exact he.trans hg

/-- The radius-two labels at the center act trivially on the second sphere. -/
theorem LocalRelations.radiusTwo_le_actionHom_ker
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (a : RankTwo.Vertex F) (ha : a.type = d.side) (f : BranchFrame F a)
    (e : (f.blockAction h.action.toCubicTreeAction).range ≃* Equiv.Perm (Fin 4)) :
    (d.labelBall a 2).subgroupOf (d.labelBall a 4) ≤
      (r.radiusFour_actionHom hr a ha f e).ker := by
  intro u hu
  have hk := d.labelBall_le_ballKernel h.action.toCubicTreeAction a 2 2
    (by omega) (by have := h.five_le; omega) hu
  let u' : RankTwo.stabilizer F a := Subgroup.inclusion
    (d.labelBall_le_stabilizer a 4 (by omega) (by have := h.five_le; omega)) u
  have hh : u' ∈ (f.blockAction h.action.toCubicTreeAction).ker := by
    rw [f.blockAction_ker h.action.toCubicTreeAction]
    exact hk
  change e ((f.blockAction h.action.toCubicTreeAction).rangeRestrict u') = 1
  rw [← e.map_one]
  congr 1
  apply Subtype.ext
  exact hh

/-- The literal radius-four action has precisely the radius-two label group
as its kernel. The six order-two quotient subgroups eliminate any further kernel. -/
theorem LocalRelations.radiusFour_actionHom_ker
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (a : RankTwo.Vertex F) (ha : a.type = d.side) (f : BranchFrame F a)
    (e : (f.blockAction h.action.toCubicTreeAction).range ≃* Equiv.Perm (Fin 4)) :
    (r.radiusFour_actionHom hr a ha f e).ker =
      (d.labelBall a 2).subgroupOf (d.labelBall a 4) := by
  let K := d.labelBall a 4
  let A := (d.labelBall a 2).subgroupOf K
  let t := h.action.toCubicTreeAction
  have hK : K ≤ RankTwo.stabilizer F a :=
    d.labelBall_le_stabilizer a 4 (by omega) (by have := h.five_le; omega)
  let : Finite (RankTwo.stabilizer F a) := h.action.finite_stabilizer a
  let : Finite K := Finite.of_injective (Subgroup.inclusion hK) (Subgroup.inclusion_injective _)
  let : A.Normal := radiusTwo_normal_in_radiusFour d h hr a
  let π := QuotientGroup.mk' A
  let φ := r.radiusFour_actionHom hr a ha f e
  have hAφ : A ≤ φ.ker := r.radiusTwo_le_actionHom_ker hr a ha f e
  let ψ := QuotientGroup.lift A φ hAφ
  have hψ : Function.Surjective ψ := QuotientGroup.lift_surjective_of_surjective A φ
    (r.radiusFour_actionHom_surjective hr a ha f e) hAφ
  let E : Fin 3 × ZMod 2 → Subgroup K := fun i => (d.labelBall (f.point i) 2).subgroupOf K
  let P : Fin 3 × ZMod 2 → Subgroup (K ⧸ A) := fun i => (E i).map π
  have hpoint (i : Fin 3 × ZMod 2) : (f.point i).type = d.side :=
    ((RankTwo.even_dist_iff F t.generated a (f.point i)).mp
      (by rw [f.point_dist t i]; decide)).symm.trans ha
  have hE (i : Fin 3 × ZMod 2) : d.labelBall (f.point i) 2 ≤ K :=
    radiusTwo_le_radiusFour d t (f.point_dist t i).le
  have hP (i : Fin 3 × ZMod 2) : Nat.card (P i) = 2 :=
    r.radiusTwo_quotient_card hr ha (hpoint i) (f.point_dist t i)
  have heven := f.blockAction_even_of_labelBall_card_eight h d hr ha (r.labelBall_card a ha)
  have herange := f.blockAction_eq_evenModel_of_even h heven
  let ee : evenModel ≃* Equiv.Perm (Fin 4) := (MulEquiv.subgroupCongr herange.symm).trans e
  have hswap (i : Fin 3 × ZMod 2) : ∃ u : K ⧸ A, u ∈ P i ∧ (ψ u).IsSwap := by
    obtain ⟨g,hg,hg2,hgs⟩ := BranchFrame.exists_nearby_label_swap f h d hr ha (f.point_dist t i)
    let k : K := ⟨g.val, hE i hg⟩
    refine ⟨π k, mem_map_of_mem π (show k ∈ E i from hg), ?_⟩
    let x : evenModel := ⟨f.blockAction t g, heven ⟨g,rfl⟩⟩
    have hx : x ^ 2 = 1 := by
      apply Subtype.ext
      change (f.blockAction t g)^2 = 1
      rw [← map_pow, hg2, map_one]
    exact symmetricFour_isSwap_of_involution_block_swap ee x hx hgs
  have hstable : ∀ (g : K ⧸ A) i, ∃ j,
      (P i).map (MulAut.conj g).toMonoidHom = P j := by
    intro g i
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective A g
    let k' : RankTwo.stabilizer F a := Subgroup.inclusion hK k
    let j := f.sphereAction t k' i
    refine ⟨j, ?_⟩
    apply eq_of_le_of_card_ge
    · rintro u ⟨v, ⟨w,hw,rfl⟩, rfl⟩
      have hc : (k : G) * (w : G) * (k : G)⁻¹ ∈ d.labelBall (f.point j) 2 := by
        have hh := radiusTwo_point_map_conj d t f k' i
        rw [← hh]
        exact mem_map.mpr ⟨w.val,hw,rfl⟩
      have heq : (MulAut.conj (π k)) (π w) = π (k*w*k⁻¹) := by
        simp only [MulAut.conj_apply, map_mul, map_inv]
      change (MulAut.conj (π k)) (π w) ∈ P j
      rw [heq]
      exact mem_map_of_mem π hc
    · have hm : Nat.card ((P i).map (MulAut.conj (π k)).toMonoidHom) = Nat.card (P i) :=
        card_map_of_injective (f := (MulAut.conj (π k)).toMonoidHom)
          (MulAut.conj (π k)).injective
      change Nat.card (P j) ≤ Nat.card ((P i).map (MulAut.conj (π k)).toMonoidHom)
      rw [hm, hP, hP]
  have hEgen : (⨆ i, E i) = ⊤ := by
    apply map_injective K.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, K.range_subtype]
    simp only [E, map_subgroupOf_eq_of_le (hE _)]
    exact (radiusFour_eq_iSup_radiusTwo d t ha f).symm
  have hPgen : (⨆ i, P i) = ⊤ := by
    rw [← Subgroup.map_iSup, hEgen, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
  have hbij := Theory.GroupTheory.SymmetricFourCoxeterRecognition.bijective_of_six_conjugate_subgroups
    (by rw [Nat.card_prod, Nat.card_fin, Nat.card_zmod] : Nat.card (Fin 3 × ZMod 2) ≤ 6)
    ψ hψ P hP hswap hstable hPgen
  apply le_antisymm
  · intro u hu
    have he : π u = 1 := hbij.injective (by
      change φ u = ψ 1
      rw [map_one]
      exact hu)
    exact (QuotientGroup.eq_one_iff u).mp he
  · exact hAφ

/-- The radius-four source label group has the exact order of the labelled
M₁₂ parabolic endpoint. -/
theorem LocalRelations.radiusFour_card
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (a : RankTwo.Vertex F) (ha : a.type = d.side) :
    Nat.card (d.labelBall a 4) = 192 := by
  obtain ⟨f⟩ := h.action.toCubicTreeAction.exists_branchFrame a
  obtain ⟨e⟩ := r.action_image a ha f
  let φ := r.radiusFour_actionHom hr a ha f e
  have hker : Nat.card φ.ker = 8 := by
    rw [r.radiusFour_actionHom_ker hr a ha f e]
    exact (Nat.card_congr (subgroupOfEquivOfLe
      (radiusTwo_le_radiusFour d h.action.toCubicTreeAction (by simp))).toEquiv).trans
      (r.labelBall_card a ha)
  have hrange : Nat.card φ.range = 24 := by
    rw [MonoidHom.range_eq_top.mpr (r.radiusFour_actionHom_surjective hr a ha f e)]
    rw [Subgroup.card_top, Nat.card_perm, Nat.card_fin]
    decide
  have hh := φ.ker.card_mul_index
  rw [Subgroup.index_ker, hker, hrange] at hh
  omega

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
