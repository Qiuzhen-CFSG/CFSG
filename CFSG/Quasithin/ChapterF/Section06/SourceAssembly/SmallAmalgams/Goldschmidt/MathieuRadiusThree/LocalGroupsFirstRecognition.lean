module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsFirstBase
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsQuotientRecognition

/-!
# The first radius-three endpoint from its literal source labels

The radius-four label subgroup acts on the six distance-two vertices.
Its kernel is the radius-two elementary eight and its image is S₄.
The source's three distance-four labels map to a transposition chain;
their commutator relations with the eight recognize the actual M₁₂
involution-centralizer endpoint.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(6.12.6), printed p.405.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup SimpleGraph Theory.GroupAction.CubicTree Subgroup.CosetGeometry
open Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
open Theory.SpecificGroups.SymmetricSix.SynthemeCalculation
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

theorem LocalRelations.radiusFour_equiv_firstParabolic
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (a : RankTwo.Vertex F) (ha : a.type = d.side) :
    Nonempty (d.labelBall a 4 ≃* Sporadic.Mathieu.M12SmallPair.firstParabolic) := by
  let K := d.labelBall a 4
  have hK : K ≤ RankTwo.stabilizer F a :=
    d.labelBall_le_stabilizer a 4 (by omega) (by have := h.five_le; omega)
  let : Finite (RankTwo.stabilizer F a) := h.action.finite_stabilizer a
  let : Finite K := Finite.of_injective (Subgroup.inclusion hK) (Subgroup.inclusion_injective hK)
  have hEK : d.labelBall a 2 ≤ K := radiusTwo_le_radiusFour d h.action.toCubicTreeAction (by simp)
  obtain ⟨u,v,A,B,C,R⟩ := r.exists_firstGeometry hr a ha
  have hu : u ∈ K := hEK (R.generators ▸ subset_closure (by simp))
  have hv : v ∈ K := hEK (R.generators ▸ subset_closure (by simp))
  have hz : d.label a ∈ K := d.label_mem_labelBall ha (by simp)
  let uu : K := ⟨u,hu⟩
  let vv : K := ⟨v,hv⟩
  let zz : K := ⟨d.label a,hz⟩
  let aa : K := ⟨A,R.A_mem⟩
  let bb : K := ⟨B,R.B_mem⟩
  let cc : K := ⟨C,R.C_mem⟩
  let ee : K := zz*vv
  let ff : K := uu*vv
  have rb : FirstBaseRelations ee ff aa bb cc zz :=
    FirstBaseRelations.of_injective K.subtype K.subtype_injective R.baseRelations
  have hz1 : zz ≠ 1 := by
    intro hh
    have hh' : d.label a=1 := congrArg Subtype.val hh
    have ho := d.order_two a ha
    rw [hh',orderOf_one] at ho
    omega
  obtain ⟨frame⟩ := h.action.toCubicTreeAction.exists_branchFrame a
  obtain ⟨e⟩ := r.action_image a ha frame
  let φ := r.radiusFour_actionHom hr a ha frame e
  have hker : φ.ker = closure ({ee,ff,zz} : Set K) := by
    rw [r.radiusFour_actionHom_ker hr a ha frame e]
    apply map_injective K.subtype_injective
    rw [map_subgroupOf_eq_of_le hEK, MonoidHom.map_closure,
      Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    exact R.radiusTwo_eq_closure_basis
  have heven := frame.blockAction_even_of_labelBall_card_eight h d hr ha (r.labelBall_card a ha)
  have herange := frame.blockAction_eq_evenModel_of_even h heven
  let eEven : evenModel ≃* Equiv.Perm (Fin 4) :=
    (MulEquiv.subgroupCongr herange.symm).trans e
  have hswap (k : K) (hk2 : k^2=1)
      (hlabel : ∃ b, b.type=d.side ∧ (RankTwo.graph F).dist a b=4 ∧ k.val=d.label b) :
      (φ k).IsSwap := by
    obtain ⟨b,hb,hab,hkb⟩ := hlabel
    let k' : RankTwo.stabilizer F a := Subgroup.inclusion hK k
    have hs := label_branchAction_isSwap h d hr ha hb hab frame k' hkb
    let x : evenModel := ⟨frame.blockAction h.action.toCubicTreeAction k', heven ⟨k',rfl⟩⟩
    have hx : x^2=1 := by
      apply Subtype.ext
      change (frame.blockAction h.action.toCubicTreeAction k')^2=1
      rw [← map_pow]
      have hk' : k'^2=1 := by
        change (Subgroup.inclusion hK k)^2=1
        rw [← map_pow,hk2,map_one]
      rw [hk',map_one]
    exact symmetricFour_isSwap_of_involution_block_swap eEven x hx hs
  exact firstParabolic_equiv_of_base_action ee ff aa bb cc zz rb hz1 φ hker
    (hswap aa rb.A_sq R.A_label) (hswap bb rb.B_sq R.B_label)
    (hswap cc rb.C_sq R.C_label) (r.radiusFour_card_ge hr a ha)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
