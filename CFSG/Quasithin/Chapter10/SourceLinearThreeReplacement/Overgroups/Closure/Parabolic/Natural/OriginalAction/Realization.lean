module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction.Image
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.NaturalFlag.Model

/-!
# Realizing the original factor permutation by binary matrices

Every automorphism of a natural binary three-space is induced by a unique
SL₃(2) matrix. The original maximal local group permutes the two moved
factors. In the preserving case we realize the two restrictions; in the
exchanging case we realize the two maps between the factors. Their literal
coordinate formulas give an element of the regular wreath product. The
faithfulness of its action makes these elementwise realizations a homomorphism.
No splitting or order-two assumption on the specified exchanger is used.

Source: Aschbacher--Smith 10.1.1(3), 10.2.4, pp.741,747.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Matrix IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction
open Chapter3.Section02 Geometry.Escape

private theorem matrix_realization (a : MulAut Eight) :
    ∃ m : Matrix.PSL3Two.SL, ∀ v : Eight,
      Multiplicative.ofAdd (m.val *ᵥ v.toAdd) = a v := by
  obtain ⟨m,rfl⟩ := Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.slAut.surjective a
  refine ⟨m,fun v => ?_⟩
  exact (congrArg Multiplicative.ofAdd
    (Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.slAut_apply m v)).symm

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : SourceLinearThreeSurvivor T D)
  (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)

private theorem preserving_realization (g : localJoin T L)
    (ha : (⁅D.fullModule,L⁆).map (MulAut.conj (g : G)).toMonoidHom = ⁅D.fullModule,L⁆)
    (hb : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).map
      (MulAut.conj (g : G)).toMonoidHom =
        (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) :
    ∃ w : Actor, ∀ v : D.fullModule,
      fullCoordinates s hz (joinAction D g v) = action w (fullCoordinates s hz v) := by
  let ca := movedCoordinates s hz
  let cb := partnerCoordinates s hz
  let ea : (⁅D.fullModule,L⁆ : Subgroup G) ≃* _ :=
    ((MulAut.conj (g : G)).subgroupMap ⁅D.fullModule,L⁆).trans (MulEquiv.subgroupCongr ha)
  let eb : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) ≃* _ :=
    ((MulAut.conj (g : G)).subgroupMap
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)).trans (MulEquiv.subgroupCongr hb)
  obtain ⟨ma,hma⟩ := matrix_realization ((ca.symm.trans ea).trans ca)
  obtain ⟨mb,hmb⟩ := matrix_realization ((cb.symm.trans eb).trans cb)
  refine ⟨⟨fun i => if i = 1 then ma else mb, 1⟩,fun v => ?_⟩
  obtain ⟨⟨a,b⟩,rfl⟩ := (factorProduct s hz).surjective v
  have he : joinAction D g (factorProduct s hz (a,b)) =
      factorProduct s hz (ea a,eb b) := by
    apply Subtype.ext
    rw [joinAction_apply,factorProduct_apply,factorProduct_apply]
    change (g : G) * ((a : G) * b) * (g : G)⁻¹ =
      ((g : G) * a * (g : G)⁻¹) * ((g : G) * b * (g : G)⁻¹)
    group
  rw [he]
  funext i
  rw [coordinates_factorProduct,action_apply]
  simp only [inv_one,one_mul]
  rw [coordinates_factorProduct]
  by_cases hi : i = 1
  · simp only [hi,ite_true]
    have hh := hma (ca a)
    simp only [MulEquiv.trans_apply] at hh
    rw [ca.symm_apply_apply] at hh
    exact hh.symm
  · simp only [hi,if_false]
    have hh := hmb (cb b)
    simp only [MulEquiv.trans_apply] at hh
    rw [cb.symm_apply_apply] at hh
    exact hh.symm

private theorem exchanging_realization (g : localJoin T L)
    (ha : (⁅D.fullModule,L⁆).map (MulAut.conj (g : G)).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)
    (hb : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).map
      (MulAut.conj (g : G)).toMonoidHom = ⁅D.fullModule,L⁆) :
    ∃ w : Actor, ∀ v : D.fullModule,
      fullCoordinates s hz (joinAction D g v) = action w (fullCoordinates s hz v) := by
  let ca := movedCoordinates s hz
  let cb := partnerCoordinates s hz
  let ea : (⁅D.fullModule,L⁆ : Subgroup G) ≃* _ :=
    ((MulAut.conj (g : G)).subgroupMap ⁅D.fullModule,L⁆).trans (MulEquiv.subgroupCongr ha)
  let eb : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) ≃* _ :=
    ((MulAut.conj (g : G)).subgroupMap
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)).trans (MulEquiv.subgroupCongr hb)
  obtain ⟨ma,hma⟩ := matrix_realization ((cb.symm.trans eb).trans ca)
  obtain ⟨mb,hmb⟩ := matrix_realization ((ca.symm.trans ea).trans cb)
  refine ⟨⟨fun i => if i = 1 then ma else mb, other⟩,fun v => ?_⟩
  obtain ⟨⟨a,b⟩,rfl⟩ := (factorProduct s hz).surjective v
  let _ : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  have hcomm : (a : G) * b = (b : G) * a :=
    congrArg Subtype.val (mul_comm
      (⟨a,survivor_moved_le s a.property⟩ : D.fullModule)
      ⟨b,survivor_partner_le s b.property⟩)
  have he : joinAction D g (factorProduct s hz (a,b)) =
      factorProduct s hz (eb b,ea a) := by
    apply Subtype.ext
    rw [joinAction_apply,factorProduct_apply,factorProduct_apply]
    change (g : G) * ((a : G) * b) * (g : G)⁻¹ =
      ((g : G) * b * (g : G)⁻¹) * ((g : G) * a * (g : G)⁻¹)
    rw [hcomm]
    group
  rw [he]
  funext i
  rw [coordinates_factorProduct,action_apply]
  rcases bit_cases i with rfl | rfl
  · simp only [other_inv,mul_one,coordinates_factorProduct,other_ne_one,if_false,ite_true]
    have hh := hma (cb b)
    simp only [MulEquiv.trans_apply] at hh
    rw [cb.symm_apply_apply] at hh
    exact hh.symm
  · simp only [other_inv,other_mul_self,coordinates_factorProduct,other_ne_one,if_false,ite_true]
    have hh := hmb (ca a)
    simp only [MulEquiv.trans_apply] at hh
    rw [ca.symm_apply_apply] at hh
    exact hh.symm

theorem element_realization (g : localJoin T L) :
    ∃ w : Actor, ∀ v : D.fullModule,
      fullCoordinates s hz (joinAction D g v) = action w (fullCoordinates s hz v) := by
  have hgm : (g : G) ∈ D.maximalLocal :=
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) g.property
  have hne : ⁅D.fullModule,L⁆ ≠ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := by
    intro he
    have hd := (survivor_pair_disjoint s hz).eq_bot
    rw [←he,inf_idem] at hd
    have hc := moved_card s hz
    rw [hd,card_bot] at hc
    contradiction
  rcases survivor_moved_pair s g hgm with ha | ha <;>
    rcases Geometry.Escape.partner_pair s g hgm with hb | hb
  · exact (hne (map_injective (MulAut.conj (g : G)).injective (ha.trans hb.symm))).elim
  · exact preserving_realization s hz g ha hb
  · exact exchanging_realization s hz g ha hb
  · exact (hne (map_injective (MulAut.conj (g : G)).injective (ha.trans hb.symm))).elim

def originalLift : LiftData s hz := by
  let w := fun g => Classical.choose (element_realization s hz g)
  have hw (g : localJoin T L) (v : D.fullModule) :
      fullCoordinates s hz (joinAction D g v) = action (w g) (fullCoordinates s hz v) :=
    Classical.choose_spec (element_realization s hz g) v
  refine ⟨{ toFun := w, map_one' := ?_, map_mul' := ?_ },hw⟩
  · apply action_injective
    apply MulEquiv.ext
    intro z
    obtain ⟨v,rfl⟩ := (fullCoordinates s hz).surjective z
    rw [←hw,map_one,map_one]
    rfl
  · intro g h
    apply action_injective
    rw [map_mul]
    apply MulEquiv.ext
    intro z
    obtain ⟨v,rfl⟩ := (fullCoordinates s hz).surjective z
    rw [←hw,map_mul]
    change fullCoordinates s hz (joinAction D g (joinAction D h v)) = _
    rw [hw,hw]
    rfl

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction
