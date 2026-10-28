module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.SecondField
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.FieldTorus

/-!
# The two field circles with one common field parameter

Four-centralizer generation chooses the second involution. The two literal
fixed circles are the same distinguished common centralizer circle, so their
positive binary degrees agree by the group order formula. Both ambient
tori therefore carry the same square-root Frobenius power. These are the
concrete inputs to the odd Sylow construction in Proposition 16.5.

Source: GLS IV, Chapter 2, Proposition 16.5, equations (16H) and (16I).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open RankOneModelGeometry _root_.BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem marked_four_pair_generates (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) {u v : G} (huW : u ∈ W) (hvW : v ∈ W)
    (hu : PFAppendixIII.IsInvolution u) (hv : PFAppendixIII.IsInvolution v) (hne : v ≠ u) :
    W = zpowers u ⊔ zpowers v := by
  let F := closure ({u,v} : Set G)
  have hc : Commute u v := Subtype.ext_iff.mp (mul_comm (⟨u,huW⟩ : W) ⟨v,hvW⟩)
  let : IsKleinFour F := isKleinFour_closure_pair_of_orderOf u v
    (orderOf_eq_prime hu.sq_eq_one hu.ne_one) (orderOf_eq_prime hv.sq_eq_one hv.ne_one)
    hne.symm hc
  have hFW : F ≤ W := (closure_le _).mpr (by intro x hx; rcases hx with rfl | rfl <;> assumption)
  have hFeq : F = W := eq_of_le_of_card_ge hFW (by rw [hW,show Nat.card F = 4 from IsKleinFour.card_four])
  rw [← hFeq]
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    rcases hx with he | he
    · rw [he]
      exact (le_sup_left : zpowers u ≤ zpowers u ⊔ zpowers v) (mem_zpowers u)
    · rw [Set.mem_singleton_iff.mp he]
      exact (le_sup_right : zpowers v ≤ zpowers u ⊔ zpowers v) (mem_zpowers v)
  · exact sup_le (zpowers_le.mpr (subset_closure (by simp)))
      (zpowers_le.mpr (subset_closure (by simp)))

/-- The source four-group gives two actual field circles over the same
square field, including their literal fixed subgroups and ambient torus actions. -/
public theorem source16_paired_field_circles
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hg : ResidualGeneration Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (hzu : Commute z u) (htu : Commute t u)
    (hmax : ∀ w ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution w →
      (residualCentralizerTrace Z M w).ncard ≤ (residualCentralizerTrace Z M u).ncard)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hWD : W ≤ residualPairStabilizer M t)
    (hWz : W ≤ centralizer ({z} : Set G)) (hWt : W ≤ centralizer ({t} : Set G))
    (huW : u ∈ W) :
    ∃ v ∈ W, PFAppendixIII.IsInvolution v ∧ v ≠ u ∧
      W = zpowers u ⊔ zpowers v ∧
      ∃ (hvu : Commute v u),
      let Bu := centralizer ({u} : Set G)
      let Bv := centralizer ({v} : Set G)
      ∃ (hBu : ¬ Bu ≤ M) (hneU : ∃ z ∈ Z, z ∈ Bu ∧ z ∈ M)
        (hBv : ¬ Bv ≤ M) (hneV : ∃ z ∈ Z, z ∈ Bv ∧ z ∈ M),
      let au := source16_circleAction h.disconnected Bu hBu hneU
        ⟨v,mem_centralizer_singleton_iff.mpr hvu.eq⟩
      let av := source16_circleAction h.disconnected Bv hBv hneV
        ⟨u,mem_centralizer_singleton_iff.mpr hvu.symm.eq⟩
      ∃ m : ℕ, 0 < m ∧
        Nonempty (localCircle Z Bu ≃* PSL2BinaryMatrixGroup (2*m)) ∧
        Nonempty (localCircle Z Bv ≃* PSL2BinaryMatrixGroup (2*m)) ∧
        Nonempty (au.fixedSubgroup ≃* PSL2BinaryMatrixGroup m) ∧
        Nonempty (av.fixedSubgroup ≃* PSL2BinaryMatrixGroup m) ∧
        au ^ 2 = 1 ∧ (¬ ∃ g, au = MulAut.conj g) ∧
        av ^ 2 = 1 ∧ (¬ ∃ g, av = MulAut.conj g) ∧
        (let Du := residualPairStabilizer M t ⊓ localCircleIn Z Bu
         IsCyclic Du ∧ Nat.card Du = 2^(2*m)-1 ∧
           (∀ x ∈ Du, t*x*t⁻¹=x⁻¹) ∧ (∀ x ∈ Du, v*x*v⁻¹=x^(2^m))) ∧
        (let Dv := residualPairStabilizer M t ⊓ localCircleIn Z Bv
         IsCyclic Dv ∧ Nat.card Dv = 2^(2*m)-1 ∧
           (∀ x ∈ Dv, t*x*t⁻¹=x⁻¹) ∧ (∀ x ∈ Dv, u*x*u⁻¹=x^(2^m))) := by
  obtain ⟨v,hvW,hv,hvuNe,huBv,hBv,hneV,mv,hmv,⟨ev⟩,⟨efv⟩⟩ :=
    source16_exists_second_square_field_circle h r ha hg hz hzM ht htM hu hzu htu
      W hW hWD hWz hWt huW
  have hvu : Commute v u := Subtype.ext_iff.mp (mul_comm (⟨v,hvW⟩ : W) ⟨u,huW⟩)
  have hzv : Commute z v := (mem_centralizer_singleton_iff.mp (hWz hvW)).symm
  have htv : Commute t v := (mem_centralizer_singleton_iff.mp (hWt hvW)).symm
  obtain ⟨hBu,hneU,mu,hmu,⟨eu⟩,⟨efu⟩⟩ := source16_square_field_circle h r ha hg
    hz hzM ht htM hu huD hzu htu hmax hv (hWD hvW) hvu hzv htv hvuNe
  let Bu := centralizer ({u} : Set G)
  let Bv := centralizer ({v} : Set G)
  let au := source16_circleAction h.disconnected Bu hBu hneU
    ⟨v,mem_centralizer_singleton_iff.mpr hvu.eq⟩
  let av := source16_circleAction h.disconnected Bv hBv hneV
    ⟨u,mem_centralizer_singleton_iff.mpr hvu.symm.eq⟩
  have heU := source16_fixed_circle_eq h.disconnected r Bu
    (r.involution_centralizer_ne_top h.disconnected hu) hBu hneU
    ⟨v,mem_centralizer_singleton_iff.mpr hvu.eq⟩ efu
  have heV := source16_fixed_circle_eq h.disconnected r Bv
    (r.involution_centralizer_ne_top h.disconnected hv) hBv hneV
    ⟨u,mem_centralizer_singleton_iff.mpr hvu.symm.eq⟩ efv
  change av.fixedSubgroup.map (localCircleHom Z Bv) = localCircleIn Z (Bv ⊓ Bu) at heV
  rw [inf_comm Bv Bu] at heV
  let emU := equivMapOfInjective au.fixedSubgroup (localCircleHom Z Bu) (localCircleHom_injective Z Bu)
  let emV := equivMapOfInjective av.fixedSubgroup (localCircleHom Z Bv) (localCircleHom_injective Z Bv)
  let ecU : localCircleIn Z (Bu ⊓ Bv) ≃* PSL2BinaryMatrixGroup mu :=
    ((emU.trans (MulEquiv.subgroupCongr heU)).symm).trans efu
  let ecV : localCircleIn Z (Bu ⊓ Bv) ≃* PSL2BinaryMatrixGroup mv :=
    ((emV.trans (MulEquiv.subgroupCongr heV)).symm).trans efv
  have heqm := source16_binary_parameter_eq hmu hmv (ecU.symm.trans ecV)
  subst mv
  have hgeomU := source16_field_torus_geometry h r ha Bu
    (r.involution_centralizer_ne_top h.disconnected hu) hBu hneU hz
    (mem_centralizer_singleton_iff.mpr hzu.eq) hzM ht
    (mem_centralizer_singleton_iff.mpr htu.eq) htM
    (source16_centralizer_nonsolvable h r ha ht htM hu huD)
    ⟨v,mem_centralizer_singleton_iff.mpr hvu.eq⟩ hv (hWD hvW).1 hzv htv hmu eu efu
  have hgeomV := source16_field_torus_geometry h r ha Bv
    (r.involution_centralizer_ne_top h.disconnected hv) hBv hneV hz
    (mem_centralizer_singleton_iff.mpr hzv.eq) hzM ht
    (mem_centralizer_singleton_iff.mpr htv.eq) htM
    (source16_centralizer_nonsolvable h r ha ht htM hv (hWD hvW))
    ⟨u,mem_centralizer_singleton_iff.mpr hvu.symm.eq⟩ hu huD.1 hzu htu hmu ev efv
  exact ⟨v,hvW,hv,hvuNe,marked_four_pair_generates W hW huW hvW hu hv hvuNe,hvu,hBu,hneU,hBv,hneV,mu,hmu,⟨eu⟩,⟨ev⟩,⟨efu⟩,⟨efv⟩,
    hgeomU.1,hgeomU.2.1,hgeomV.1,hgeomV.2.1,hgeomU.2.2,hgeomV.2.2⟩

end BenderSuzuki.ZD
