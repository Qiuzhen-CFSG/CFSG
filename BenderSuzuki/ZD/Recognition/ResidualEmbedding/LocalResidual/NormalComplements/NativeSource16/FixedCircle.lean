module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.FieldSource
public import Theory.SpecificGroups.PSL2.InvolutionGeneration
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# The common distinguished circle in Proposition 16.5

The fixed subgroup of the literal conjugation action on a local circle is
identified with the distinguished circle of the common centralizer. The
forward inclusion uses involution generation in characteristic-two PSL₂,
including PSL₂(2); local strong embedding places each involution back in Z.
The reverse inclusion is the defining closure of the same original Z elements.

The source field reduction therefore gives an actual PSL₂ model for that
common circle. Its positive field exponent is unique by the group order
formula, allowing two marked involution centralizers to use the same
square-root parameter.

Source: GLS, *The Classification of the Finite Simple Groups*, volume 4,
Chapter 2, Proposition 16.5, after the choice of W = ⟨u,v⟩.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open RankOneModelGeometry _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The literal fixed subgroup maps onto the distinguished common circle. -/
public theorem source16_fixed_circle_eq
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (F : Subgroup G) (hF : F ≠ ⊤) (hFM : ¬ F ≤ M)
    (hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M) (v : F) {m : ℕ}
    (e : (source16_circleAction h F hFM hne v).fixedSubgroup ≃* PSL2BinaryMatrixGroup m) :
    (source16_circleAction h F hFM hne v).fixedSubgroup.map (localCircleHom Z F) =
      localCircleIn Z (F ⊓ centralizer ({(v : G)} : Set G)) := by
  let C := localCircle Z F
  let a := source16_circleAction h F hFM hne v
  let f := localCircleHom Z F
  let D := F ⊓ centralizer ({(v : G)} : Set G)
  let K := localCircleIn Z D
  let g : a.fixedSubgroup →* G := f.comp a.fixedSubgroup.subtype
  have hgen : closure {x : a.fixedSubgroup | orderOf x = 2} = ⊤ :=
    Theory.PSL2.closure_involutions_eq_top_of_equiv e
  apply le_antisymm
  · have hle : closure {x : a.fixedSubgroup | orderOf x = 2} ≤ K.comap g := by
      apply (closure_le _).mpr
      intro x hx
      have hxC : PFAppendixIII.IsInvolution (x : C) := by
        have ho : orderOf (x : C) = 2 := (Subgroup.orderOf_coe x).trans hx
        exact ⟨(orderOf_eq_prime_iff.mp ho).2,by simpa only [ho] using pow_orderOf_eq_one (x : C)⟩
      have hxZ := localCircle_involution_mem h r F hF hFM hne hxC
      change g x ∈ K
      rw [show K = localCircleIn Z D from rfl,localCircleIn_eq_closure]
      apply Subgroup.subset_closure
      refine ⟨hxZ,⟨(x : C).val.property,?_⟩⟩
      apply mem_centralizer_singleton_iff.mpr
      have he := congrArg f ((MulAut.mem_fixedSubgroup a (x : C)).mp x.property)
      rw [source16_circleAction_apply] at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    rw [hgen] at hle
    rintro y ⟨x,hx,rfl⟩
    exact hle (mem_top (⟨x,hx⟩ : a.fixedSubgroup))
  · rw [localCircleIn_eq_closure]
    apply (closure_le _).mpr
    rintro x ⟨hxZ,hxF,hxv⟩
    let xC : C := ⟨⟨x,hxF⟩,Subgroup.subset_closure hxZ⟩
    refine mem_map.mpr ⟨xC,?_,rfl⟩
    rw [MulAut.mem_fixedSubgroup]
    apply localCircleHom_injective Z F
    rw [source16_circleAction_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hxv).symm

/-- An isomorphism of positive-degree binary PSL₂ models fixes their degree. -/
public theorem source16_binary_parameter_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (e : PSL2BinaryMatrixGroup m ≃* PSL2BinaryMatrixGroup n) : m = n := by
  have hcard (k : ℕ) (hk : 0 < k) : Nat.card (PSL2BinaryMatrixGroup k) =
      2^k * ((2^k)^2-1) := by
    have h := External.huppert614_card_psl_mul_center (K := BinaryGaloisField k)
    rw [External.huppert614_card_center_of_neg_one_eq_one (by simp only [CharTwo.neg_eq]),
      show Nat.card (BinaryGaloisField k) = 2^k from GaloisField.card 2 k (by omega)] at h
    simpa using h
  have he := Nat.card_congr e.toEquiv
  rw [hcard m hm,hcard n hn] at he
  have hm2 : 2 ≤ 2^m := Nat.le_self_pow (by omega) 2
  have hn2 : 2 ≤ 2^n := Nat.le_self_pow (by omega) 2
  have hmono {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
      a*(a^2-1) < b*(b^2-1) := by
    have hp : 0 < a^2-1 := Nat.sub_pos_of_lt (by nlinarith)
    have hsub : a^2-1 ≤ b^2-1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hab.le 2) 1
    exact (Nat.mul_lt_mul_of_pos_right hab hp).trans_le (Nat.mul_le_mul_left b hsub)
  have heq : 2^m = 2^n := by
    rcases lt_trichotomy (2^m) (2^n) with hlt | heq | hgt
    · exact ((Nat.ne_of_lt (hmono hm2 hlt)) he).elim
    · exact heq
    · exact ((Nat.ne_of_lt (hmono hn2 hgt)) he.symm).elim
  exact Nat.pow_right_injective (by decide : 1 < 2) heq

/-- The original 16.5 setup recognizes its common distinguished circle. -/
public theorem source16_square_field_common_circle
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hg : ResidualGeneration Z M)
    {z t u v : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (hzu : Commute z u) (htu : Commute t u)
    (hmax : ∀ w ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution w →
      (residualCentralizerTrace Z M w).ncard ≤ (residualCentralizerTrace Z M u).ncard)
    (hv : PFAppendixIII.IsInvolution v) (hvD : v ∈ residualPairStabilizer M t)
    (hvu : Commute v u) (hzv : Commute z v) (htv : Commute t v) (hnevu : v ≠ u) :
    ∃ m : ℕ, 0 < m ∧
      Nonempty (localCircle Z (centralizer ({u} : Set G)) ≃* PSL2BinaryMatrixGroup (2*m)) ∧
      Nonempty (localCircleIn Z (centralizer ({u} : Set G) ⊓ centralizer ({v} : Set G)) ≃*
        PSL2BinaryMatrixGroup m) := by
  obtain ⟨hBM,hne,m,hm,hmodel,⟨e⟩⟩ := source16_square_field_circle h r ha hg
    hz hzM ht htM hu huD hzu htu hmax hv hvD hvu hzv htv hnevu
  let B := centralizer ({u} : Set G)
  let vB : B := ⟨v,mem_centralizer_singleton_iff.mpr hvu.eq⟩
  let a := source16_circleAction h.disconnected B hBM hne vB
  have heq := source16_fixed_circle_eq h.disconnected r B
    (r.involution_centralizer_ne_top h.disconnected hu) hBM hne vB e
  let em := equivMapOfInjective a.fixedSubgroup (localCircleHom Z B) (localCircleHom_injective Z B)
  exact ⟨m,hm,hmodel,⟨((em.trans (MulEquiv.subgroupCongr heq)).symm).trans e⟩⟩

omit [Finite G] in
/-- Two models of the same marked common circle have equal positive degree. -/
public theorem source16_common_circle_parameter_unique
    (F : Subgroup G) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (em : Nonempty (localCircleIn Z F ≃* PSL2BinaryMatrixGroup m))
    (en : Nonempty (localCircleIn Z F ≃* PSL2BinaryMatrixGroup n)) : m = n := by
  obtain ⟨em⟩ := em
  obtain ⟨en⟩ := en
  exact source16_binary_parameter_eq hm hn (em.symm.trans en)

end BenderSuzuki.ZD
