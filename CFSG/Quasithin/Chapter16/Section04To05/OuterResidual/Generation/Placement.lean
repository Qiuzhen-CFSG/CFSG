module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Generation.Field
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Basic
public import Theory.GroupTheory.GeneralizedFitting.FixedNormalizerPlacement
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.SpecificGroups.PSL2.OuterSolvable
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage

/-!
# Component placement for the binary PSL₂ field branch

The actual field action identifies Lᵣ with the simple, perfect fixed subgroup
PSL₂(2^(n/2)), with n/2 ≥ 2. For every involution i in C_{T_C}(r), tight
embedding gives C_G(i) ≤ N_G(L), so C_L(r) is normal in C_{H′}(⟨i,r⟩).
This proves the required relative component assertion.

Take i = z. The proved semilinear automorphism theorem makes Out(L′)
solvable. Applied through the actual quotient H′/K′, perfectness puts Lᵣ
in L′K′. The fixed-normalizer component theorem places it in one factor.
Finally the centralizer-generation equality from Generation.Field and the
noncontainment output of 16.4.2(2) exclude the K′ factor.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the PSL₂
field-involution paragraph in the proof of Lemma 16.4.8, printed p.1188.
The local deduction needs only IntersectionSetup and the actual field-action
witness; the global Hypothesis 16.1.1 has already supplied the earlier setup.
No component-placement or generation certificate is assumed here.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual

private theorem perfect_simple_center {A : Type*} [Group A]
    [IsSimpleGroup A] [Group.IsPerfect A] : center A = ⊥ := by
  rcases (inferInstance : (center A).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp h)).elim

private theorem perfect_simple_quasisimple {A : Type*} [Group A]
    [IsSimpleGroup A] [Group.IsPerfect A] : IsQuasisimple A := by
  refine { simple := ?_ }
  let e : (A ⧸ center A) ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq perfect_simple_center).trans QuotientGroup.quotientBot
  exact (MulEquiv.isSimpleGroup_congr e).mpr inferInstance

private theorem binary_large_field {n : ℕ} (hn : 2 ≤ n) :
    4 ≤ Nat.card (Theory.PSL2.BinaryField n) := by
  rw [GaloisField.card 2 n (by omega)]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn

private theorem charTwo_perfect {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hc : 4 ≤ Nat.card F) : Group.IsPerfect (Theory.PSL2.Group F) := by
  have hu : 1 < Nat.card Fˣ := by
    rw [Nat.card_units]
    omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨u, hu⟩ := exists_ne (1 : Fˣ)
  exact ⟨SL2Simple.PSL_commutator_eq_top ⟨u, u.ne_zero, fun hs =>
    hu (Units.val_eq_one.mp (CharTwo.sq_injective (by simpa using hs)))⟩⟩

private theorem binary_center {n : ℕ} (hn : 2 ≤ n) :
    center (Theory.PSL2.BinaryGroup n) = ⊥ := by
  let := charTwo_perfect (binary_large_field hn)
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (binary_large_field hn)
  exact perfect_simple_center

private theorem binary_outer_solvable {n : ℕ} (hn : 2 ≤ n) :
    Group.IsSolvable (MulAut.Outer (Theory.PSL2.BinaryGroup n)) :=
  Theory.PSL2.OuterSolvable.binary_outer_isSolvable_of_coverage n
    (BenderSuzuki.ZD.Linear.binary_semilinear_coverage hn)

private theorem binary_fixed_quasisimple {n : ℕ} (hn : 2 < n)
    (σ : Theory.PSL2.BinaryField n ≃+* Theory.PSL2.BinaryField n)
    (hσ : orderOf σ = 2) : IsQuasisimple (Theory.PSL2.fieldAut σ).fixedSubgroup := by
  have hs : Function.Involutive σ := by
    intro x
    have hp := pow_orderOf_eq_one σ
    rw [hσ] at hp
    exact DFunLike.congr_fun hp x
  have hne : σ ≠ RingEquiv.refl _ := by
    intro hz
    have hz' : σ = 1 := hz
    rw [hz', orderOf_one] at hσ
    contradiction
  obtain ⟨m, hm, hnm, ⟨e⟩⟩ := Theory.PSL2.binary_fixedField_model (by omega) σ hs hne
  have hc : 4 ≤ Nat.card (FixedBy.subfield (Theory.PSL2.BinaryField n) σ) := by
    rw [Nat.card_congr e.toEquiv]
    exact binary_large_field (by omega)
  let := charTwo_perfect hc
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hc
  let := perfect_simple_quasisimple (A := Theory.PSL2.Group
    (FixedBy.subfield (Theory.PSL2.BinaryField n) σ))
  exact IsQuasisimple.of_mulEquiv (Theory.PSL2.fieldAutFixedEquiv σ).symm

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The actual fixed-field model makes Lᵣ quasisimple. -/
theorem involutionResidual_quasisimple_of_binaryField
    (h : IntersectionSetup T z L g R) (hr : r ∈ R)
    (hfield : IsBinaryFieldInvolution (involutionAction h hr)) :
    IsQuasisimple (involutionResidual L r) := by
  obtain ⟨n, hn, e, σ, hσ, he⟩ := hfield
  let c : (involutionAction h hr).fixedSubgroup ≃*
      (Theory.PSL2.fieldAut σ).fixedSubgroup :=
    (MulAut.fixedSubgroupCongr e (involutionAction h hr)).trans
      (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup he))
  let := binary_fixed_quasisimple hn σ hσ
  let : IsQuasisimple (involutionAction h hr).fixedSubgroup :=
    IsQuasisimple.of_mulEquiv c.symm
  let c' := ComponentTransfer.Intrinsic.centralizerEquivFixed
    (h.sylow_normalizes (h.le_sylow hr))
  let : IsQuasisimple (ComponentTransfer.centralizerIn L r) :=
    IsQuasisimple.of_mulEquiv c'.symm
  have heq : involutionResidual L r = ComponentTransfer.centralizerIn L r :=
    involutionResidual_eq_centralizer_of_binaryField h hr ⟨n, hn, e, σ, hσ, he⟩
  exact IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr heq).symm

private theorem field_disjoint (h : IntersectionSetup T z L g R) (hr : r ∈ R)
    (hfield : IsBinaryFieldInvolution (involutionAction h hr)) :
    Disjoint L (centralizer (L : Set G)) := by
  obtain ⟨n, hn, e, σ, hσ, he⟩ := hfield
  have hc : center L = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hec := (Subgroup.centerCongr e ⟨x, hx⟩).property
    change e x ∈ center (Theory.PSL2.BinaryGroup n) at hec
    rw [binary_center (by omega), mem_bot] at hec
    exact e.injective (hec.trans e.map_one.symm)
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  intro x hx
  have hz : (⟨x, hx.1⟩ : L) ∈ center L :=
    mem_center_iff.mpr fun y => Subtype.ext (hx.2 y y.property)
  exact congrArg L.subtype (mem_bot.mp (hc ▸ hz))

/-- The genuine common centralizer inside the opposite normalizer H′. -/
@[expose] def fieldPairCentralizer (L : Subgroup G) (g i r : G) : Subgroup G :=
  normalizer ((centralizer (L : Set G)).conjBy g : Set G) ⊓
    (involutionCentralizer i ⊓ involutionCentralizer r)

omit [Finite G] in
private theorem pair_centralizer (i r : G) :
    involutionCentralizer i ⊓ involutionCentralizer r = centralizer ({i, r} : Set G) := by
  ext x
  simp [involutionCentralizer, mem_centralizer_iff]

omit [Finite G] in
/-- The displayed intersection is precisely C_H′(⟨i,r⟩). -/
theorem fieldPairCentralizer_eq (L : Subgroup G) (g i r : G) :
    fieldPairCentralizer L g i r =
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) ⊓
        centralizer (closure ({i, r} : Set G) : Set G) := by
  rw [fieldPairCentralizer, centralizer_closure, pair_centralizer]

/-- Normality is relative to C_H′(⟨i,r⟩), and follows from tight embedding. -/
theorem involutionResidual_component_of_binaryField
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hfield : IsBinaryFieldInvolution (involutionAction h hr))
    {i : G} (hi : i ∈ commutingSylow T L ⊓ involutionCentralizer r)
    (hi2 : orderOf i = 2) :
    IsComponentIn (involutionResidual L r) (fieldPairCentralizer L g i r) := by
  let D := involutionResidual L r
  let M := fieldPairCentralizer L g i r
  have hDC : D ≤ involutionCentralizer i := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hi.1.2 x ((involutionResidual_le L r) hx).1)
  have hDM : D ≤ M := le_inf (involutionResidual_le_conjugate_normalizer h hr hr2)
    (le_inf hDC ((involutionResidual_le L r).trans inf_le_right))
  have hMN : M ≤ normalizer (L : Set G) := by
    apply le_trans (show M ≤ involutionCentralizer i from inf_le_right.trans inf_le_left)
    rw [← h.normalizers_eq]
    exact h.tight.involution_centralizer_le_normalizer hi.1.2 hi2
  have hnorm : M ≤ normalizer (D : Set G) := by
    change M ≤ normalizer (involutionResidual L r : Set G)
    rw [involutionResidual_eq_centralizer_of_binaryField h hr hfield]
    exact (le_inf hMN ((show M ≤ involutionCentralizer r from inf_le_right.trans inf_le_right).trans
      (involutionCentralizer r).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  let : (D.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hnorm
  let := involutionResidual_quasisimple_of_binaryField h hr hfield
  exact ⟨hDM, (inferInstance : (D.subgroupOf M).Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hDM).symm⟩

private theorem conjugate_normalizers (h : IntersectionSetup T z L g R) :
    normalizer ((centralizer (L : Set G)).conjBy g : Set G) =
      normalizer (L.conjBy g : Set G) := by
  simp only [conjBy]
  rw [← map_equiv_normalizer_eq _ (MulAut.conj g), h.normalizers_eq,
    map_equiv_normalizer_eq]

omit [Finite G] in
private theorem conjugate_centralizer (L : Subgroup G) (g : G) :
    (centralizer (L : Set G)).conjBy g = centralizer (L.conjBy g : Set G) := by
  rw [conjBy, map_centralizer_equiv]
  rfl

/-- The component placement in the binary field branch of source 16.4.8. -/
theorem involutionResidual_placement_of_binaryField
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hfield : IsBinaryFieldInvolution (involutionAction h hr)) :
    involutionResidual L r ≤ L.conjBy g ∨
      involutionResidual L r ≤ (centralizer (L : Set G)).conjBy g := by
  let A := L.conjBy g
  let B := (centralizer (L : Set G)).conjBy g
  let D := involutionResidual L r
  let M := fieldPairCentralizer L g z r
  have hn : normalizer (B : Set G) = normalizer (A : Set G) := conjugate_normalizers h
  have hBC : B = centralizer (A : Set G) := conjugate_centralizer L g
  have hzK : z ∈ centralizer (L : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp (h.component.1 hx)
  have hzr : z ∈ involutionCentralizer r := by
    apply mem_centralizer_singleton_iff.mpr
    exact (mem_centralizer_singleton_iff.mp (h.sylow_centralizes (h.le_sylow hr))).symm
  have hc : IsComponentIn D M := involutionResidual_component_of_binaryField
    h hr hr2 hfield ⟨⟨h.mem_sylow, hzK⟩, hzr⟩ h.involution
  have hsolv : Group.IsSolvable (MulAut.Outer A) := by
    obtain ⟨n, hn, e, σ, hσ, he⟩ := hfield
    let := binary_outer_solvable (show 2 ≤ n by omega)
    exact MulAut.isSolvable_outer_of_mulEquiv (((MulAut.conj g).subgroupMap L).symm.trans e)
  let := hsolv
  have hd : Disjoint A B := by
    rw [disjoint_iff]
    change L.map (MulAut.conj g).toMonoidHom ⊓
      (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom = ⊥
    rw [← map_inf _ _ _ (MulAut.conj g).injective,
      disjoint_iff.mp (field_disjoint h hr hfield), Subgroup.map_bot]
  have hactorsB : ({z, r} : Set G) ⊆ normalizer (B : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact centralizer_le_conjugate_normalizer h hr hr2 hzr
    · exact B.le_normalizer (h.sylow.le hr).1
  have hactorsA : ({z, r} : Set G) ⊆ normalizer (A : Set G) :=
    fun _ hx => hn ▸ hactorsB hx
  have hc' : IsComponentIn D (normalizer (A : Set G) ⊓ centralizer ({z, r} : Set G)) := by
    simpa only [M, fieldPairCentralizer, conjugate_normalizers h, pair_centralizer] using hc
  have hd' : Disjoint A (centralizer (A : Set G)) := hBC ▸ hd
  exact (hc'.le_or_le_centralizer_of_fixed_normalizer hd' hactorsA).imp
    id (fun hh => hh.trans hBC.ge)

/-- Source 16.4.2(2) excludes the centralizer factor, completing the field branch. -/
theorem involutionResidual_le_conjugate_of_binaryField
    (h : IntersectionSetup T z L g R)
    (hnot : ¬ L ≤ normalizer ((centralizer (L : Set G)).conjBy g : Set G))
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hfield : IsBinaryFieldInvolution (involutionAction h hr)) :
    involutionResidual L r ≤ L.conjBy g :=
  (involutionResidual_placement_of_binaryField h hr hr2 hfield).resolve_right
    (involutionResidual_not_le_conjugate_centralizer h hnot
      (involutionResidual_centralizers_generate_of_binaryField h hr hfield))

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual
