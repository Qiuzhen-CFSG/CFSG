module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.First

/-!
# Absorbing the second-layer displacement into X

A two-group acting on a binary natural plane fixes a nonzero vector, so
its whole displacement lies in that vector's line. If this displacement
escapes a subgroup containing the denominator, its intersection with that
subgroup lies in the denominator.

Apply this to the original X and the transported Y. The marked moving
factor forces the displacement to escape the transported U. Hence U's
displacement lies in the original Z, already contained in the transported
X. A nontrivial two-subgroup normally generates SL₂(2), extending the bound
to the full actor. All normalization is relative to the stated actors.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), the “Moreover” calculation on printed p.907.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Second

private theorem binary_displacement_of_fixed : ∀ (a : SL2) (v w : Fin 2 → ZMod 2),
    v ≠ 0 → a.val.mulVec v = v →
    a.val.mulVec w - w = 0 ∨ a.val.mulVec w - w = v := by decide

private def line (v : Fin 2 → ZMod 2) : Subgroup (Multiplicative (Fin 2 → ZMod 2)) where
  carrier := {x | x = 1 ∨ x = Multiplicative.ofAdd v}
  one_mem' := Or.inl rfl
  mul_mem' := fun {a b} => by
    intro ha hb
    change a = 1 ∨ a = Multiplicative.ofAdd v at ha
    change b = 1 ∨ b = Multiplicative.ofAdd v at hb
    change a * b = 1 ∨ a * b = Multiplicative.ofAdd v
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (by rw [ha,hb,one_mul])
    · exact Or.inr (by rw [ha,hb,one_mul])
    · exact Or.inr (by rw [ha,hb,mul_one])
    · apply Or.inl
      rw [ha,hb]
      exact congrArg Multiplicative.ofAdd
        ((show ∀ w : Fin 2 → ZMod 2, w + w = 0 by decide) v)
  inv_mem' := fun {a} => by
    intro ha
    change a = 1 ∨ a = Multiplicative.ofAdd v at ha
    change a⁻¹ = 1 ∨ a⁻¹ = Multiplicative.ofAdd v
    rcases ha with ha | ha
    · exact Or.inl (by rw [ha, inv_one])
    · apply Or.inr
      rw [ha]
      exact congrArg Multiplicative.ofAdd
        ((show ∀ w : Fin 2 → ZMod 2, -w = w by decide) v)

variable {G : Type*} [Group G]

private theorem small_displacement (P H N E : Subgroup G)
    (n : RankOnePairing.RankOneFactor P H N)
    (hEP : E ≤ P) (hE : IsPGroup 2 E) :
    ∃ v : Fin 2 → ZMod 2, v ≠ 0 ∧
      ⁅H,E⁆ ≤ ((line v).comap n.coordinates).map H.subtype := by
  let : MulAction E (Fin 2 → ZMod 2) := {
    smul := fun e v => (n.projection ⟨e, hEP e.property⟩).val.mulVec v
    one_smul := by
      intro v
      change (n.projection 1).val.mulVec v = v
      rw [map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    mul_smul := by
      intro a b v
      change (n.projection ((⟨a, hEP a.property⟩ : P) * ⟨b, hEP b.property⟩)).val.mulVec v = _
      rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
      rfl }
  obtain ⟨v, hv, hne⟩ := hE.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 2 → ZMod 2)
    (show 2 ∣ Nat.card (Fin 2 → ZMod 2) by norm_num [Nat.card_eq_fintype_card])
    (a := (0 : Fin 2 → ZMod 2)) (by
      apply MulAction.mem_fixedPoints.mpr
      intro e
      change (n.projection ⟨e, hEP e.property⟩).val.mulVec 0 = 0
      exact Matrix.mulVec_zero _)
  refine ⟨v, Ne.symm hne, ?_⟩
  rw [commutator_comm]
  apply commutator_le.mpr
  intro e he y hy
  let a : P := ⟨e, hEP he⟩
  let u : H := ⟨y,hy⟩
  let z : H := ⟨e * y * e⁻¹,
    (mem_normalizer_iff.mp (n.normalized a.property) _).mp hy⟩
  refine ⟨z * u⁻¹, ?_, rfl⟩
  change n.coordinates (z * u⁻¹) = 1 ∨ n.coordinates (z * u⁻¹) = Multiplicative.ofAdd v
  have hd : (n.coordinates (z * u⁻¹)).toAdd =
      (n.projection a).val.mulVec (n.coordinates u).toAdd - (n.coordinates u).toAdd := by
    rw [map_mul, map_inv]
    simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    rw [n.action a u z rfl]
  have hfix : (n.projection a).val.mulVec v = v :=
    MulAction.mem_fixedPoints.mp hv (⟨e,he⟩ : E)
  rcases binary_displacement_of_fixed _ _ _ (Ne.symm hne) hfix with h | h
  · exact Or.inl (Multiplicative.toAdd.injective (hd.trans h))
  · exact Or.inr (Multiplicative.toAdd.injective (hd.trans h))

private theorem displacement_intersection (P H N E U : Subgroup G)
    (n : RankOnePairing.RankOneFactor P H N)
    (hEP : E ≤ P) (hE : IsPGroup 2 E) (hNU : N ≤ U)
    (hnot : ¬ ⁅H,E⁆ ≤ U) : ⁅H,E⁆ ⊓ U ≤ N := by
  obtain ⟨v, _, hv⟩ := small_displacement P H N E n hEP hE
  obtain ⟨b,hb,hbu⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨b',hb',rfl⟩ := hv hb
  have hbv : n.coordinates b' = Multiplicative.ofAdd v := by
    rcases hb' with h | h
    · have hk : b' ∈ n.coordinates.ker := h
      rw [n.kernel] at hk
      exact False.elim (hbu (hNU hk))
    · exact h
  rintro a ⟨ha,hau⟩
  obtain ⟨a',ha',rfl⟩ := hv ha
  rcases ha' with h | h
  · have hk : a' ∈ n.coordinates.ker := h
    rw [n.kernel] at hk
    exact hk
  · have hk : b' * a'⁻¹ ∈ n.coordinates.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, hbv, mul_inv_cancel]
    rw [n.kernel] at hk
    apply False.elim
    apply hbu
    have hh := U.mul_mem (hNU hk) hau
    change ((b' : G) * (a' : G)⁻¹) * (a' : G) ∈ U at hh
    change (b' : G) ∈ U
    simpa only [inv_mul_cancel_right] using hh

private theorem two_power_square (a : SL2) (k : ℕ) (h : a ^ 2 ^ k = 1) : a ^ 2 = 1 := by
  induction k generalizing a with
  | zero =>
    simp only [pow_zero, pow_one] at h
    simp only [h, one_pow]
  | succ k ih =>
    have hh : (a ^ 2) ^ 2 ^ k = 1 := by
      rw [← pow_mul, ← Nat.pow_succ']
      exact h
    exact (show ∀ a : SL2, (a ^ 2) ^ 2 = 1 → a ^ 2 = 1 by decide) a (ih _ hh)

private theorem reflection_words : ∀ (a b : SL2), a ^ 2 = 1 → a ≠ 1 →
    ∃ k : SL2, b = 1 ∨ b = a ∨ b = k * a * k⁻¹ ∨ b = a * (k * a * k⁻¹) := by decide

private theorem normal_generation (P H N K E C : Subgroup G)
    (n : MarkedFactor P H N K) (hEP : E ≤ P) (hE : IsPGroup 2 E)
    (hescape : ¬ E ≤ K) (hPC : P ≤ normalizer C) (hKC : K ≤ C) (hEC : E ≤ C) : P ≤ C := by
  obtain ⟨e,he,hek⟩ := SetLike.not_le_iff_exists.mp hescape
  let a : P := ⟨e,hEP he⟩
  have ha : n.val.projection a ≠ 1 := by
    intro hh
    have hk := MonoidHom.mem_ker.mpr hh
    rw [n.property] at hk
    exact hek hk
  have hs : n.val.projection a ^ 2 = 1 := by
    obtain ⟨k,hk⟩ := hE (⟨e,he⟩ : E)
    have hk' : a ^ 2 ^ k = 1 := Subtype.ext (congrArg (fun u : E => (u : G)) hk)
    exact two_power_square _ k (by rw [← map_pow, hk', map_one])
  intro b hb
  let b' : P := ⟨b,hb⟩
  obtain ⟨k,hw⟩ := reflection_words (n.val.projection a) (n.val.projection b') hs ha
  obtain ⟨k',hk'⟩ := n.val.surjective k
  have hconj : (k' : G) * e * (k' : G)⁻¹ ∈ C :=
    le_normalizer_iff.mp hPC _ k'.property _ (hEC he)
  have lift (w : P) (hwC : (w : G) ∈ C) (hw : n.val.projection b' = n.val.projection w) : b ∈ C := by
    have hh : b' * w⁻¹ ∈ n.val.projection.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hw, mul_inv_cancel]
    rw [n.property] at hh
    have hh' := C.mul_mem (hKC hh) hwC
    change (b * (w : G)⁻¹) * (w : G) ∈ C at hh'
    simpa only [inv_mul_cancel_right] using hh'
  rcases hw with hw | hw | hw | hw
  · exact lift 1 C.one_mem (by simpa only [map_one] using hw)
  · exact lift a (hEC he) hw
  · exact lift (k' * a * k'⁻¹) hconj (by simpa only [map_mul,map_inv,hk'] using hw)
  · exact lift (a * (k' * a * k'⁻¹)) (C.mul_mem (hEC he) hconj)
      (by simpa only [map_mul,map_inv,hk'] using hw)

/-- A small displacement on the original natural factor, together with
nontrivial action on the transported moving factor, absorbs the second
layer's displacement into X. The conclusion is for the full actor. -/
theorem absorption (P Y U K X A E Z : Subgroup G)
    (n : RankOnePairing.RankOneFactor A E Z)
    (m : MarkedFactor P (⁅Y,P⁆ ⊔ U) U K)
    (hYA : Y ≤ A) (hY : IsPGroup 2 Y) (hEP : E ≤ P) (hE : IsPGroup 2 E)
    (hescape : ¬ E ≤ K) (hUY : U ≤ Y) (hXU : X ≤ U) (hZX : Z ≤ X)
    (hPY : P ≤ normalizer Y) (hPU : P ≤ normalizer U) (hPX : P ≤ normalizer X)
    (hUK : ⁅U,K⁆ ≤ X) (hKP : K ≤ P) : ⁅U,P⁆ ≤ X := by
  have hnot : ¬ ⁅E,Y⁆ ≤ U := by
    intro hh
    apply hescape
    apply (markedFactor_commutator_iff m E hEP).mp
    rw [commutator_comm] at hh
    exact (commutator_mono
      (sup_le (le_normalizer_iff_commutator_le_left.mp hPY) hUY) le_rfl).trans hh
  have hi := displacement_intersection A E Z Y U n hYA hY (hZX.trans hXU) hnot
  have hUE : ⁅U,E⁆ ≤ X := by
    apply le_trans _ (hi.trans hZX)
    apply le_inf
    · rw [commutator_comm]
      exact commutator_mono le_rfl hUY
    · exact le_normalizer_iff_commutator_le_left.mp (hEP.trans hPU)
  let C := commutatorPreimage P U X
  have hPC : P ≤ normalizer C :=
    commutatorPreimage_normalized P U X P hPX P.le_normalizer hPU hPX
  have hKC : K ≤ C := le_commutatorPreimage hKP (by rwa [commutator_comm])
  have hEC : E ≤ C := le_commutatorPreimage hEP (by rwa [commutator_comm])
  have hgen := normal_generation P (⁅Y,P⁆ ⊔ U) U K E C m hEP hE hescape hPC hKC hEC
  rw [commutator_comm]
  exact (commutator_mono hgen le_rfl).trans (commutator_commutatorPreimage_le P U X hPX)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Second
