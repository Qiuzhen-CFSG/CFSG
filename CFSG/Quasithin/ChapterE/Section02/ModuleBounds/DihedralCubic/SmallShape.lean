module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.SmallCore
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.WreathOuter
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# The order-six quotient of the marked quaternion pair

Conjugation embeds X/P into Out(P), because P=F*(X) is self-centralizing.
The intrinsic quaternion factors embed Out(P) into S₃ wr C₂. A structural
exponent-twelve bound for this wreath product leaves odd dihedral parameter
one or three; parameter one would make X a two-group, contrary to the
proper two-conjugate generator. Thus the actual quotient X/P is S₃.

Only the two-element top group and six permutations of three letters are
computed. Powers in the wreath product are handled by its base homomorphism.

Source: Aschbacher–Smith, E.2.17, first paragraph, printed p.229. This is used
by SmallCoreAction on the original chosen-module quotient action.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses

private theorem wreath_pow_twelve (a : BinaryFourPlus.Wreath) : a ^ 12 = 1 := by
  let j : (BinaryFourPlus.C2 → Equiv.Perm (Fin 3)) →* BinaryFourPlus.Wreath := {
    toFun u := ⟨u, 1⟩
    map_one' := rfl
    map_mul' u v := by apply RegularWreathProduct.ext <;> simp [RegularWreathProduct.mul_left] }
  have htwo : ∀ q : BinaryFourPlus.C2, q ^ 2 = 1 := by decide +kernel
  have hr : (a ^ 2).right = 1 := by
    change RegularWreathProduct.rightHom (a ^ 2) = 1
    rw [map_pow]
    exact htwo _
  have ha : a ^ 2 = j (a ^ 2).left := by
    apply RegularWreathProduct.ext
    · rfl
    · exact hr
  have hsix : ∀ f : BinaryFourPlus.C2 → Equiv.Perm (Fin 3), f ^ 6 = 1 := by
    intro f
    funext i
    have hp : ∀ a : Equiv.Perm (Fin 3), a ^ 6 = 1 := by decide +kernel
    exact hp (f i)
  change a ^ (2 * 6) = 1
  rw [pow_mul, ha, ← map_pow, hsix, map_one]

private theorem odd_dvd_twelve {m : ℕ} (ho : Odd m) (hd : m ∣ 12) : m = 1 ∨ m = 3 := by
  have hm : m ≤ 12 := Nat.le_of_dvd (by decide) hd
  interval_cases m <;> norm_num at *

variable {X : Type*} [Group X] [Finite X]
variable {T : Sylow 2 X} {V M : Subgroup X} {g : X}

omit [Finite X] in
private theorem outerAction_injective_of_selfcentralizing (N : Subgroup X) [N.Normal]
    (hC : centralizer (N : Set X) ≤ N) : Function.Injective (MulAut.outerAction N) := by
  apply (MonoidHom.ker_eq_bot_iff (MulAut.outerAction N)).mp
  calc
    (MulAut.outerAction N).ker = Subgroup.map (QuotientGroup.mk' N)
        ((MulAut.innerSubgroup N).comap MulAut.conjNormal) :=
      QuotientGroup.ker_map N (MulAut.innerSubgroup N) MulAut.conjNormal _
    _ = ⊥ := by
      rw [MulAut.conjNormal_comap_innerSubgroup, sup_eq_left.mpr hC,
        QuotientGroup.map_mk'_self]

/-- The genuine dihedral quotient of a quaternion pair core has order six. -/
theorem quotient_three_of_quaternion_core
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting X = pCore 2 X)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2)
    (d : QuaternionCentralProductData (P V M g)) :
    letI := h.core_geometry.1
    Nonempty ((X ⧸ P V M g) ≃* DihedralGroup 3) := by
  let := h.core_geometry.1
  obtain ⟨hP, _, m, hm, ho, ⟨e⟩, _⟩ := h.odd_dihedral hcard
  let : NeZero m := ⟨hm.ne'⟩
  have hC : centralizer (P V M g : Set X) ≤ P V M g := by
    rw [hP, ← hfit]
    exact Theory.GroupTheory.centralizer_generalizedFitting_le X
  let f : (X ⧸ P V M g) →* BinaryFourPlus.Wreath :=
    d.outerWreathEmbedding.comp (MulAut.outerAction (P V M g))
  have hf : Function.Injective f := d.outerWreathEmbedding_injective.comp
    (outerAction_injective_of_selfcentralizing (P V M g) hC)
  let x : X ⧸ P V M g := e.symm (DihedralGroup.r 1)
  have hdx : orderOf x = m := by
    exact (orderOf_injective e.toMonoidHom e.injective x).symm.trans
      (by change orderOf (e x) = m; rw [show e x = DihedralGroup.r 1 from e.apply_symm_apply _];
          exact DihedralGroup.orderOf_r_one)
  have hd : m ∣ 12 := by
    rw [← hdx, ← orderOf_injective f hf]
    exact orderOf_dvd_of_pow_eq_one (wreath_pow_twelve (f x))
  have hmalt : m = 1 ∨ m = 3 := odd_dvd_twelve ho hd
  rcases hmalt with hm1 | rfl
  · have hquot : Nat.card (X ⧸ P V M g) = 2 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card, hm1]
    have hX : Nat.card X = 64 := by
      rw [(P V M g).card_eq_card_quotient_mul_card_subgroup, hquot, d.card]
    have hpX : IsPGroup 2 X := IsPGroup.of_card (n := 6) hX
    have hcore : (⊤ : Subgroup X) ≤ pCore 2 X :=
      le_sSup ⟨inferInstance, hpX.of_equiv topEquiv.symm⟩
    exact (h.V_not_le_twoCore hproper (le_top.trans hcore)).elim
  · exact ⟨e⟩

end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
