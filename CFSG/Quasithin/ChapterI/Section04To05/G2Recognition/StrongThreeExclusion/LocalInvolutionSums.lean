module

public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.LocalCharacters
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.TorusNormalizerStructure
public import Theory.GroupTheory.QuaternionCentralProductInvolutionCensus
public import Theory.GroupTheory.ConjugacyOrderCensus
public import Theory.Character.InvolutionRootPairing

/-!
# Involution counts in the original centralizer

The quaternion core contains nineteen involutions. The outside involutions
form one class, whose centralizer has order eight, and hence there are
seventy-two. These are counts in the actual H of the source configuration.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped BigOperators
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
namespace LocalCharacters
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

private theorem outer_centralizer_card (t : CubicTorus c) :
    Nat.card (Subgroup.centralizer ({t.n} : Set c.H)) = 8 := by
  have he : (Subgroup.centralizer ({t.n} : Set c.H)).map c.H.subtype =
      Subgroup.centralizer (t.torus.map c.H.subtype : Set G) := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩ v ⟨w, hw, rfl⟩
      change ((w * u : c.H) : G) = ((u * w : c.H) : G)
      apply congrArg Subtype.val
      have hz : Commute t.z u := Subtype.ext
        (mem_centralizer_singleton_iff.mp (t.centralizer ▸ u.property)).symm
      have hn : Commute t.n u := (mem_centralizer_singleton_iff.mp hu).symm
      have ht : t.torus ≤ Subgroup.centralizer ({u} : Set c.H) :=
        sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hz))
          (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hn))
      exact mem_centralizer_singleton_iff.mp (ht hw)
    · intro u hu
      have hzA : (t.z : G) ∈ t.torus.map c.H.subtype :=
        mem_map_of_mem _ (mem_sup_left (mem_zpowers _))
      have hnA : (t.n : G) ∈ t.torus.map c.H.subtype :=
        mem_map_of_mem _ (mem_sup_right (mem_zpowers _))
      have huH : u ∈ c.H := t.centralizer.ge
        (mem_centralizer_singleton_iff.mpr (hu _ hzA).symm)
      exact ⟨⟨u, huH⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext (hu _ hnA).symm), rfl⟩
  rw [← card_map_of_injective c.H.subtype_injective, he]
  exact t.torus_centralizer_structure.2

theorem outside_involutions_card :
    Nat.card {x : c.H // orderOf x = 2 ∧ x ∉ quaternionCore c} = 72 := by
  obtain ⟨t⟩ := exists_cubic_torus c
  have hnQ : t.n ∉ quaternionCore c := fun h => t.outside
    ((sup_le_sup (c.H₁.pCoreIn_le 2) (c.H₂.pCoreIn_le 2)) h)
  have hs : {x : c.H | orderOf x = 2 ∧ x ∉ quaternionCore c} =
      (ConjClasses.mk t.n).carrier := by
    ext x
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    constructor
    · rintro ⟨hx, hxQ⟩
      exact (outside_involutions_conjugate c t.n x t.n_order t.outside hx
        (fun hK => hxQ (residual_involution_mem_core c x hx hK))).symm
    · intro hx
      obtain ⟨g, hg⟩ := isConj_iff.mp hx.symm
      have hx2 : orderOf x = 2 := by
        rw [← hg]
        exact ((MulAut.conj g).orderOf_eq t.n).trans t.n_order
      refine ⟨hx2, ?_⟩
      intro hxQ
      apply hnQ
      have hnormal : g ∈ normalizer (quaternionCore c : Set c.H) := by
        rw [(quaternionCore c).normalizer_eq_top]
        trivial
      exact (mem_normalizer_iff.mp hnormal t.n).mpr (hg.symm ▸ hxQ)
  have hcard : Nat.card {x : c.H // orderOf x = 2 ∧ x ∉ quaternionCore c} =
      Nat.card (ConjClasses.mk t.n).carrier := Nat.card_congr (Equiv.setCongr hs)
  have hh := ConjClasses.nat_card_carrier_mul_card_centralizer t.n
  rw [outer_centralizer_card c t, H_card c, ← hcard] at hh
  omega

theorem core_involutions_card :
    Nat.card {x : quaternionCore c // orderOf x = 2} = 19 := by
  let Q := quaternionCore c
  let d := quaternionCoreData c
  let I := {x : Q // orderOf x = 2}
  obtain ⟨z, hz, hzall⟩ := (Nat.card_eq_two_iff' (1 : center Q)).mp d.center_card
  have hz2 : orderOf (z : Q) = 2 :=
    (orderOf_coe z).trans (orderOf_eq_prime (d.center_square z) hz)
  let iz : I := ⟨z, hz2⟩
  have hc : Nat.card {x : I // x.val ∈ center Q} = 1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    refine ⟨⟨?_⟩, ⟨⟨iz, z.property⟩⟩⟩
    intro a b
    have he (x : {x : I // x.val ∈ center Q}) : x.val.val = (z : Q) := by
      have hne : (⟨x.val.val, x.property⟩ : center Q) ≠ 1 := by
        intro hh
        have hx : x.val.val = 1 := congrArg Subtype.val hh
        have ho := x.val.property
        rw [hx, orderOf_one] at ho
        contradiction
      exact congrArg Subtype.val (hzall _ hne)
    exact Subtype.ext (Subtype.ext ((he a).trans (he b).symm))
  have hnc : Nat.card {x : I // x.val ∉ center Q} = 18 := by
    calc
      _ = Nat.card {x : Q // orderOf x = 2 ∧ x ∉ center Q} := Nat.card_congr {
        toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
        invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      _ = 18 := d.noncentral_involutions_card
  have hsplit := Nat.card_congr (Equiv.sumCompl (fun x : I => x.val ∈ center Q))
  rw [Nat.card_sum, hc, hnc] at hsplit
  exact hsplit.symm

private theorem sum_involutions_of_core_values (f : ClassFunction c.H) (a b : ℂ)
    (hin : ∀ x : c.H, orderOf x = 2 → x ∈ quaternionCore c → f x = a)
    (hout : ∀ x : c.H, orderOf x = 2 → x ∉ quaternionCore c → f x = b) :
    Theory.Character.involutionSum f = 19 * a + 72 * b := by
  let : Fintype c.H := Fintype.ofFinite c.H
  let I := {x : c.H // orderOf x = 2}
  let p : I → Prop := fun x => x.val ∈ quaternionCore c
  have hc : Nat.card {x : I // p x} = 19 := by
    calc
      _ = Nat.card {x : quaternionCore c // orderOf x = 2} := Nat.card_congr {
        toFun := fun x => ⟨⟨x.val.val, x.property⟩,
          (orderOf_coe (⟨x.val.val, x.property⟩ : quaternionCore c)).symm.trans x.val.property⟩
        invFun := fun x => ⟨⟨x.val.val, (orderOf_coe x.val).trans x.property⟩, x.val.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      _ = 19 := core_involutions_card c
  have ho : Nat.card {x : I // ¬ p x} = 72 := by
    calc
      _ = Nat.card {x : c.H // orderOf x = 2 ∧ x ∉ quaternionCore c} := Nat.card_congr {
        toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
        invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      _ = 72 := outside_involutions_card c
  unfold Theory.Character.involutionSum
  change (∑ x : I, f x.val) = _
  rw [← (Equiv.sumCompl p).sum_comp (fun x : I => f x.val), Fintype.sum_sum_type]
  have hi (x : {x : I // p x}) : f x.val.val = a := hin _ x.val.property x.property
  have he (x : {x : I // ¬ p x}) : f x.val.val = b := hout _ x.val.property x.property
  simp only [Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, hi, he,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hc, ho]
  norm_num

private theorem quotientMap_core (x : c.H) (hx : x ∈ quaternionCore c) : quotientMap c x = 1 := by
  have hh : QuotientGroup.mk' (quaternionCore c) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  simp only [quotientMap, MonoidHom.comp_apply, hh, map_one]

private theorem outside_sign (x : c.H) (hx : orderOf x = 2) (hQ : x ∉ quaternionCore c) :
    Equiv.Perm.sign (quotientMap c x).val.1 = -1 := by
  change axisSign c 1 x = -1
  have hn : axisSign c 1 x ≠ 1 := by
    intro h
    have hk : x ∈ (axisSign c 1).ker := h
    rw [axisSign_kernel c 1] at hk
    exact hQ (residual_involution_mem_core c x hx hk)
  have hsign : ∀ a : Units ℤ, a = 1 ∨ a = -1 := by decide
  exact (hsign _).resolve_left hn

private instance : DecidablePred (· ∈ LocalCharactersModel.equalSign) :=
  fun _ => inferInstanceAs (Decidable (_ = _))
private instance : Fintype LocalCharactersModel.D := Subtype.fintype _

private theorem row_odd_zero (i : Fin 4) (d : LocalCharactersModel.D)
    (hd : Equiv.Perm.sign d.val.1 = -1) : LocalCharactersModel.row i d = 0 := by
  have h : ∀ (i : Fin 4) (d : LocalCharactersModel.D), Equiv.Perm.sign d.val.1 = -1 →
      LocalCharactersModel.rowValue i d = 0 := by decide +kernel
  simp only [LocalCharactersModel.row, h i d hd, Int.cast_zero]

/-- The actual H has ninety-one involutions. -/
theorem principal_involutionSum : Theory.Character.involutionSum (1 : ClassFunction c.H) = 91 := by
  rw [sum_involutions_of_core_values c 1 1 1 (by intros; rfl) (by intros; rfl)]
  norm_num

/-- Each quadratic row sums to thirty-eight on the actual involutions. -/
theorem localRow_involutionSum (i : Fin 4) : Theory.Character.involutionSum (localRow c i) = 38 := by
  rw [sum_involutions_of_core_values c (localRow c i) 2 0 ?_ ?_]
  · norm_num
  · intro x _ hx
    simp only [localRow, quotientMap_core c x hx, LocalCharactersModel.row_one]
  · intro x hx hQ
    exact row_odd_zero i (quotientMap c x) (outside_sign c x hx hQ)

/-- The linear sign sums to minus fifty-three on the actual involutions. -/
theorem localSign_involutionSum : Theory.Character.involutionSum (localSign c : c.H → ℂ) = -53 := by
  rw [sum_involutions_of_core_values c (localSign c) 1 (-1) ?_ ?_]
  · norm_num
  · intro x _ hx
    simp only [localSign, MonoidHom.comp_apply, quotientMap_core c x hx, map_one]
  · intro x hx hQ
    change ((Equiv.Perm.sign (quotientMap c x).val.1 : ℤ) : ℂ) = -1
    rw [outside_sign c x hx hQ]
    norm_num

/-- The literal local involution-pair pairing, including mixed-order products. -/
theorem localAlpha_involutionPairCount (i : Fin 4) :
    scalarProduct c.H (localAlpha c i)
      (fun x => (Theory.Character.involutionPairCount x : ℂ)) = 18 := by
  rw [localAlpha_eq, scalarProduct_sub_left, scalarProduct_add_left]
  rw [Theory.Character.scalarProduct_irreducible_involutionPairCount _ isIrreducibleCharacter_one,
    Theory.Character.scalarProduct_irreducible_involutionPairCount _ (localSign_linear c).1,
    Theory.Character.scalarProduct_irreducible_involutionPairCount _ (localRow_irreducible c i)]
  rw [principal_involutionSum, localSign_involutionSum, localRow_involutionSum,
    localRow_one, map_one, H_card c]
  norm_num

end LocalCharacters
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
