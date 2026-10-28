module

public import Theory.Representation.PSL3Two.FourGroupGeometry.Normalizers

/-!
# Four-group normalizers and pointwise fixers in PSL₃(2)

The proved full automorphism normalizer of an inner four-group is an inner
S₄, with automizer of order six. Its centralizer consequently has order
four and equals that inner four-group. Injectivity of the inner map
identifies the actual group normalizer with this S₄. The canonical
SL₃(2) ≃ PSL₃(2) retains the specified four-group throughout.

Source: Aschbacher--Smith 2.5.8(5), printed p.556.
-/

public section
open Subgroup
namespace Matrix.PSL3Two

private theorem normalizer_map_of_injective {K A : Type*} [Group K] [Group A]
    (F : Subgroup K) (f : K →* A) (hf : Function.Injective f) :
    (normalizer (F : Set K)).map f = f.range ⊓ normalizer (F.map f : Set A) := by
  apply le_antisymm (le_inf (map_le_range _ _) (le_normalizer_map f))
  rintro _ ⟨⟨x, rfl⟩, hx⟩
  refine ⟨x, ?_, rfl⟩
  have hh : (normalizer (F.map f : Set A)).comap f = normalizer (F : Set K) := by
    rw [comap_normalizer_eq_of_le_range (map_le_range _ _), comap_map_eq_self_of_injective hf]
  exact hh ▸ hx

/-- Both assertions for the actual binary special-linear carrier. -/
theorem four_normalizer_and_fixer_SL (F : Subgroup SL) [IsKleinFour F] :
    Nonempty (normalizer (F : Set SL) ≃* Equiv.Perm (Fin 4)) ∧
      ∀ a : MulAut SL, (∀ x ∈ F, a x = x) → ∃ g ∈ F, a = MulAut.conj g := by
  let : IsElementaryAbelian 2 F := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  let J := F.map (MulAut.conj : SL →* MulAut SL)
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.map _
  have hJcard : Nat.card J = 4 := by
    rw [card_map_of_injective MarkedAutomorphisms.conj_injective]
    exact IsKleinFour.card_four
  obtain ⟨hNI, ⟨eN⟩, hact⟩ := BinaryLinearThree.FourGroupGeometry.inner_fourGroup_normalizer
    J (map_le_range _ _) inferInstance hJcard
  have hmap : (normalizer (F : Set SL)).map MulAut.conj = normalizer (J : Set (MulAut SL)) := by
    rw [normalizer_map_of_injective F _ MarkedAutomorphisms.conj_injective]
    exact inf_eq_right.mpr hNI
  refine ⟨⟨((normalizer (F : Set SL)).equivMapOfInjective MulAut.conj
    MarkedAutomorphisms.conj_injective).trans ((MulEquiv.subgroupCongr hmap).trans eN)⟩, ?_⟩
  have hNcard : Nat.card (normalizer (J : Set (MulAut SL))) = 24 := by
    rw [Nat.card_congr eN.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  have hCcard : Nat.card (centralizer (J : Set (MulAut SL))) = 4 := by
    have hc := J.normalizerMonoidHom.ker.card_mul_index
    rw [index_ker, hact, hNcard, normalizerMonoidHom_ker] at hc
    rw [Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (J : Set (MulAut SL)))).toEquiv] at hc
    omega
  have hC : centralizer (J : Set (MulAut SL)) = J :=
    (eq_of_le_of_card_ge J.le_centralizer (by rw [hCcard, hJcard])).symm
  intro a ha
  have hac : a ∈ centralizer (J : Set (MulAut SL)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hh := BinaryLinearThree.FourGroupGeometry.Normalizers.conjugate_conj a x
    rw [ha x hx, mul_inv_eq_iff_eq_mul] at hh
    exact hh.symm
  rw [hC] at hac
  obtain ⟨g, hg, he⟩ := hac
  exact ⟨g, hg, he.symm⟩

/-- Every four-group in PSL₃(2) has actual normalizer S₄. -/
theorem four_normalizer (F : Subgroup PSL) [IsKleinFour F] :
    Nonempty (normalizer (F : Set PSL) ≃* Equiv.Perm (Fin 4)) := by
  let E := F.map equiv.symm.toMonoidHom
  let eF := F.equivMapOfInjective equiv.symm.toMonoidHom equiv.symm.injective
  let : IsKleinFour E := {
    card_four := (Nat.card_congr eF.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eF).symm.trans IsKleinFour.exponent_two }
  obtain ⟨e⟩ := (four_normalizer_and_fixer_SL E).1
  exact ⟨(BinaryLinearThree.FourGroupGeometry.normalizerEquivMap equiv.symm F).trans e⟩

/-- Every pointwise four-group fixer of PSL₃(2) is inner by that four-group. -/
theorem four_fixed_inner (F : Subgroup PSL) [IsKleinFour F]
    (a : MulAut PSL) (ha : ∀ x ∈ F, a x = x) : ∃ g ∈ F, a = MulAut.conj g := by
  let E := F.map equiv.symm.toMonoidHom
  let eF := F.equivMapOfInjective equiv.symm.toMonoidHom equiv.symm.injective
  let : IsKleinFour E := {
    card_four := (Nat.card_congr eF.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eF).symm.trans IsKleinFour.exponent_two }
  let b := MulAut.congr equiv.symm a
  have hb : ∀ x ∈ E, b x = x := by
    rintro _ ⟨x, hx, rfl⟩
    change equiv.symm (a (equiv (equiv.symm x))) = equiv.symm x
    rw [equiv.apply_symm_apply, ha x hx]
  obtain ⟨g, hg, he⟩ := (four_normalizer_and_fixer_SL E).2 b hb
  obtain ⟨x, hx, rfl⟩ := hg
  refine ⟨x, hx, ?_⟩
  ext y
  apply equiv.symm.injective
  have hh := congrArg (fun c : MulAut SL => c (equiv.symm y)) he
  simpa [b, MulAut.congr_apply] using hh

end Matrix.PSL3Two
