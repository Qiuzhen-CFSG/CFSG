module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.CommutingCandidates
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Rigidity of exceptional moved spaces

A shear supported on a space containing the cyclic moved space centralizes
the cyclic actor: its commutator is a shear supported on that smaller space,
so the ambient involution bound kills it. The remaining shear image lies
in the fixed space, giving faithfulness of restriction to any supporting
space of dimension at most twice the cyclic moved dimension.

When the supporting dimension is at most one more than the cyclic moved
dimension, an involution's square-zero displacement and faithful restriction
force its ambient rank to be too small. Thus the actual subgroup acting
trivially modulo an exceptional three-dimensional moved space is an odd
subgroup of GL3(2). Its order divides twenty-one, so it is precisely the
exceptional factor. This proves uniqueness for coincident supports, without
assuming or concluding commutation for different supports.

These are ambient consequences of the input for Aschbacher--Smith E.6.24,
printed p.255. No involution lower bound is transferred to a quotient and
no reconstruction of the unavailable Aschbacher 1981 10.4 proof is claimed.
-/

public section
open Module Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure
open FactorConstruction
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

omit [FiniteDimensional (ZMod 2) W] in
private theorem add_self (v : W) : v + v = 0 := by
  have he : (1 + 1 : ZMod 2) = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun r => r • v) he

omit [FiniteDimensional (ZMod 2) W] in
private theorem square_eq_one_of_shear (hf : Function.Injective ρ)
    (T : Submodule (ZMod 2) W) (q : A)
    (hQ : ∀ v : W, ρ q v - v ∈ T) (hfix : ∀ v ∈ T, ρ q v = v) : q ^ 2 = 1 := by
  apply hf
  ext v
  have he := hfix (ρ q v - v) (hQ v)
  rw [map_sub, sub_eq_iff_eq_add] at he
  simp only [pow_two, map_mul, Module.End.mul_apply, map_one, Module.End.one_apply]
  calc
    _ = (ρ q v - v) + ρ q v := he
    _ = (ρ q v + ρ q v) - v := by abel
    _ = v := by rw [add_self, zero_sub]; exact neg_eq_iff_add_eq_zero.mpr (add_self v)

/-- A shear whose supporting space has dimension at most the actor's moved
space is excluded by the ambient involution bound. -/
theorem Input.eq_one_of_small_shear (h : Input ρ C)
    (T : Submodule (ZMod 2) W) (q : A)
    (hQ : ∀ v : W, ρ q v - v ∈ T) (hfix : ∀ v ∈ T, ρ q v = v)
    (hdim : finrank (ZMod 2) T ≤ finrank (ZMod 2) (displacementSpan ρ C ⊤)) : q = 1 := by
  by_contra hn
  have ho : orderOf q = 2 := orderOf_eq_prime (square_eq_one_of_shear h.faithful T q hQ hfix) hn
  have hb := h.no_small_involutions q ho
  rw [fixedCodim_zpowers_eq_displacement_rank] at hb
  have hr : (ρ q - LinearMap.id).range ≤ T := by
    rintro _ ⟨v, rfl⟩
    exact hQ v
  exact (Nat.not_lt_of_ge ((Submodule.finrank_mono hr).trans hdim)) hb

/-- A shear on a space containing the actor's moved space centralizes the
actor. Its commutator is a shear on the smaller moved space. -/
theorem Input.shear_commutes_actor (h : Input ρ C)
    (T : Submodule (ZMod 2) W) (hST : displacementSpan ρ C ⊤ ≤ T)
    (q : A) (hQ : ∀ v : W, ρ q v - v ∈ T) (hfix : ∀ v ∈ T, ρ q v = v) :
    ∀ c ∈ C, Commute c q := by
  intro c hc
  let N := ρ q - LinearMap.id
  have hNfix (v : W) (hv : v ∈ T) : N v = 0 := sub_eq_zero.mpr (hfix v hv)
  have hNq (v : W) : N (ρ q v) = N v := by
    have he := hNfix (ρ q v - v) (hQ v)
    rw [map_sub, sub_eq_zero] at he
    exact he
  have hNc (v : W) : N (ρ c v) = N v := by
    have he := hNfix (ρ c v - v) (hST (Submodule.subset_span ⟨c, hc, v, Submodule.mem_top, rfl⟩))
    rwa [map_sub, sub_eq_zero] at he
  have hNci (v : W) : N (ρ c⁻¹ v) = N v := by
    have he := hNc (ρ c⁻¹ v)
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] using he.symm
  have hqsq := square_eq_one_of_shear h.faithful T q hQ hfix
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hqsq)
  let r := c * q * c⁻¹ * q⁻¹
  have hr (v : W) : ρ r v - v = ρ c (N v) - N v := by
    have hq (w : W) : ρ q w = w + N w := by dsimp [N]; abel
    change ρ (c * q * c⁻¹ * q⁻¹) v - v = _
    rw [hqi]
    simp only [map_mul, Module.End.mul_apply]
    rw [hq (ρ c⁻¹ (ρ q v)), hNci, hNq, map_add]
    have hcancel (w : W) : ρ c (ρ c⁻¹ w) = w := by
      simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    rw [hcancel, hq v]
    have he := add_self (N v)
    have hn : -N v = N v := neg_eq_iff_add_eq_zero.mpr he
    simp only [sub_eq_add_neg, hn]
    abel
  have hrQ (v : W) : ρ r v - v ∈ displacementSpan ρ C ⊤ := by
    rw [hr]
    exact Submodule.subset_span ⟨c, hc, N v, Submodule.mem_top, rfl⟩
  have hrfix (v : W) (hv : v ∈ displacementSpan ρ C ⊤) : ρ r v = v := by
    apply sub_eq_zero.mp
    rw [hr, hNfix v (hST hv), map_zero, sub_self]
  have hr1 := h.eq_one_of_small_shear (displacementSpan ρ C ⊤) r hrQ hrfix le_rfl
  change c * q = q * c
  have he := congrArg (fun x : A => x * (q * c)) hr1
  simpa only [r, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, one_mul] using he

/-- The actual kernel of the action on the quotient by T. -/
@[expose] def FactorConstruction.quotientFixer (ρ : Representation (ZMod 2) A W)
    (T : Submodule (ZMod 2) W) : Subgroup A where
  carrier := {a | ∀ v : W, ρ a v - v ∈ T}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb v
    have he := T.add_mem (ha (ρ b v)) (hb v)
    simpa only [map_mul, Module.End.mul_apply, sub_add_sub_cancel] using he
  inv_mem' := by
    intro a ha v
    have he := T.neg_mem (ha (ρ a⁻¹ v))
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply, neg_sub] using he

/-- Restriction to T of the subgroup acting trivially on W/T. -/
@[expose] def FactorConstruction.onQuotientFixer (ρ : Representation (ZMod 2) A W)
    (T : Submodule (ZMod 2) W) : Representation (ZMod 2) (quotientFixer ρ T) T :=
  Representation.subrepresentation (ρ.comp (quotientFixer ρ T).subtype) T (by
    intro a v hv
    change ρ (a : A) v ∈ T
    have he := T.add_mem (a.property v) hv
    simpa only [sub_add_cancel] using he)

/-- Faithfulness on a supporting space at most twice the cyclic moved dimension.
A restriction-kernel shear centralizes C and then has image in its fixed space. -/
theorem Input.onQuotientFixer_faithful (h : Input ρ C)
    (T : Submodule (ZMod 2) W) (hST : displacementSpan ρ C ⊤ ≤ T)
    (hdim : finrank (ZMod 2) T ≤ 2 * finrank (ZMod 2) (displacementSpan ρ C ⊤)) :
    Function.Injective (onQuotientFixer ρ T) := by
  apply (injective_iff_map_eq_one _).mpr
  intro q hq
  have hQ : ∀ v : W, ρ (q : A) v - v ∈ T := q.property
  have hfix (v : W) (hv : v ∈ T) : ρ (q : A) v = v := by
    have he := congrArg (fun f : Module.End (ZMod 2) T => f ⟨v, hv⟩) hq
    exact congrArg Subtype.val he
  have hc := h.shear_commutes_actor T hST q hQ hfix
  have hU (v : W) : ρ (q : A) v - v ∈ fixedSpace ρ C := by
    intro c
    have hh := hfix (ρ c v - v)
      (hST (Submodule.subset_span ⟨c, c.property, v, Submodule.mem_top, rfl⟩))
    have he : ρ (c : A) (ρ (q : A) v) = ρ (q : A) (ρ (c : A) v) := by
      simp only [← Module.End.mul_apply, ← map_mul, (hc c c.property).eq]
    change ρ (c : A) (ρ (q : A) v - v) = ρ (q : A) v - v
    rw [map_sub, he]
    rw [map_sub] at hh
    exact sub_eq_sub_iff_add_eq_add.mpr (by
      have hh' := sub_eq_sub_iff_add_eq_add.mp hh
      simpa only [add_comm] using hh')
  have hi : Disjoint (T ⊓ fixedSpace ρ C) (displacementSpan ρ C ⊤) :=
    h.split.disjoint.mono_left inf_le_right
  have he := (T ⊓ fixedSpace ρ C).finrank_sup_add_finrank_inf_eq
    (displacementSpan ρ C ⊤)
  rw [hi.eq_bot, finrank_bot, add_zero] at he
  have hb := Submodule.finrank_mono
    (sup_le (show T ⊓ fixedSpace ρ C ≤ T from inf_le_left) hST)
  have hsmall : finrank (ZMod 2) ↥(T ⊓ fixedSpace ρ C) ≤
      finrank (ZMod 2) (displacementSpan ρ C ⊤) := by omega
  apply Subtype.ext
  exact h.eq_one_of_small_shear (T ⊓ fixedSpace ρ C) q
    (fun v => ⟨hQ v, hU v⟩) (fun v hv => hfix v hv.1) hsmall

variable [Finite A]

/-- The subgroup supported on a space of dimension at most d+1 is odd,
provided that space contains the d-dimensional cyclic moved space. -/
theorem Input.odd_quotientFixer (h : Input ρ C)
    (T : Submodule (ZMod 2) W) (hST : displacementSpan ρ C ⊤ ≤ T)
    (hdim : finrank (ZMod 2) T ≤ finrank (ZMod 2) (displacementSpan ρ C ⊤) + 1) :
    Odd (Nat.card (quotientFixer ρ T)) := by
  have hfaith := h.onQuotientFixer_faithful T hST (by have := h.moved_dimension_gt_one; omega)
  by_contra hodd
  have hdiv : 2 ∣ Nat.card (quotientFixer ρ T) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := quotientFixer ρ T) 2 hdiv
  have htA : orderOf (t : A) = 2 :=
    (orderOf_injective (quotientFixer ρ T).subtype Subtype.val_injective t).trans ht
  let N := ρ (t : A) - LinearMap.id
  have htt (v : W) : ρ (t : A) (ρ (t : A) v) = v := by
    have he : (t : A) ^ 2 = 1 := htA ▸ pow_orderOf_eq_one (t : A)
    simpa only [pow_two, map_mul, Module.End.mul_apply, map_one, Module.End.one_apply]
      using congrArg (fun a => ρ a v) he
  have hNN (v : W) : N (N v) = 0 := by
    change ρ (t : A) (ρ (t : A) v - v) - (ρ (t : A) v - v) = 0
    rw [map_sub, htt]
    calc
      _ = (v + v) - (ρ (t : A) v + ρ (t : A) v) := by abel
      _ = 0 := by rw [add_self, add_self, sub_self]
  have hrle : N.range ≤ T ⊓ N.ker := by
    rintro _ ⟨v, rfl⟩
    exact ⟨t.property v, hNN v⟩
  have hmne : T.map N ≠ ⊥ := by
    intro hm
    have he : onQuotientFixer ρ T t = 1 := by
      ext v
      change ρ (t : A) (v : W) = (v : W)
      apply sub_eq_zero.mp
      have hv := Submodule.mem_map_of_mem (f := N) v.property
      rw [hm] at hv
      exact hv
    have ht1 : t = 1 := (injective_iff_map_eq_one _).mp hfaith t he
    norm_num [ht1] at ht
  have hmpos : 0 < finrank (ZMod 2) (T.map N) := by
    let : Nontrivial (T.map N) := Submodule.nontrivial_iff_ne_bot.mpr hmne
    exact finrank_pos
  have hrT := (N.domRestrict T).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at hrT
  have hker : finrank (ZMod 2) ↥(N.ker.comap T.subtype) =
      finrank (ZMod 2) ↥(T ⊓ N.ker) := by
    rw [← T.map_comap_subtype N.ker, Submodule.finrank_map_subtype_eq]
  rw [hker] at hrT
  have hr := Submodule.finrank_mono hrle
  have hb := h.no_small_involutions (t : A) htA
  rw [fixedCodim_zpowers_eq_displacement_rank] at hb
  change finrank (ZMod 2) (displacementSpan ρ C ⊤) < finrank (ZMod 2) N.range at hb
  omega

/-- An exceptional factor is the full subgroup acting trivially modulo its
moved space. Faithfulness and the ambient involution bound force this subgroup
to be an odd subgroup of GL3(2), hence of order at most twenty-one. -/
theorem ExceptionalCandidate.quotientFixer_moved_eq [Finite W] {B : Subgroup A}
    (hB : ExceptionalCandidate ρ C B) (h : Input ρ C) :
    quotientFixer ρ (displacementSpan ρ B ⊤) = B := by
  let T := displacementSpan ρ B ⊤
  let L := quotientFixer ρ T
  have hST : displacementSpan ρ C ⊤ ≤ T :=
    displacementSpan_mono ρ hB.contained le_rfl
  have hdim := h.moved_finrank_eq_two_of_card_three hB.cyclic_card
  have hTdim : finrank (ZMod 2) T = 3 := hB.moved_dimension
  have hfaith := h.onQuotientFixer_faithful T hST (by omega)
  have hodd := h.odd_quotientFixer T hST (by omega)
  let μ := (onQuotientFixer ρ T).asGroupHom
  have hμ : Function.Injective μ := by
    intro x y he
    apply hfaith
    exact congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) T =>
      (g : Module.End (ZMod 2) T)) he
  let basis := Module.finBasisOfFinrankEq (ZMod 2) T hTdim
  let e : Matrix.PSL3Two.SL ≃* LinearMap.GeneralLinearGroup (ZMod 2) T :=
    Matrix.PSL3Two.equivGL.trans (Matrix.GeneralLinearGroup.toLin' basis)
  have hGL : Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) T) = 168 :=
    (Nat.card_congr e.toEquiv.symm).trans Matrix.PSL3Two.card_SL
  have hdiv : Nat.card L ∣ 168 := hGL ▸ Subgroup.card_dvd_of_injective μ hμ
  have hcop : (Nat.card L).Coprime 8 := by
    simpa using hodd.coprime_two_right.pow_right 3
  have hdiv21 : Nat.card L ∣ 21 := hcop.dvd_of_dvd_mul_right (by simpa using hdiv)
  have hBL : B ≤ L := by
    intro b hb v
    exact Submodule.subset_span ⟨b, hb, v, Submodule.mem_top, rfl⟩
  apply (Subgroup.eq_of_le_of_card_ge hBL ?_).symm
  rw [hB.factor_card]
  exact Nat.le_of_dvd (by decide) hdiv21

/-- Actual order-twenty-one subgroups with moved space contained in that of
an exceptional factor must be that factor. -/
theorem ExceptionalCandidate.eq_of_moved_le [Finite W] {B D : Subgroup A}
    (hB : ExceptionalCandidate ρ C B) (h : Input ρ C)
    (hD : Nat.card D = 21)
    (hDB : displacementSpan ρ D ⊤ ≤ displacementSpan ρ B ⊤) : D = B := by
  have hle : D ≤ B := by
    rw [← hB.quotientFixer_moved_eq h]
    intro d hd v
    exact hDB (Submodule.subset_span ⟨d, hd, v, Submodule.mem_top, rfl⟩)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hD, hB.factor_card])

/-- Equality of moved spaces forces equality of actual conjugate factors.
This excludes coincident supports; it does not assert that different supports
commute or are disjoint. -/
theorem ExceptionalCandidate.conjugate_eq_of_moved_eq [Finite W] {B : Subgroup A}
    (hB : ExceptionalCandidate ρ C B) (h : Input ρ C) (a : A)
    (hT : (displacementSpan ρ B ⊤).map (ρ a) = displacementSpan ρ B ⊤) :
    B.map (MulAut.conj a).toMonoidHom = B := by
  apply hB.eq_of_moved_le h
  · exact (Subgroup.card_map_of_injective (MulAut.conj a).injective).trans hB.factor_card
  · have he := displacementSpan_conjugate ρ B ⊤ a
    rw [map_top_action, hT] at he
    exact he.le

end Representation.RegularCyclicNormalClosure
