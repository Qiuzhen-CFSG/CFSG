module
public import Theory.SpecificGroups.AlternatingSix.M10.SolvableResidual
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Transport
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Normal index-two extensions of the actual M₁₀

Restrict automorphisms of M₁₀ to its characteristic inner A₆. For an element of
M₁₀, this restriction is exactly its given automorphism of A₆. Thus conjugation
in a normal index-two extension has kernel disjoint from M₁₀ and of order at
most two. A trivial kernel identifies the extension with Aut(A₆); a kernel of
order two is central and gives the marked direct product C₂ × M₁₀.

Both alternatives retain the original M₁₀ subgroup. No extension recognition
or automorphism-group identification is an input.

Source: Aschbacher–Smith J.2.7(3), printed p.436 (PDF p.447).
-/

open Subgroup
namespace AlternatingSix.M10.IndexTwoExtension
open ShadowLocal

local instance : (inner.subgroupOf extension).Characteristic := by
  rw [← residual_eq_inner]
  infer_instance

noncomputable def restriction : MulAut extension →* AutA6 :=
  (MulAut.congr innerInExtensionEquiv).toMonoidHom.comp
    (MulAut.characteristic (inner.subgroupOf extension))

lemma restriction_conj (m : extension) : restriction (MulAut.conj m) = (m : AutA6) := by
  apply MulEquiv.ext
  intro a
  apply inner_injective
  change MulAut.conj (innerInExtensionEquiv
    (MulAut.characteristic (inner.subgroupOf extension) (MulAut.conj m)
      (innerInExtensionEquiv.symm a))) = MulAut.conj ((m : AutA6) a)
  have h (x : inner.subgroupOf extension) :
      MulAut.conj (innerInExtensionEquiv x) = ((x : extension) : AutA6) := by
    exact congrArg Subtype.val (innerEquiv.apply_symm_apply
      ((subgroupOfEquivOfLe Action.inner_le_extension) x))
  rw [h]
  change (m : AutA6) * (((innerInExtensionEquiv.symm a : inner.subgroupOf extension) :
    extension) : AutA6) * (m : AutA6)⁻¹ = _
  have ha : (((innerInExtensionEquiv.symm a : inner.subgroupOf extension) : extension) :
      AutA6) = MulAut.conj a := by
    exact (h (innerInExtensionEquiv.symm a)).symm.trans
      (congrArg MulAut.conj (innerInExtensionEquiv.apply_symm_apply a))
  rw [ha]
  ext b
  simp


variable {N : Type*} [Group N] (M : Subgroup N) [M.Normal]
    (eM : M ≃* extension)

noncomputable def action : N →* AutA6 :=
  restriction.comp ((MulAut.congr eM).toMonoidHom.comp (MulAut.conjNormal (H := M)))

lemma action_on_subgroup (m : M) : action M eM (m : N) = (eM m : AutA6) := by
  have h : MulAut.congr eM (MulAut.conjNormal (H := M) (m : N)) =
      MulAut.conj (eM m) := by
    ext a
    simp [MulAut.congr, MulAut.conjNormal_val]
  change restriction (MulAut.congr eM (MulAut.conjNormal (H := M) (m : N))) = _
  rw [h, restriction_conj]

lemma action_map_subgroup : M.map (action M eM) = extension := by
  ext a
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [action_on_subgroup M eM ⟨m, hm⟩]
    exact (eM ⟨m, hm⟩).property
  · intro ha
    refine ⟨eM.symm ⟨a, ha⟩, (eM.symm ⟨a, ha⟩).property, ?_⟩
    rw [action_on_subgroup, eM.apply_symm_apply]

lemma disjoint_kernel : Disjoint M (action M eM).ker := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  apply mem_bot.mpr
  have he : eM ⟨x, hx.1⟩ = 1 := Subtype.ext
    ((action_on_subgroup M eM ⟨x, hx.1⟩).symm.trans hx.2)
  exact congrArg Subtype.val (eM.injective (he.trans (map_one eM).symm))

lemma kernel_card_dvd (hi : M.index = 2) : Nat.card (action M eM).ker ∣ 2 := by
  let q : (action M eM).ker →* N ⧸ M :=
    (QuotientGroup.mk' M).comp (action M eM).ker.subtype
  have hq : Function.Injective q := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxM : (x : N) ∈ M := (QuotientGroup.eq_one_iff _).mp hx
    have he : (x : N) = 1 := (disjoint_kernel M eM).le_bot ⟨hxM, x.property⟩
    exact Subtype.ext he
  have h := card_dvd_of_injective q hq
  change Nat.card (action M eM).ker ∣ M.index at h
  rwa [hi] at h

include eM
omit [M.Normal] in
lemma ambient_card (hi : M.index = 2) : Nat.card N = 1440 := by
  rw [← M.index_mul_card, hi, Nat.card_congr eM.toEquiv, Action.card_extension]

variable [Finite N]

/-- The actual normal index-two M₁₀ extension, with its subgroup marking. -/
public theorem marked_dichotomy (hi : M.index = 2) :
    (∃ e : N ≃* AutA6, M.map e.toMonoidHom = extension) ∨
    (∃ e : N ≃* (Multiplicative (ZMod 2) × extension),
      M.map e.toMonoidHom = (⊥ : Subgroup (Multiplicative (ZMod 2))).prod ⊤) := by
  let f := action M eM
  rcases (Nat.dvd_prime Nat.prime_two).mp (kernel_card_dvd M eM hi) with hk | hk
  · have hf : Function.Injective f :=
      (MonoidHom.ker_eq_bot_iff f).mp (Subgroup.card_eq_one.mp hk)
    have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (by
      rw [card_aut, ambient_card M eM hi])
    exact Or.inl ⟨MulEquiv.ofBijective f hbij, action_map_subgroup M eM⟩
  · have hcentral := Subgroup.central_of_normal_card_two f.ker hk
    have hcomm : ∀ (a : f.ker) (b : M), Commute (a : N) (b : N) := by
      intro a b
      exact (mem_center_iff.mp (hcentral a.property) b).symm
    let g : f.ker × M →* N := f.ker.subtype.noncommCoprod M.subtype hcomm
    have hg : Function.Injective g := by
      apply (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr
      refine ⟨Subtype.val_injective, Subtype.val_injective, ?_⟩
      simpa only [range_subtype] using (disjoint_kernel M eM).symm
    have hgcard : Nat.card N ≤ Nat.card (f.ker × M) := by
      rw [ambient_card M eM hi, Nat.card_prod, hk, Nat.card_congr eM.toEquiv,
        Action.card_extension]
    let eg : f.ker × M ≃* N := MulEquiv.ofBijective g (hg.bijective_of_nat_card_le hgcard)
    let ec : f.ker ≃* Multiplicative (ZMod 2) :=
      mulEquivOfPrimeCardEq hk (by simp [Nat.card_eq_fintype_card])
    let e : N ≃* (Multiplicative (ZMod 2) × extension) :=
      eg.symm.trans (MulEquiv.prodCongr ec eM)
    have he (m : M) : e (m : N) = (1, eM m) := by
      have hgm : eg (1, m) = (m : N) := by
        change (1 : N) * m = m
        exact one_mul _
      rw [← hgm]
      change (MulEquiv.prodCongr ec eM) (eg.symm (eg (1, m))) = _
      rw [eg.symm_apply_apply]
      change (ec 1, eM m) = _
      rw [map_one]
    refine Or.inr ⟨e, ?_⟩
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      change e m ∈ _
      rw [he ⟨m, hm⟩]
      exact ⟨rfl, trivial⟩
    · intro hx
      have hx1 : x.1 = 1 := hx.1
      refine ⟨eM.symm x.2, (eM.symm x.2).property, ?_⟩
      change e (eM.symm x.2) = x
      rw [he, eM.apply_symm_apply]
      exact Prod.ext hx1.symm rfl

end AlternatingSix.M10.IndexTwoExtension
