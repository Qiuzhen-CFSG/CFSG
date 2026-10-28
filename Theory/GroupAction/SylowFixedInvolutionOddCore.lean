module

public import Theory.GroupAction.SylowFixedInvolution
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupTheory.PPrimeCoreReduction

/-!
# Odd cores of centralizers in faithful automorphism overgroups

Let a centerless finite group X have the property that every automorphism
fixing a Sylow two-subgroup pointwise is conjugation by an element of that
Sylow subgroup. If the relevant inner involution centralizers have trivial
odd core, the same holds in any faithful acting group containing Inn(X).

Lift Inn(X) into the acting group and restrict it to the involution
centralizer. This gives a normal subgroup isomorphic to the actual inner
centralizer. Its centralizer fixes the Sylow subgroup pointwise, so the
pointwise-stabilizer hypothesis places it back in that normal subgroup.
The self-centralizing normal-subgroup criterion eliminates the odd core.

This is a conditional finite-group transfer lemma. The model-specific
pointwise-stabilizer and inner-centralizer facts are explicit premises.
Source: the automorphism-centralizer inspection in Aschbacher–Smith,
combined manuscript (1 March 2004), E.6.19, printed p.252 (PDF p.263).
-/

public section

open Subgroup
namespace Theory.GroupAction
variable {X H : Type*} [Group X] [Group H]

private noncomputable def innerLift (φ : H →* MulAut X)
    (hf : Function.Injective φ) (hi : (MulAut.conj : X →* MulAut X).range ≤ φ.range) :
    X →* H :=
  (MonoidHom.ofInjective hf).symm.toMonoidHom.comp
    ((MulAut.conj : X →* MulAut X).codRestrict φ.range (fun x => hi ⟨x, rfl⟩))

private theorem innerLift_apply (φ : H →* MulAut X)
    (hf : Function.Injective φ) (hi : (MulAut.conj : X →* MulAut X).range ≤ φ.range)
    (x : X) : φ (innerLift φ hf hi x) = MulAut.conj x :=
  MonoidHom.apply_ofInjective_symm hf _

private theorem innerLift_injective (φ : H →* MulAut X)
    (hf : Function.Injective φ) (hi : (MulAut.conj : X →* MulAut X).range ≤ φ.range)
    (hc : center X = ⊥) : Function.Injective (innerLift φ hf hi) := by
  intro x y h
  apply MulAut.conj_injective_of_center_eq_bot hc
  simpa only [innerLift_apply] using congrArg φ h

private theorem innerLift_range (φ : H →* MulAut X)
    (hf : Function.Injective φ) (hi : (MulAut.conj : X →* MulAut X).range ≤ φ.range) :
    (innerLift φ hf hi).range = (MulAut.innerSubgroup X).comap φ := by
  ext h
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (innerLift_apply φ hf hi x).symm⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hf ((innerLift_apply φ hf hi x).trans hx)⟩

private theorem aut_conj (a : MulAut X) (x : X) :
    MulAut.conj (a x) = a * MulAut.conj x * a⁻¹ := by
  ext y
  simp

private theorem conj_comm_iff (hc : center X = ⊥) (a : MulAut X) (x : X) :
    MulAut.conj x * a = a * MulAut.conj x ↔ a x = x := by
  constructor
  · intro h
    apply MulAut.conj_injective_of_center_eq_bot hc
    rw [aut_conj, ← h, mul_inv_cancel_right]
  · intro h
    have he := aut_conj a x
    rw [h] at he
    exact eq_mul_inv_iff_mul_eq.mp he

private theorem centralizer_generator {E : Subgroup H} (a : E)
    (ha : ∀ x : E, x ∈ zpowers a) : centralizer (E : Set H) = centralizer ({(a : H)} : Set H) := by
  ext x
  constructor
  · intro hx
    exact mem_centralizer_singleton_iff.mpr (hx a a.property).symm
  · intro hx y hy
    obtain ⟨n, hn⟩ := ha ⟨y, hy⟩
    have he : (a : H) ^ n = y := congrArg Subtype.val hn
    rw [← he]
    exact ((show Commute (a : H) x from (mem_centralizer_singleton_iff.mp hx).symm).zpow_left n).eq

/-- A Sylow pointwise stabilizer contained in inner conjugations, together with
trivial odd cores of the corresponding inner involution centralizers, controls
the centralizer in every faithful overgroup of the inner automorphism group. -/
theorem SylowFixedInvolution.oddCore_eq_bot_of_inner
    [Finite X] [Finite H] {φ : H →* MulAut X} {E : Subgroup H}
    (d : SylowFixedInvolution φ E) (hc : center X = ⊥)
    (hinner : ∀ (S : Sylow 2 X) (a : MulAut X),
      (∀ x ∈ (S : Subgroup X), a x = x) →
      ∃ g ∈ (S : Subgroup X), a = MulAut.conj g)
    (hlocal : ∀ (S : Sylow 2 X) (z : X), orderOf z = 2 →
      (∀ x ∈ (S : Subgroup X), MulAut.conj z x = x) →
      pPrimeCore 2 (centralizer ({z} : Set X)) = ⊥) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  let : IsCyclic E := isCyclic_of_prime_card d.card
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := E)
  have hao : orderOf (a : H) = 2 := by
    rw [orderOf_coe]
    exact (orderOf_eq_card_of_forall_mem_zpowers ha).trans d.card
  rw [centralizer_generator a ha]
  obtain ⟨S, hS⟩ := d.fixes
  obtain ⟨z, _, hz⟩ := hinner S (φ a) (hS a a.property)
  have hzo : orderOf z = 2 := by
    rw [← MulAut.conj_orderOf_of_center_eq_bot hc, ← hz,
      orderOf_injective φ d.faithful]
    exact hao
  have hzfix : ∀ x ∈ (S : Subgroup X), MulAut.conj z x = x := by
    rw [← hz]
    exact hS a a.property
  let f := innerLift φ d.faithful d.inner
  have hf : Function.Injective f := innerLift_injective φ d.faithful d.inner hc
  have hfφ (x : X) : φ (f x) = MulAut.conj x := innerLift_apply φ d.faithful d.inner x
  let C := centralizer ({(a : H)} : Set H)
  let K := centralizer ({z} : Set X)
  have hmem (x : X) : f x ∈ C ↔ x ∈ K := by
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    rw [← d.faithful.eq_iff, map_mul, map_mul, hz, hfφ,
      ← map_mul, ← map_mul, (MulAut.conj_injective_of_center_eq_bot hc).eq_iff]
  let j : K →* C := (f.comp K.subtype).codRestrict C (fun x => (hmem x).mpr x.property)
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  have hjrange : j.range = f.range.subgroupOf C := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, hy⟩
      refine ⟨⟨y, (hmem y).mp (hy ▸ x.property)⟩, ?_⟩
      exact Subtype.ext hy
  have hfn : f.range.Normal := by
    rw [innerLift_range]
    infer_instance
  let : j.range.Normal := by rw [hjrange]; infer_instance
  apply Theory.GroupTheory.pPrimeCore_eq_bot_of_selfCentralizing j.range
  · exact Theory.GroupTheory.pPrimeCore_eq_bot_of_equiv (MonoidHom.ofInjective hj).symm
      (hlocal S z hzo hzfix)
  · intro b hb
    have hbfix : ∀ x ∈ (S : Subgroup X), φ b.val x = x := by
      intro x hx
      have hxK : x ∈ K := by
        exact mem_centralizer_singleton_iff.mpr
          (mul_inv_eq_iff_eq_mul.mp (hzfix x hx)).symm
      have hcomm := hb (j ⟨x, hxK⟩) ⟨⟨x, hxK⟩, rfl⟩
      have he := congrArg (fun c : C => φ c.val) hcomm
      change φ (f x * b.val) = φ (b.val * f x) at he
      rw [map_mul, map_mul, hfφ] at he
      exact (conj_comm_iff hc (φ b.val) x).mp he
    obtain ⟨g, hgS, hg⟩ := hinner S (φ b.val) hbfix
    have hgK : g ∈ K := mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (hzfix g hgS)).symm
    refine ⟨⟨g, hgK⟩, Subtype.ext ?_⟩
    exact d.faithful ((hfφ g).trans hg.symm)

end Theory.GroupAction
