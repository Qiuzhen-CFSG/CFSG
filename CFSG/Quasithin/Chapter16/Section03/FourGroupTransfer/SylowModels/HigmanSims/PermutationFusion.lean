module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.ModelFacts
public import CFSG.Quasithin.Chapter16.Section03.Basic
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Enumeration
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Marking
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner

/-!
# Fusion of alternating Sylow involutions in HS

The noncentral HS involution class is fixed-point-free on the 100 letters.
A two-group whose order does not divide 100 has an involution fixing a letter.
For A₆, its Sylow subgroup has order eight and all involutions are conjugate.
For A₈, use the regular elementary abelian group of order eight. Its seven
involutions have support eight, as does every nonidentity central element of
an A₈ Sylow subgroup: that Sylow acts transitively on the eight letters.
Alternating-group conjugacy then puts each required involution in the HS class
of e₀. These arguments apply to every embedding, without a centralizer table.

Source: Aschbacher–Smith, proof of 16.3.4, printed p.1178. This proof uses the
certified degree-100 HS action and the alternating conjugacy criterion.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
namespace HSPermutationFusion
open Subgroup
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage

private theorem exists_involution_fixed {D X : Type*} [Group D] [Finite D] [MulAction D X]
    [Finite X] (hp : IsPGroup 2 D) (hcard : ¬ Nat.card D ∣ Nat.card X) :
    ∃ d : D, orderOf d = 2 ∧ ∃ x : X, d • x = x := by
  classical
  by_contra! hn
  have hf (x : X) : MulAction.stabilizer D x = ⊥ := by
    rcases (hp.to_subgroup (MulAction.stabilizer D x)).card_eq_or_dvd with h | h
    · exact card_eq_one.mp h
    · obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' 2 h
      exact (hn d ((orderOf_injective (MulAction.stabilizer D x).subtype Subtype.val_injective d).trans hd) x d.property).elim
  have hc := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hf)
  rw [Nat.card_prod] at hc
  exact hcard ⟨Nat.card (Quotient (MulAction.orbitRel D X)), by rw [hc, Nat.mul_comm]⟩

private theorem has_fixedPoint_of_isConj {x y : Carrier} (h : IsConj x y)
    (hx : ∃ p : Fin 100, inclusion x p = p) : ∃ p : Fin 100, inclusion y p = p := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  obtain ⟨p, hp⟩ := hx
  refine ⟨inclusion g p, ?_⟩
  have he : y * g = g * x := ((mul_inv_eq_iff_eq_mul).mp hg).symm
  have hh := congrArg (fun u : Carrier => inclusion u p) he
  simpa only [map_mul, Equiv.Perm.mul_apply, hp] using hh

private theorem central_class_of_fixedPoint {x : Carrier} (hx : orderOf x = 2)
    (hf : ∃ p : Fin 100, inclusion x p = p) : IsConj e0 x := by
  rcases involution_classes x hx with h | h
  · exact h
  · obtain ⟨p, hp⟩ := has_fixedPoint_of_isConj h.symm hf
    exact (t_fixedPointFree p hp).elim

private theorem a6_involution_fixed (f : alternatingGroup (Fin 6) →* Carrier)
    (x : alternatingGroup (Fin 6)) (hx : orderOf x = 2) :
    ∃ p : Fin 100, inclusion (f x) p = p := by
  let P : Sylow 2 (alternatingGroup (Fin 6)) := default
  let a : P →* Equiv.Perm (Fin 100) := (inclusion.comp f).comp (P : Subgroup (alternatingGroup (Fin 6))).subtype
  let : MulAction P (Fin 100) := MulAction.compHom (Fin 100) a
  have hcard : ¬ Nat.card P ∣ Nat.card (Fin 100) := by
    rw [AlternatingSix.ShadowLocal.alternatingSylow_card, Nat.card_fin]
    decide
  obtain ⟨y, hy, p, hp⟩ := exists_involution_fixed P.isPGroup' hcard
  have hy' : orderOf (y : alternatingGroup (Fin 6)) = 2 := (orderOf_injective (P : Subgroup (alternatingGroup (Fin 6))).subtype Subtype.val_injective y).trans hy
  have hc := AlternatingSix.ShadowLocal.involutions_isConj (y : alternatingGroup (Fin 6)) x hy' hx
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  apply has_fixedPoint_of_isConj (x := f y) (y := f x) _ ⟨p, hp⟩
  exact isConj_iff.mpr ⟨f g, by simpa only [map_mul, map_inv] using congrArg f hg⟩
namespace Eight
private abbrev A8 := alternatingGroup (Fin 8)
private def tr (i : Fin 8) : Equiv.Perm (Fin 8) where
  toFun := fun j => i ^^^ j
  invFun := fun j => i ^^^ j
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

private theorem tr_even (i : Fin 8) : tr i ∈ alternatingGroup (Fin 8) := by
  apply Equiv.Perm.mem_alternatingGroup.mpr
  revert i
  decide +kernel

private def a (i : Fin 8) : A8 := ⟨tr i, tr_even i⟩

private def E : Subgroup A8 where
  carrier := Set.range a
  one_mem' := ⟨0, by decide +kernel⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    refine ⟨i ^^^ j, ?_⟩
    revert i j
    decide +kernel
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    revert i
    decide +kernel

private theorem E_card : Nat.card E = 8 := by
  let f : Fin 8 → E := fun i => ⟨a i, ⟨i, rfl⟩⟩
  have hi : Function.Injective f := by
    intro i j h
    have he := congrArg (fun z : E => z.val.val 0) h
    change tr i 0 = tr j 0 at he
    have ht : ∀ k : Fin 8, tr k 0 = k := by decide +kernel
    simpa only [ht] using he
  have hs : Function.Surjective f := by
    rintro ⟨_, i, rfl⟩
    exact ⟨i, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)).symm.trans (Nat.card_fin 8)

private theorem E_two : IsPGroup 2 E := IsPGroup.of_card (show Nat.card E = 2 ^ 3 from E_card)

private theorem transitive (P : Sylow 2 A8) (p q : Fin 8) :
    ∃ g : A8, g ∈ (P : Subgroup A8) ∧ g.val p = q := by
  obtain ⟨Q, hQ⟩ := E_two.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A8 Q P
  let u := a (g.val.symm q ^^^ g.val.symm p)
  have hu : u ∈ (Q : Subgroup A8) := hQ ⟨_, rfl⟩
  refine ⟨g * u * g⁻¹, ?_, ?_⟩
  · rw [← hg]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom hu
  · change g.val (tr (g.val.symm q ^^^ g.val.symm p) (g.val.symm p)) = q
    have ht : ∀ x y : Fin 8, tr (y ^^^ x) x = y := by decide +kernel
    rw [ht, g.val.apply_symm_apply]

private theorem center_fixedPointFree (P : Sylow 2 A8) (x : P) (hx : x ∈ center P)
    (hne : (x : A8) ≠ 1) : ∀ p : Fin 8, x.val.val p ≠ p := by
  intro p hp
  apply hne
  apply Subtype.ext
  apply Equiv.ext
  intro q
  obtain ⟨g, hg, he⟩ := transitive P p q
  have hc := congrArg (fun y : P => y.val.val p) (mem_center_iff.mp hx ⟨g, hg⟩)
  change g.val (x.val.val p) = x.val.val (g.val p) at hc
  simpa only [hp, he, coe_one, Equiv.Perm.one_apply] using hc.symm

private theorem center_support (P : Sylow 2 A8) (x : P) (hx : x ∈ center P)
    (hne : (x : A8) ≠ 1) : x.val.val.support.card = 8 := by
  have h : x.val.val.support = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro p
    exact Equiv.Perm.mem_support.mpr (center_fixedPointFree P x hx hne p)
  rw [h]
  rfl

private theorem E_support (x : E) (hx : orderOf x = 2) : x.val.val.support.card = 8 := by
  obtain ⟨i, hi⟩ := x.property
  have hn : i ≠ 0 := by
    intro h
    have he : x = 1 := Subtype.ext (hi.symm.trans (h ▸ show a 0 = 1 by decide +kernel))
    simp [he] at hx
  change x.val.val.support.card = 8
  rw [← hi]
  have h : ∀ i : Fin 8, i ≠ 0 → (a i).val.support.card = 8 := by decide +kernel
  exact h i hn
end Eight

private theorem a8_sylow_involution_fixed (f : Eight.A8 →* Carrier)
    (P : Sylow 2 Eight.A8) (x : P) (hx : x ∈ center P)
    (ho : orderOf (x : Eight.A8) = 2) :
    ∃ p : Fin 100, inclusion (f x) p = p := by
  let a : Eight.E →* Equiv.Perm (Fin 100) := (inclusion.comp f).comp Eight.E.subtype
  let : MulAction Eight.E (Fin 100) := MulAction.compHom (Fin 100) a
  have hcard : ¬ Nat.card Eight.E ∣ Nat.card (Fin 100) := by
    rw [Eight.E_card, Nat.card_fin]
    decide
  obtain ⟨y, hy, p, hp⟩ := exists_involution_fixed Eight.E_two hcard
  have hy' : orderOf (y : Eight.A8) = 2 :=
    (orderOf_injective Eight.E.subtype Subtype.val_injective y).trans hy
  have hne : (x : Eight.A8) ≠ 1 := by intro h; simp [h] at ho
  have hyne : (y : Eight.A8) ≠ 1 := by intro h; simp [h] at hy'
  have hc : IsConj (y : Eight.A8) (x : Eight.A8) :=
    GLS3.Chapter5.SchurPresentation.alternating_involution_isConj_of_card_support_eq
      (congrArg Subtype.val (orderOf_eq_prime_iff.mp hy').1)
      (congrArg Subtype.val (orderOf_eq_prime_iff.mp ho).1) hyne
      ((Eight.E_support y hy).trans (Eight.center_support P x hx hne).symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  apply has_fixedPoint_of_isConj (x := f y) (y := f x) _ ⟨p, hp⟩
  exact isConj_iff.mpr ⟨f g, by simpa only [map_mul, map_inv] using congrArg f hg⟩

/-- Every involution in every embedded A₆ belongs to the central HS class. -/
theorem a6_involution_isConj (f : alternatingGroup (Fin 6) →* Carrier)
    (hf : Function.Injective f) (x : alternatingGroup (Fin 6)) (hx : orderOf x = 2) :
    IsConj e0 (f x) :=
  central_class_of_fixedPoint ((orderOf_injective f hf x).trans hx)
    (a6_involution_fixed f x hx)

/-- Every central Sylow involution in every embedded A₈ belongs to the central HS class. -/
theorem a8_sylow_involution_isConj (f : alternatingGroup (Fin 8) →* Carrier)
    (hf : Function.Injective f) (P : Sylow 2 (alternatingGroup (Fin 8)))
    (x : P) (hx : x ∈ center P) (ho : orderOf (x : alternatingGroup (Fin 8)) = 2) :
    IsConj e0 (f x) :=
  central_class_of_fixedPoint ((orderOf_injective f hf x).trans ho)
    (a8_sylow_involution_fixed f P x hx ho)

end HSPermutationFusion
end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
