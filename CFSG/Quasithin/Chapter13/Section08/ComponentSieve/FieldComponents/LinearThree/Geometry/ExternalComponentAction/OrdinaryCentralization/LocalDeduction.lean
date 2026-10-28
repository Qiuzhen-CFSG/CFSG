module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.OrdinaryCentralization.SylowAction
public import Theory.GroupTheory.Commutator.TwoSubgroupNormalizer
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.SylowNormalRestriction
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The local external-commutator deduction

Suppose X=[X,T], T is Sylow two, X/O₂(X) has order three, and N is normal
with N/O₂(N) isomorphic to the actual PSL₃(2). If X is not contained in N,
its intersection with N is contained in O₂(X): the other possibility gives
a two-group image of X, which the full-commutator equality makes trivial.
Since T normalizes X, O₂(X) lies in T. Hence X normalizes T∩N.

Conjugation on N/O₂(N) therefore stabilizes the image of this Sylow subgroup.
Its automorphism stabilizer is a two-group by `SylowAction`; X=[X,T] again
kills this image. Evaluating the actual quotient action on representatives
gives [X,N]≤O₂(N), with the core embedded in the ambient group.

Source: Aschbacher–Smith 13.8.21(1), combined manuscript of 1 March 2004,
printed p.956. This is the intrinsic deduction, before the source setup
and the star-quotient identification are supplied by the parent module.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.OrdinaryCentralization
variable {A : Type*} [Group A] [Finite A]

private theorem full_two_eq_bot (X T : Subgroup A) (hpX : IsPGroup 2 X)
    (hpT : IsPGroup 2 T) (hfull : ⁅X, T⁆ = X) : X = ⊥ := by
  let J := X ⊔ T
  have hn : T ≤ normalizer (X : Set A) :=
    le_normalizer_iff_commutator_le_left.mpr hfull.le
  have hp : IsPGroup 2 J := hpX.to_sup_of_normal_left' hpT hn
  have hc : ⁅X.subgroupOf J, T.subgroupOf J⁆ = X.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, hfull]
  have hb := le_normal_of_quotient_isPGroup_of_eq_commutator
    (X.subgroupOf J) (T.subgroupOf J) ⊥ (hp.of_equiv QuotientGroup.quotientBot.symm) hc
  have he := congrArg (map J.subtype) (bot_unique hb)
  simpa only [map_subgroupOf_eq_of_le (show X ≤ J from le_sup_left), Subgroup.map_bot] using he

omit [Finite A] in
private theorem full_image_eq_bot {B : Type*} [Group B] [Finite B] (f : A →* B)
    (X T : Subgroup A) (hpX : IsPGroup 2 (X.map f))
    (hpT : IsPGroup 2 T) (hfull : ⁅X, T⁆ = X) : X.map f = ⊥ :=
  full_two_eq_bot (X.map f) (T.map f) hpX (hpT.map f)
    (by rw [← map_commutator, hfull])

private theorem outside_intersection (N X T : Subgroup A) [N.Normal]
    (hpT : IsPGroup 2 T) (hfull : ⁅X, T⁆ = X)
    (hcard : Nat.card (X ⧸ pCore 2 X) = 3) (hout : ¬ X ≤ N) :
    X ⊓ N ≤ X.pCoreIn 2 := by
  let C := N.subgroupOf X
  let q := QuotientGroup.mk' (pCore 2 X)
  let : Fact (Nat.card (X ⧸ pCore 2 X)).Prime := ⟨hcard ▸ by decide⟩
  rcases (C.map q).eq_bot_or_eq_top_of_prime_card with hc | hc
  · have hle : C ≤ pCore 2 X := by
      simpa only [q, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hc
    have hm := map_mono (f := X.subtype) hle
    simpa only [C, subgroupOf_map_subtype, pCoreIn, inf_comm] using hm
  · have hsup : C ⊔ pCore 2 X = ⊤ := by
      have hh := congrArg (comap q) hc
      simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
    have hp : IsPGroup 2 (X ⧸ C) :=
      isPGroup_quotient_of_sup_eq_top C (pCore 2 X) pCore_isPGroup hsup
    let f := (QuotientGroup.mk' N).comp X.subtype
    have hk : f.ker = C := by
      ext x
      exact QuotientGroup.eq_one_iff x.val
    have hp' : IsPGroup 2 f.range := by
      apply IsPGroup.of_equiv _ (QuotientGroup.quotientKerEquivRange f)
      exact hp.of_equiv (QuotientGroup.quotientMulEquivOfEq hk.symm)
    have hm : IsPGroup 2 (X.map (QuotientGroup.mk' N)) := by
      have hr : f.range = X.map (QuotientGroup.mk' N) := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩; exact ⟨x.val, x.property, rfl⟩
        · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
      exact hp'.of_equiv (MulEquiv.subgroupCongr hr)
    have hb := full_image_eq_bot (QuotientGroup.mk' N) X T hm hpT hfull
    exact False.elim (hout (by simpa only [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hb))

/-- The external case forces normalization of the component Sylow subgroup. -/
private theorem outside_normalizes_sylow (N X : Subgroup A) [N.Normal]
    (T : Sylow 2 A) (hfull : ⁅X, (T : Subgroup A)⁆ = X)
    (hcard : Nat.card (X ⧸ pCore 2 X) = 3) (hout : ¬ X ≤ N) :
    X ≤ normalizer (((T : Subgroup A) ⊓ N : Subgroup A) : Set A) := by
  have hn : (T : Subgroup A) ≤ normalizer (X : Set A) :=
    le_normalizer_iff_commutator_le_left.mpr hfull.le
  have hcore : X.pCoreIn 2 ≤ T := by
    have hncore := hn.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
    exact le_sup_left.trans (le_of_eq (T.is_maximal'
      ((isPGroup_pCoreIn 2 X).to_sup_of_normal_left' T.isPGroup' hncore) le_sup_right))
  apply le_normalizer_iff_commutator_le_right.mpr
  apply le_inf
  · have hx : ⁅X, (T : Subgroup A) ⊓ N⁆ ≤ X :=
      (commutator_mono le_rfl inf_le_left).trans hfull.le
    have hN : ⁅X, (T : Subgroup A) ⊓ N⁆ ≤ N :=
      (commutator_mono le_rfl inf_le_right).trans (commutator_le_right X N)
    exact (le_inf hx hN).trans ((outside_intersection N X T T.isPGroup' hfull hcard hout).trans hcore)
  · exact (commutator_mono le_rfl inf_le_right).trans (commutator_le_right X N)

open scoped commutatorElement

/-- An external full commutator of odd quotient order three centralizes the
normal binary linear-three component modulo its intrinsic two-core. -/
theorem commutator_le_core_of_outside (N X : Subgroup A) [N.Normal]
    (T : Sylow 2 A) (hfull : ⁅X, (T : Subgroup A)⁆ = X)
    (hcard : Nat.card (X ⧸ pCore 2 X) = 3) (hout : ¬ X ≤ N)
    (e : (N ⧸ pCore 2 N) ≃* Matrix.PSL3Two.PSL) :
    ⁅X, N⁆ ≤ N.pCoreIn 2 := by
  have hn := outside_normalizes_sylow N X T hfull hcard hout
  obtain ⟨S, hS⟩ := T.exists_sylow_map_eq_inf_of_normal N
  let q := QuotientGroup.mk' (pCore 2 N)
  let p := e.toMonoidHom.comp q
  have hp : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := S.mapSurjective hp
  let ρ := (MulAut.congr e).toMonoidHom.comp (normalQuotientAction N (pCore 2 N))
  have happ (a : A) (n : N) : ρ a (p n) = p (MulAut.conjNormal a n) := by
    change MulAut.congr e (normalQuotientAction N (pCore 2 N) a) (e (q n)) = _
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, e.symm_apply_apply]
    rw [normalQuotientAction_apply_mk]
    rfl
  have hpres (a : A) (ha : a ∈ X) : ∀ z ∈ (R : Subgroup Matrix.PSL3Two.PSL),
      ρ a z ∈ (R : Subgroup Matrix.PSL3Two.PSL) := by
    rintro z ⟨s, hs, rfl⟩
    rw [happ]
    apply mem_map_of_mem
    have hsA : (s : A) ∈ (T : Subgroup A) ⊓ N := hS ▸ mem_map_of_mem N.subtype hs
    have hb := le_normalizer_iff.mp hn a ha (s : A) hsA
    have hb' : (MulAut.conjNormal a s : N).val ∈ (S : Subgroup N).map N.subtype :=
      hS.symm ▸ hb
    exact (mem_map_iff_mem N.subtype_injective).mp hb'
  have hρ : X.map ρ ≤ MulAction.stabilizer (MulAut Matrix.PSL3Two.PSL)
      (R : Subgroup Matrix.PSL3Two.PSL) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_automorphism_stabilizer_iff]
    intro z
    constructor
    · intro hz
      have hh := hpres a⁻¹ (X.inv_mem ha) (ρ a z) hz
      simpa only [map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply] using hh
    · exact hpres a ha z
  have hzero := full_image_eq_bot ρ X T ((sylow_stabilizer_two R).to_le hρ) T.isPGroup' hfull
  have hker : X ≤ ρ.ker := (Subgroup.map_eq_bot_iff X).mp hzero
  apply commutator_le.mpr
  intro x hx n hnN
  let n' : N := ⟨n, hnN⟩
  let b : N := MulAut.conjNormal x n'
  have he := DFunLike.congr_fun (hker hx) (p n')
  change ρ x (p n') = p n' at he
  rw [happ] at he
  have heq : q b = q n' := e.injective he
  have hc : b * n'⁻¹ ∈ pCore 2 N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (b * n'⁻¹) = 1
    rw [map_mul, map_inv, heq, mul_inv_cancel]
  exact ⟨b * n'⁻¹, hc, rfl⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.OrdinaryCentralization
