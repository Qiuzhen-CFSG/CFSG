module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors.Context
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import GorensteinWalter.PGL2DihedralSylow
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.ElementaryAbelian.Quotient

/-!
# Centralizing actors in the paired linear-three setup

For the actual normal subgroups K and X with F*(H) = K × X and |X| = 3,
self-centralization of the intrinsic generalized Fitting subgroup gives
C_H(K) ∩ C_H(X) = X. Thus conjugation on K is injective on every elementary
abelian two-subgroup of C_H(X). Transport through the actual K ≃ SL₃(2)
and Aut(PSL₃(2)) ≃ PGL₂(7) equivalences, followed by the dihedral Sylow
calculation, bounds its binary rank by two.

An involution centralizing X which acts inner on K lies in KX. Its X-factor
has square one and hence is trivial. This proves that involutions outside K
induce outer automorphisms, with the conjugation kernel retained throughout.

These are the group-theoretic inputs to the paired-module calculation in the
ordinary-A₆ branch of Aschbacher–Smith 13.8.21(1), printed p.956, combined
manuscript of 1 March 2004. The module-displacement and final source-theorem
assembly are separate obligations.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

private theorem aut_rank (K : Type*) [Group K] [Finite K]
    (eK : K ≃* BinaryLinearThree.Group) :
    primeRank 2 (MulAut K) ≤ 2 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Finite (GorensteinWalter.PGL2 (ZMod 7)) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let P : Sylow 2 (GorensteinWalter.PGL2 (ZMod 7)) := Classical.choice inferInstance
  have hp : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod 7)) := by
    refine ⟨7, 1, by decide, by decide, by decide, ?_⟩
    norm_num
  obtain ⟨n, _, ⟨eP⟩⟩ := GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model (ZMod 7) hp P
  have hr : primeRank 2 (GorensteinWalter.PGL2 (ZMod 7)) ≤ 2 := by
    rw [P.primeRank_eq, primeRank_equiv 2 eP]
    exact dihedral_rank_le_two n
  let e : MulAut K ≃* GorensteinWalter.PGL2 (ZMod 7) :=
    (MulAut.congr (eK.trans Matrix.PSL3Two.equiv)).trans
      Matrix.PSL3Two.Automorphisms.pgl2SevenEquivAut.symm
  rw [primeRank_equiv 2 e]
  exact hr

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
variable {σ : Representation (ZMod 2) H U} {K X : Subgroup H}
  {eK : K ≃* BinaryLinearThree.Group} (h : PairedSetup σ K X eK)

include eK in
private theorem component_center : center K = ⊥ := by
  apply le_bot_iff.mp
  intro k hk
  have hc := (Subgroup.centerCongr eK ⟨k, hk⟩).property
  change eK k ∈ center BinaryLinearThree.Group at hc
  rw [Matrix.PSL3Two.center_eq_bot, mem_bot] at hc
  exact mem_bot.mpr (eK.map_eq_one_iff.mp hc)

include h

private theorem cyclic_le_component_centralizer : X ≤ centralizer (K : Set H) := by
  intro x hx
  exact mem_centralizer_iff.mpr (fun k hk => (h.commute k hk x hx).eq)

private theorem cyclic_le_self_centralizer : X ≤ centralizer (X : Set H) := by
  let := h.cyclic
  intro x hx
  apply mem_centralizer_iff.mpr
  intro y hy
  exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : X) ⟨x, hx⟩)

private theorem square_eq_one_in_cyclic {x : H} (hx : x ∈ X) (hx2 : x ^ 2 = 1) : x = 1 := by
  have hx3 : x ^ 3 = 1 := by
    have hh : (⟨x, hx⟩ : X) ^ Nat.card X = 1 := pow_card_eq_one'
    rw [h.cyclic_order] at hh
    exact congrArg Subtype.val hh
  simpa [pow_succ, hx2] using hx3

variable [Finite H]

/-- The kernel of conjugation on K, restricted to C_H(X), is precisely X. -/
theorem centralizer_component_inf_cyclic :
    centralizer (K : Set H) ⊓ centralizer (X : Set H) = X := by
  let := h.cyclic_normal
  apply le_antisymm
  · intro a ha
    have hsup : a ∈ centralizer ((K ⊔ X : Subgroup H) : Set H) := by
      rw [sup_eq_closure, centralizer_closure]
      apply mem_centralizer_iff.mpr
      intro y hy
      rcases hy with hy | hy
      · exact mem_centralizer_iff.mp ha.1 y hy
      · exact mem_centralizer_iff.mp ha.2 y hy
    have haF : a ∈ K ⊔ X := by
      rw [← h.fitting] at hsup ⊢
      exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le hsup
    obtain ⟨k, hk, x, hx, rfl⟩ := mem_sup_of_normal_right.mp haF
    have hkC : k ∈ centralizer (K : Set H) := by
      have hh := (centralizer (K : Set H)).mul_mem ha.1
        ((centralizer (K : Set H)).inv_mem ((cyclic_le_component_centralizer h) hx))
      simpa only [mul_inv_cancel_right] using hh
    have hkZ : (⟨k, hk⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hkC y y.property)
    have hk1 : k = 1 := congrArg Subtype.val
      (mem_bot.mp ((component_center (eK := eK)).le hkZ))
    simpa [hk1] using hx
  · exact le_inf (cyclic_le_component_centralizer h) (cyclic_le_self_centralizer h)

/-- Conjugation on K is injective on every elementary two-subgroup of C_H(X). -/
theorem centralizing_conjugation_injective (A : Subgroup H) (hA : IsElementaryAbelian 2 A)
    (hAX : A ≤ centralizer (X : Set H)) :
    Function.Injective ((@MulAut.conjNormal H _ K h.component_normal).comp A.subtype) := by
  let := h.component_normal
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro a ha
  have hac : (a : H) ∈ centralizer (K : Set H) := by
    apply mem_centralizer_iff.mpr
    intro k hk
    have hh := congrArg (fun f : MulAut K => (f ⟨k, hk⟩ : H)) ha
    change a.val * k * a.val⁻¹ = k at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have haX : (a : H) ∈ X := (centralizer_component_inf_cyclic h).le ⟨hac, hAX a.property⟩
  let := hA
  exact mem_bot.mpr (Subtype.ext ((square_eq_one_in_cyclic h) haX
    (elemPow_eq_one_of_isElementaryAbelian a.val a.property)))

/-- Elementary two-subgroups centralizing X have rank at most two. -/
theorem elementary_centralizing_rank_le_two (A : Subgroup H) (hA : IsElementaryAbelian 2 A)
    (hAX : A ≤ centralizer (X : Set H)) : rank A ≤ 2 := by
  let := h.component_normal
  let := hA
  let f : A →* MulAut K := MulAut.conjNormal.comp A.subtype
  have hf : Function.Injective f := (centralizing_conjugation_injective h) A hA hAX
  let E : Subgroup (MulAut K) := f.range
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.of_surjective
    f.rangeRestrict f.rangeRestrict_surjective
  have hc := (primeRank_le_iff_elementary_card_le (MulAut K)).mp (aut_rank K eK) E hE
  have he : Nat.card A = Nat.card E := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
  have hcard : Nat.card A ≤ 4 := by simpa only [he, Nat.reducePow] using hc
  exact (Nat.log_mono_right hcard).trans (by decide : Nat.log 2 4 ≤ 2)

/-- The rank bound in the nontrivial actor convention used by binary offenders. -/
theorem centralizing_rank_le_two (A : Subgroup H) (hA : IsElementaryTwo A)
    (hAX : A ≤ centralizer (X : Set H)) : rank A ≤ 2 :=
  (elementary_centralizing_rank_le_two h) A hA.2 hAX

/-- A centralizing involution outside K induces an outer automorphism of K. -/
theorem outerOnComponent_of_centralizing_involution (a : H) (ha2 : a ^ 2 = 1)
    (haK : a ∉ K) (haX : a ∈ centralizer (X : Set H)) : OuterOnComponent K a := by
  rintro ⟨k, hk⟩
  let b : H := k.val⁻¹ * a
  have hbK : b ∈ centralizer (K : Set H) := by
    apply mem_centralizer_iff.mpr
    intro u hu
    have hh := hk ⟨u, hu⟩
    have hb : b * u * b⁻¹ = u := by
      dsimp [b]
      calc
        k.val⁻¹ * a * u * (k.val⁻¹ * a)⁻¹ =
            k.val⁻¹ * (a * u * a⁻¹) * k.val := by group
        _ = k.val⁻¹ * (k.val * u * k.val⁻¹) * k.val := by rw [hh]
        _ = u := by group
    exact (mul_inv_eq_iff_eq_mul.mp hb).symm
  have hkX : k.val ∈ centralizer (X : Set H) := by
    exact mem_centralizer_iff.mpr (fun x hx => (h.commute k.val k.property x hx).eq.symm)
  have hbX : b ∈ X := (centralizer_component_inf_cyclic h).le
    ⟨hbK, (centralizer (X : Set H)).mul_mem
      ((centralizer (X : Set H)).inv_mem hkX) haX⟩
  have hab : a = k.val * b := by dsimp [b]; group
  have hkb : Commute k.val b := h.commute k.val k.property b hbX
  have hb2K : b ^ 2 ∈ K := by
    have hh : k.val ^ 2 * b ^ 2 = 1 := by rw [← hkb.mul_pow, ← hab, ha2]
    have hb2 : b ^ 2 = (k.val ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hh
    rw [hb2]
    exact K.inv_mem (K.pow_mem k.property 2)
  have hb2 : b ^ 2 = 1 := mem_bot.mp (h.disjoint.le ⟨hb2K, X.pow_mem hbX 2⟩)
  have hb1 := (square_eq_one_in_cyclic h) hbX hb2
  apply haK
  simpa only [hab, hb1, mul_one] using k.property

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors
