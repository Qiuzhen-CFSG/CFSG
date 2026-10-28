module
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Mathlib.GroupTheory.FixedPointFree
public import Theory.SpecificGroups.Janko1.Model.Certification
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.Geometry

/-!
# The order-nineteen obstruction in the actual J₁ component

An automorphism of order nineteen on a two-group Q fixes a subgroup whose
order is congruent to |Q| modulo nineteen. The powers 2⁰,...,2¹⁶ have distinct
residues, so |Q| ≤ 2¹⁶ forces that automorphism to be trivial. The actual
J₁ quotient of the source component has an element of order nineteen, and
its simplicity and the component's perfectness make the component generated
by nineteen-elements. Consequently it centralizes every normalized two-group
of order at most 2¹⁶. The final theorem applies this to the original flag
residual. Construction of Q and its source bounds remains with this task's
assembly owner, qt-d-1222-natural-line-action.

Source: Aschbacher--Smith, 3.3.16, final paragraph, printed p.591.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer

private theorem nineteen_coprime_card_mulAut_of_twoGroup_small
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (hsmall : Nat.card Q ≤ 2 ^ 16) :
    Nat.Coprime 19 (Nat.card (MulAut Q)) := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  apply (show Nat.Prime 19 by decide).coprime_iff_not_dvd.mpr
  intro hnineteen
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 19 hnineteen
  let A := zpowers a
  have hp : IsPGroup 19 A := IsPGroup.of_card (n := 1) (by
    simpa only [A,Nat.card_zpowers,pow_one] using ha)
  let F := FixedPoints.subgroup A Q
  have hm := hp.card_modEq_card_fixedPoints Q
  change Nat.card Q % 19 = Nat.card F % 19 at hm
  obtain ⟨n,hn⟩ := hQ.exists_card_eq
  obtain ⟨m,hmc⟩ := (hQ.to_subgroup F).exists_card_eq
  have hnle : n ≤ 16 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hn] using hsmall
  have hmle : m ≤ 16 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    exact hmc ▸ (Nat.card_le_card_of_injective F.subtype F.subtype_injective).trans hsmall
  have hinj : Function.Injective (fun i : Fin 17 => (2 ^ i.val) % 19) := by decide +kernel
  have hnm : n = m := congrArg Fin.val (hinj (a₁ := ⟨n,by omega⟩) (a₂ := ⟨m,by omega⟩)
    (by simpa only [hn,hmc] using hm))
  have ht : F = ⊤ := F.eq_top_of_card_eq (by rw [hmc,hn,hnm])
  have hone : a = 1 := by
    apply MulEquiv.ext
    intro x
    exact (show x ∈ F from ht ▸ mem_top x) ⟨a,mem_zpowers a⟩
  rw [hone,orderOf_one] at ha
  norm_num at ha

variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c}
    {A : OddSupplement T} (E : JankoConfiguration S f A)

namespace JankoConfiguration

/-- The actual source component centralizes any normalized two-group of order at most 2¹⁶. -/
theorem centralizes_small_twoGroup {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hsmall : Nat.card Q ≤ 2 ^ 16)
    (hn : E.component ≤ normalizer (Q : Set G)) :
    E.component ≤ centralizer (Q : Set G) := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  let K := E.component
  let H := ((f.Li E.index ⊔ (T : Subgroup G)) ⊔ A.subgroup)
  let : Group.IsPerfect (K.subgroupOf H) := E.normal_component.1.2.perfect
  let eK : K.subgroupOf H ≃* K := subgroupOfEquivOfLe E.normal_component.1.1
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := eK.toMonoidHom) eK.surjective
  obtain ⟨e⟩ := E.model
  let : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
  have hd : 19 ∣ Nat.card (K ⧸ pCore 2 K) := by
    rw [Nat.card_congr e.toEquiv, ← Janko1.orderOf_abab_sq]
    exact orderOf_dvd_natCard _
  have hp : IsPPerfect 2 K := by
    intro N hN hquot
    let := hN
    let : Group.IsNilpotent (K ⧸ N) := hquot.isNilpotent
    exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hres := primeToResidual_eq_top_of_simple_quotient 19 2
    (pCore 2 K) pCore_isPGroup hp hd
  let action : K →* MulAut Q := Q.normalizerMonoidHom.comp (inclusion hn)
  have hk := primeToResidual_le_ker action
    (nineteen_coprime_card_mulAut_of_twoGroup_small hQ hsmall)
  rw [hres] at hk
  intro x hx
  apply mem_centralizer_iff.mpr
  intro y hy
  have he := congrArg (fun a : MulAut Q => (a ⟨y,hy⟩ : G))
    (hk (show (⟨x,hx⟩ : K) ∈ ⊤ from trivial))
  change x * y * x⁻¹ = y at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- A nontrivial action of the original residual contradicts the J₁ order obstruction. -/
theorem false_of_small_twoGroup {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hsmall : Nat.card Q ≤ 2 ^ 16)
    (hn : E.component ≤ normalizer (Q : Set G))
    (hmoves : ¬ f.Li E.index ≤ centralizer (Q : Set G)) : False :=
  hmoves (E.contains.le.trans (E.centralizes_small_twoGroup hQ hsmall hn))

end JankoConfiguration
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
