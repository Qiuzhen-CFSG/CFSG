module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Reduction


/-!
# Odd subgroups inverted by a conjugate of an outer family actor

The original elementary family is invariant under conjugation. Thus an actual
conjugate B of its actor can be used in the local E-generation argument whenever
B lies in the fixed Sylow subgroup. With trivial two-core, the ambient tau is
contained in C_T(B). An odd-prime subgroup X normalized by C_T(B) therefore
contributes [X,B] to the obstruction overgroup, using the intrinsic Sylow and
quotient calculations in `InnerGeometry.tau_normalized_odd_commutator_le`.
That theorem does not require B to be inner.

If the obstruction overgroup is C_G(z), with z in B inverting X, then X is
trivial: the squares in X are commutators, so odd-order squaring first puts X
in C_G(z), and inversion then makes every element have square one. No
intersection or cyclic subgroup is substituted for an original family member.

This reduction does not construct the odd subgroup or identify the overgroup.
The companion assembly takes intrinsic maximality and the concrete local
constructions explicitly until their independent producers discharge them.

Source: Aschbacher--Smith, E.1.1--2, E.1.5, E.1.8(2), E.1.10 and E.1.14(7),
printed pp.209--214; the last cites Aschbacher, *GF(2)-representations of finite
groups* (1982), Lemma 4.11.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry
variable {G : Type*} [Group G] [Finite G]

/-- A normalized odd subgroup inverted by an element of an actual conjugate
family actor is trivial once the obstruction is the involution centralizer.
The conjugator acts on the whole actor, retaining literal family membership. -/
theorem conjugate_inverted_odd_subgroup_eq_bot
    {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    (hcore : pCore 2 G = ⊥) {z : G}
    (hMC : d.overgroup = centralizer ({z} : Set G))
    {A : Subgroup G} (hA : A ∈ d.family) (g : G)
    (hBT : A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (hzB : z ∈ A.map (MulAut.conj g).toMonoidHom)
    {r : ℕ} [Fact r.Prime] (ho : Odd r) (X : Subgroup G)
    (hX : IsPGroup r X)
    (hn : (T : Subgroup G) ⊓ centralizer
      (A.map (MulAut.conj g).toMonoidHom : Set G) ≤ normalizer (X : Set G))
    (hinv : ∀ x ∈ X, z * x * z⁻¹ = x⁻¹) : X = ⊥ := by
  let B := A.map (MulAut.conj g).toMonoidHom
  have hB : B ∈ d.family := d.elementary.2 g A hA
  have htau : tau (T : Subgroup G) B ≤
      (T : Subgroup G) ⊓ centralizer (B : Set G) := by
    intro t ht
    refine ⟨tau_le _ _ ht, mem_centralizer_iff.mpr ?_⟩
    intro b hb
    have hc := (mem_centralizerModulo_iff.mp ht).2 b hb
    rw [hcore, mem_bot] at hc
    exact commutatorElement_eq_one_iff_mul_comm.mp hc
  have hcomm : ⁅X, B⁆ ≤ centralizer ({z} : Set G) := by
    rw [← hMC]
    exact InnerGeometry.tau_normalized_odd_commutator_le d hB hBT
      (fun he => ho.not_two_dvd_nat (he ▸ dvd_rfl)) X hX (htau.trans hn)
  have hsq (x : X) : (x : G) ^ 2 ∈ ⁅X, B⁆ := by
    have hi : z * (x : G)⁻¹ * z⁻¹ = x := by
      simpa using hinv _ (X.inv_mem x.property)
    have he : ⁅(x : G), z⁆ = (x : G) ^ 2 := by
      rw [commutatorElement_def]
      calc
        (x : G) * z * (x : G)⁻¹ * z⁻¹ = (x : G) * (z * (x : G)⁻¹ * z⁻¹) := by
          simp only [mul_assoc]
        _ = (x : G) ^ 2 := by rw [hi, pow_two]
    exact he ▸ commutator_mem_commutator x.property hzB
  have hXC : X ≤ centralizer ({z} : Set G) := by
    intro x hx
    obtain ⟨y, hy⟩ := (hX.powEquiv ho.coprime_two_right).surjective (⟨x, hx⟩ : X)
    have hy' : (y : G) ^ 2 = x := congrArg Subtype.val hy
    exact hy' ▸ hcomm (hsq y)
  apply le_antisymm ?_ bot_le
  intro x hx
  rw [mem_bot]
  have hc := mem_centralizer_singleton_iff.mp (hXC hx)
  have he : x = x⁻¹ := by
    simpa only [← hc, mul_inv_cancel_right] using hinv x hx
  have hs : (⟨x, hx⟩ : X) ^ 2 = 1 := by
    apply Subtype.ext
    change x ^ 2 = 1
    calc
      x ^ 2 = x * x := pow_two _
      _ = x⁻¹ * x := congrArg (fun y => y * x) he
      _ = 1 := inv_mul_cancel x
  have hh : (⟨x, hx⟩ : X) = 1 :=
    (hX.powEquiv ho.coprime_two_right).injective (by
      simpa only [IsPGroup.powEquiv_apply, one_pow] using hs)
  exact congrArg Subtype.val hh

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry
