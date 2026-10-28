module

public import Theory.GroupTheory.QuaternionCoreRecognition
public import CFSG.Quasithin.ChapterI.Section04To05.SmallSylow.SemidihedralCore
public import CFSG.Quasithin.ChapterI.Section04To05.SmallSylow.Fusion
public import Theory.GroupTheory.SpecificGroups.QuaternionEightInvolution
public import Theory.GroupTheory.SelfCentralizingCore

/-!
# The full quaternion action in the source involution centralizer

The marked quaternion core has centralizer of order two. All its elements
of order four square to the original involution, so their ambient fusion
already takes place in that involution's centralizer. Orbit-stabilizer and
the actual Sylow inclusion give centralizer order 48 and the full quaternion
automorphism action. The literal two-residual is consequently SL₂(3), and
even characteristic kills the odd core.

These are the exact local model inputs in Aschbacher–Smith I.4.3,
printed pp.416–417. The original no-index-two and even-characteristic
hypotheses discharge every local condition.
-/

open Subgroup
namespace CFSG.Quasithin.ChapterI.SmallSylow
open Theory.GroupTheory.QuaternionCoreRecognition
variable {G : Type*} [Group G] [Finite G]

/-- The actual source centralizer has full quaternion automizer and an
identified characteristic SL₂(3) residual. -/
public theorem source_automizer
    (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (hT : Stellmacher.IsSemidihedralGroup T) :
    ∃ z : G, orderOf z = 2 ∧
      ∃ _hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G),
        let H := centralizer ({z} : Set G)
        Nonempty ((pCore 2 H) ≃* QuaternionGroup 2) ∧ Nat.card H = 48 ∧
        Function.Surjective (MulAut.conjNormal : H →* MulAut (pCore 2 H)) ∧
        Nonempty ((pResidual 2 H) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
        pPrimeCore 2 H = ⊥ := by
  obtain ⟨hcard, a, b, ha, hb, hab, hgen, hz, hTH, hcore, ⟨eQ⟩, hC, hZ⟩ :=
    SemidihedralCore.source_core_structure T hE hno hT
  let z : G := ((a ^ 4 : T) : G)
  let H := centralizer ({z} : Set G)
  let zH : H := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩
  let Q := pCore 2 H
  have hzH : orderOf zH = 2 := (Subgroup.orderOf_coe zH).symm.trans hz
  have hself : centralizer (Q : Set H) ≤ Q :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T hE
      (Theory.GroupTheory.isTwoLocal_involution_centralizer hz) hTH)
  have hzQ : zH ∈ Q := hself (hC ▸ mem_zpowers zH)
  let zQ : Q := ⟨zH, hzQ⟩
  have hzQ2 : orderOf zQ = 2 := (Subgroup.orderOf_coe zQ).symm.trans hzH
  have hsquare (x : Q) (hx : orderOf x = 4) : (x : H) ^ 2 = zH := by
    have hs : orderOf (x ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by decide) (by rw [hx]; decide), hx]
    have he : x ^ 2 = zQ := eQ.injective (QuaternionGroup.eq_of_orderOf_eq_two
      (eQ (x ^ 2)) (eQ zQ) ((eQ.orderOf_eq _).trans hs) ((eQ.orderOf_eq _).trans hzQ2))
    exact congrArg Subtype.val he
  have hf : ∀ x y : Q, orderOf x = 4 → orderOf y = 4 → IsConj (x : H) y := by
    intro x y hx hy
    have hxG : orderOf ((x : H) : G) = 4 :=
      (Subgroup.orderOf_coe (x : H)).trans ((Subgroup.orderOf_coe x).trans hx)
    have hyG : orderOf ((y : H) : G) = 4 :=
      (Subgroup.orderOf_coe (y : H)).trans ((Subgroup.orderOf_coe y).trans hy)
    obtain ⟨g, hg⟩ := isConj_iff.mp ((semidihedral_fusion T hT hno).2 _ _ hxG hyG)
    have hsx : ((x : H) : G) ^ 2 = z := congrArg Subtype.val (hsquare x hx)
    have hsy : ((y : H) : G) ^ 2 = z := congrArg Subtype.val (hsquare y hy)
    have hgz : g * z * g⁻¹ = z := by
      have hh := congrArg (fun t : G => t ^ 2) hg
      rw [← MulAut.conj_apply, ← map_pow, hsx, hsy] at hh
      exact hh
    have hgH : g ∈ H := mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hgz)
    exact isConj_iff.mpr ⟨⟨g, hgH⟩, Subtype.ext hg⟩
  have hCc : Nat.card (centralizer (Q : Set H)) = 2 := by
    rw [hC, Nat.card_zpowers, hzH]
  have h16 : 16 ∣ Nat.card H := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_injective (inclusion hTH) (inclusion_injective hTH)
  obtain ⟨hH, hfull⟩ := full_automizer Q eQ hCc h16 hf
  exact ⟨z, hz, hTH, ⟨eQ⟩, hH, hfull, residual_model Q eQ hCc hH,
    Theory.GroupTheory.pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hself⟩
end CFSG.Quasithin.ChapterI.SmallSylow
