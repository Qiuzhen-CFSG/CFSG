module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.LocalFixedIndex
public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The odd core has order nine on the exceptional module

Suppose the odd core is a three-group and acts faithfully on an invariant
elementary abelian subgroup of order sixteen. If the elementary Sylow
two-subgroup has order four, the odd core has order nine and is abelian.

The specified invariance instance gives a genuine restricted linear action,
and the trivial pointwise kernel makes its representation injective.
Thus the odd core embeds in GL4(2), whose order 20160 has three-part nine.
The previously proved trivial Sylow centralizer of the odd core excludes
order one. It also makes Sylow conjugation faithful on the odd core,
excluding order three since Aut(C3) has order two. A group of order
three squared is abelian.

This supplies the cardinal calculation in Stellmacher (1.6), journal p.18,
following `refs/latex/stellmacher-n-group.tex`. Invariance of the
sixteen-element subgroup is an explicit premise; it is not inferred from
faithfulness or from the desired exceptional conclusion.
-/

namespace Stellmacher.SectionOne

open scoped IsMulCommutative

universe u

/-- A faithful invariant sixteen-element module forces the three-group odd
core to have order nine when the elementary Sylow two-subgroup has order four. -/
public theorem oddCore_card_nine_of_faithful_sixteen_action
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS : IsElementaryAbelian 2 (S : Subgroup G))
    (hScard : Nat.card (S : Subgroup G) = 4)
    (hWthree : IsPGroup 3 (oddCore G))
    (U : Subgroup V) [IsInvariant (oddCore G) V U]
    (hUcard : Nat.card U = 16)
    (hkernel : oddCore G ⊓ fixingSubgroup G (U : Set V) = ⊥) :
    Nat.card (oddCore G) = 9 ∧ IsMulCommutative (oddCore G) := by
  classical
  let W := oddCore G
  let _ : W.Normal := pPrimeCore_normal
  let _ : IsElementaryAbelian 2 U :=
    RankOneThreeGroupAssembly.isElementaryAbelian_subgroup U
  let ρ := Representation.ofElementaryAbelianAction (A := W) (G := U) (p := 2)
  have hρinj : Function.Injective ρ.asGroupHom := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro w hw
    have heq : ρ w = 1 := congrArg Units.val (MonoidHom.mem_ker.mp hw)
    have hwfix : (w : G) ∈ fixingSubgroup G (U : Set V) := by
      rw [mem_fixingSubgroup_iff]
      intro v hv
      have hvfix : w • (⟨v, hv⟩ : U) = ⟨v, hv⟩ := by
        apply Additive.ofMul.injective
        have happ := LinearMap.congr_fun heq (Additive.ofMul (⟨v, hv⟩ : U))
        simpa only [ρ, Representation.ofElementaryAbelianAction_apply_ofMul,
          Module.End.one_apply] using happ
      exact congrArg Subtype.val hvfix
    have hwbot : (w : G) ∈ (⊥ : Subgroup G) := hkernel.le ⟨w.property, hwfix⟩
    exact Subtype.ext hwbot
  have hdim : Module.finrank (ZMod 2) (Additive U) = 4 := by
    have hc : Nat.card (Additive U) = 16 := (Nat.card_congr Additive.toMul).trans hUcard
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)] at hc
    norm_num at hc
    exact Nat.pow_right_injective (by omega : 1 < 2) hc
  let b : Module.Basis (Fin 4) (ZMod 2) (Additive U) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive U) hdim
  let φ : W →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρ.asGroupHom
  have hφinj : Function.Injective φ :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hρinj
  have hdiv := Subgroup.card_dvd_of_injective φ hφinj
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  rw [hGL] at hdiv
  obtain ⟨n, hn⟩ := hWthree.exists_card_eq
  have hnle : n ≤ 2 := by
    by_contra hnot
    have hbad : 27 ∣ 20160 := by
      rw [hn] at hdiv
      exact (show 27 ∣ 3 ^ n from Nat.pow_dvd_pow 3 (by omega : 3 ≤ n)).trans hdiv
    norm_num at hbad
  have hcent : (S : Subgroup G) ⊓ Subgroup.centralizer (W : Set G) = ⊥ :=
    RankOneThreeGroupAssembly.sylow_inf_centralizer_oddCore_eq_bot h S hS hWthree
  have hcard9 : Nat.card W = 9 := by
    interval_cases n
    · have hWbot : W = ⊥ := Subgroup.card_eq_one.mp hn
      have hSbot : (S : Subgroup G) = ⊥ := by
        apply le_antisymm _ bot_le
        intro s hs
        apply hcent.le
        refine ⟨hs, ?_⟩
        change s ∈ Subgroup.centralizer (W : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hw1 : w = 1 := hWbot.le hw
        simp [hw1]
      have hSone : Nat.card (S : Subgroup G) = 1 := Subgroup.card_eq_one.mpr hSbot
      omega
    · have hWcard : Nat.card W = 3 := hn
      let _ : IsCyclic W := isCyclic_of_prime_card hWcard
      have hAut : Nat.card (MulAut W) = 2 := by
        rw [IsCyclic.card_mulAut, hWcard, Nat.totient_prime Nat.prime_three]
      let ψ : (S : Subgroup G) →* MulAut W := MulAut.conjNormal.comp (S : Subgroup G).subtype
      have hψinj : Function.Injective ψ := by
        rw [← MonoidHom.ker_eq_bot_iff]
        apply le_antisymm _ bot_le
        intro s hs
        have hscent : (s : G) ∈ Subgroup.centralizer (W : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          have heq := congrArg (fun f : MulAut W => (f ⟨w, hw⟩ : G))
            (MonoidHom.mem_ker.mp hs)
          change (s : G) * w * (s : G)⁻¹ = w at heq
          have heq' := congrArg (fun x : G => x * (s : G)) heq
          simpa [mul_assoc] using heq'.symm
        exact Subtype.ext (hcent.le ⟨s.property, hscent⟩)
      have hbad := Subgroup.card_dvd_of_injective ψ hψinj
      rw [hScard, hAut] at hbad
      norm_num at hbad
    · exact hn
  exact ⟨hcard9, IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcard9⟩

end Stellmacher.SectionOne

