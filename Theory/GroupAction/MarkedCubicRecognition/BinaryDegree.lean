module
public import Theory.Representation.ExtraspecialSmallFixedSpace
public import Theory.GroupAction.MarkedCubicRecognition.Models
public import Theory.Representation.NormalElementaryQuotient
public import Stellmacher.OmegaOneCenterMap

/-!
# The six-dimensional Heisenberg alternative

The native extraspecial subgroup is normal of order 27, and the actual
Sylow two-subgroups of the marked extension have order four. The small
fixed-space theorem therefore identifies the dimension of every faithful
binary action whose Sylow fixed space is a plane. Descent through a literal
two-core quotient then gives order 64 for a normal elementary omega span.
The original omega-span
application is in Chapter13 Section04 `Amalgam.SolvableSix`.

Source: Aschbacher--Smith 13.4.7(1iii), printed p.902.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender

namespace MarkedCubicRecognition
open Representation.ExtraspecialSmallFixedSpace
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The faithful binary action with a Sylow fixed plane has dimension six. -/
theorem heisenberg_finrank_six (ρ : Representation (ZMod 2) HeisenbergExtension V)
    (hf : Function.Injective ρ) (S : Sylow 2 HeisenbergExtension)
    (hfix : Module.finrank (ZMod 2) (fixedSpace ρ (S : Subgroup HeisenbergExtension)) ≤ 2) :
    Module.finrank (ZMod 2) V = 6 := by
  let : Finite HeisenbergExtension := Finite.of_equiv (HeisenbergPrime 3 × Four)
    (SemidirectProduct.equivProd (N := HeisenbergPrime 3) (G := Four)
      (φ := heisenbergAction)).symm
  let P : Subgroup HeisenbergExtension := SemidirectProduct.inl.range
  let e : HeisenbergPrime 3 ≃* P := MonoidHom.ofInjective SemidirectProduct.inl_injective
  let : P.Normal := by
    rw [show P = (SemidirectProduct.rightHom : HeisenbergExtension →* Four).ker from
      SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  let : IsExtraspecial 3 P := IsExtraspecial.of_mulEquiv e
    (HeisenbergPrime.isExtraspecial (by decide))
  have hP : Nat.card P = 27 := by
    rw [←Nat.card_congr e.toEquiv,HeisenbergPrime.card]
    norm_num
  have hn : ((center P).map P.subtype).Normal := inferInstance
  have hcard : Nat.card HeisenbergExtension = 108 := by
    rw [Nat.card_congr (SemidirectProduct.equivProd (N := HeisenbergPrime 3)
      (G := Four) (φ := heisenbergAction)),Nat.card_prod,HeisenbergPrime.card]
    norm_num [Four,C2,Nat.card_prod,Nat.card_zmod]
  have hS : Nat.card S = 4 := by
    rw [S.card_eq_multiplicity,hcard]
    decide +kernel
  exact (finrank_six ρ hf P S hP hn S.isPGroup' hS hfix).1
end MarkedCubicRecognition

open Stellmacher
open scoped IsMulCommutative
namespace MarkedCubicRecognition

/-- The reduced omega span has order 64 in the actual Heisenberg quotient. -/
theorem omega_seed_card
    {X : Type*} [Group X] [Finite X] (S : Sylow 2 X)
    (W : Subgroup X) [W.Normal] [IsElementaryAbelian 2 W]
    (hseed : omegaOneCenterAmbient (S : Subgroup X) ≤ W)
    (hZ : Nat.card (omegaOneCenterAmbient (S : Subgroup X)) = 4)
    (hk : centralizer (W : Set X) = pCore 2 X)
    (e : (X ⧸ pCore 2 X) ≃* MarkedCubicRecognition.HeisenbergExtension) :
    Nat.card W = 64 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = centralizer (W : Set X) := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',hk]
  let ρ := NormalElementaryQuotient.representation W q hq hker
  let S' := S.mapSurjective hq
  have hWS : W ≤ (S : Subgroup X) :=
    (IsElementaryAbelian.isPGroup 2 W).le_sylow_of_normal S
  have hfixed : W ⊓ centralizer (S : Set X) = omegaOneCenterAmbient (S : Subgroup X) := by
    apply le_antisymm
    · intro w hw
      exact (mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨hWS hw.1,elemPow_eq_one_of_isElementaryAbelian w hw.1,hw.2⟩
    · intro w hw
      exact ⟨hseed hw,((mem_omegaOneCenterAmbient_iff _ _).mp hw).2.2⟩
  have hFcard : Nat.card (fixedSpace ρ (S' : Subgroup MarkedCubicRecognition.HeisenbergExtension)) = 4 := by
    calc
      _ = Nat.card (W ⊓ centralizer (S : Set X) : Subgroup X) := by
        simpa only [ρ,S',Sylow.coe_mapSurjective,Sylow.coe_coe] using
          Nat.card_congr (NormalElementaryQuotient.fixedSpaceEquiv W q hq hker S)
      _ = 4 := by rw [hfixed,hZ]
  have hFdim : Module.finrank (ZMod 2)
      (fixedSpace ρ (S' : Subgroup MarkedCubicRecognition.HeisenbergExtension)) ≤ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hFcard
    have hh : Module.finrank (ZMod 2)
        (fixedSpace ρ (S' : Subgroup MarkedCubicRecognition.HeisenbergExtension)) = 2 :=
      Nat.pow_right_injective (by decide : 2 ≤ 2) hFcard
    exact hh.le
  have hdim := MarkedCubicRecognition.heisenberg_finrank_six ρ
    (NormalElementaryQuotient.representation_injective W q hq hker) S' hFdim
  rw [←Nat.card_congr (Additive.toMul : Additive W ≃ W),
    Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim]
  norm_num

end MarkedCubicRecognition
