module
public import Theory.Representation.InvertedCubicSeed
public import Theory.GroupAction.MarkedCubicRecognition.CentralResidual
public import Theory.Representation.NormalElementaryQuotient.SubgroupSpaceTransport
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The four-dimensional orbit of the actual central residual

Every Sylow two-subgroup of the marked Heisenberg extension contains an
inverter of the intrinsic central cubic. Its fixed-point-free action
doubles the dimension of the Sylow fixed seed. The same original quotient
map identifies module differences with group commutators, giving order
sixteen for [Z,Y₂]. The seed lies in these commutators, so they are also
exactly its full Y₂-conjugate span.

Here Y₂ is the two-residual of the full preimage of Z(O₃(X/O₂(X))), with
no chosen lift or movement hypothesis. `Amalgam.CentralResidual` applies
this to the original solvable pair in Chapter13 Section04.
Source: Aschbacher--Smith 13.4.7(3), printed p.903.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender


namespace MarkedCubicRecognition
local instance : Finite HeisenbergExtension := Finite.of_equiv (HeisenbergPrime 3 × Four)
  (SemidirectProduct.equivProd (N := HeisenbergPrime 3) (G := Four)
    (φ := heisenbergAction)).symm

/-- Every Sylow two-subgroup contains an inverter of the intrinsic central cubic. -/
theorem center_generator_inverted (S : Sylow 2 HeisenbergExtension) :
    ∃ c s : HeisenbergExtension,
      zpowers c = (center (pCore 3 HeisenbergExtension)).map (pCore 3 HeisenbergExtension).subtype ∧
      orderOf c = 3 ∧ s ∈ (S : Subgroup HeisenbergExtension) ∧ s*c = c^2*s := by
  let z : HeisenbergPrime 3 := ⟨0,0,1⟩
  let c : HeisenbergExtension := SemidirectProduct.inl z
  have hc3 : c^3 = 1 := by
    rw [show c = SemidirectProduct.inl z from rfl,←map_pow,
      HeisenbergPrime.pow_prime (by decide),map_one]
  have hcn : c ≠ 1 := by
    intro he
    have hh := congrArg (fun x : HeisenbergExtension => x.left.c) he
    change (1 : ZMod 3) = 0 at hh
    exact one_ne_zero hh
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hcn
  have hcZ : c ∈ (center (pCore 3 HeisenbergExtension)).map
      (pCore 3 HeisenbergExtension).subtype := by
    rw [heisenberg_threeCore_eq]
    let P : Subgroup HeisenbergExtension := SemidirectProduct.inl.range
    let e : HeisenbergPrime 3 ≃* P := MonoidHom.ofInjective SemidirectProduct.inl_injective
    have hz : z ∈ center (HeisenbergPrime 3) := (HeisenbergPrime.mem_center_iff z).mpr ⟨rfl,rfl⟩
    exact ⟨e z,(centerCongr e ⟨z,hz⟩).property,rfl⟩
  have hgen : zpowers c = (center (pCore 3 HeisenbergExtension)).map
      (pCore 3 HeisenbergExtension).subtype := eq_of_le_of_card_ge (zpowers_le.mpr hcZ)
    (by rw [Nat.card_zpowers,hco,heisenberg_threeCore_center_card])
  let r : HeisenbergExtension →* Four := SemidirectProduct.rightHom
  have hr : Function.Surjective r := SemidirectProduct.rightHom_surjective
  let S' := S.mapSurjective hr
  have hfour : IsPGroup 2 Four := IsPGroup.of_card (n := 2) (by
    norm_num [Four,C2,Nat.card_prod,Nat.card_zmod])
  have htop : (S' : Subgroup Four) = ⊤ := top_unique
    ((hfour.to_subgroup ⊤).le_sylow_of_normal S')
  have hf : first ∈ (S : Subgroup HeisenbergExtension).map r := by
    change first ∈ (S' : Subgroup Four)
    rw [htop]
    trivial
  obtain ⟨s,hs,hsr⟩ := hf
  refine ⟨c,s,hgen,hco,hs,?_⟩
  have hsr' : s.right = first := hsr
  apply SemidirectProduct.ext
  · simp only [c,SemidirectProduct.mul_left,SemidirectProduct.mul_right,pow_two,
      SemidirectProduct.left_inl,SemidirectProduct.right_inl,one_mul,map_one,
      MulAut.one_apply,hsr',heisenbergAction_first]
    change s.left * leftFlip z = (z*z)*s.left
    ext <;> simp [z,leftFlip,show -(1 : ZMod 3) = 2 by decide]
    ring
  · simp [c,pow_two,hsr']
end MarkedCubicRecognition

open Stellmacher
open scoped IsMulCommutative commutatorElement
namespace MarkedCubicRecognition

/-- The source's literal central residual moves the central four-group to
an elementary subgroup of order sixteen, through the same quotient action. -/
theorem centralThreeResidual_seed_span
    {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) (W : Subgroup X) [W.Normal] [IsElementaryAbelian 2 W]
    (hseed : omegaOneCenterAmbient (S : Subgroup X) ≤ W)
    (hZ : Nat.card (omegaOneCenterAmbient (S : Subgroup X)) = 4)
    (hk : centralizer (W : Set X) = pCore 2 X)
    (e : (X ⧸ pCore 2 X) ≃* HeisenbergExtension) :
    conjugateSpanBy (omegaOneCenterAmbient (S : Subgroup X)) (centralThreeResidual X) =
        ⁅omegaOneCenterAmbient (S : Subgroup X),centralThreeResidual X⁆ ∧
      Nat.card (⁅omegaOneCenterAmbient (S : Subgroup X),centralThreeResidual X⁆ : Subgroup X) = 16 := by
  let : Finite HeisenbergExtension := Finite.of_equiv (HeisenbergPrime 3 × Four)
    (SemidirectProduct.equivProd (N := HeisenbergPrime 3) (G := Four)
      (φ := heisenbergAction)).symm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = centralizer (W : Set X) := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',hk]
  let ρ := NormalElementaryQuotient.representation W q hq hker
  let S' := S.mapSurjective hq
  let R := centralThreeResidual X
  let Z := omegaOneCenterAmbient (S : Subgroup X)
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le hseed
  let Z' := NormalElementaryQuotient.subgroupSpace W Z
  have hm : R.map q = (center (pCore 3 HeisenbergExtension)).map
      (pCore 3 HeisenbergExtension).subtype := by
    dsimp only [q,R]
    rw [←map_map,centralThreeResidual_image e,map_embeddedCenter _ _ e.injective,pCore_map_iso]
  obtain ⟨c,s,hgen,hc,hs,hi⟩ := center_generator_inverted S'
  have hf : ∀ v, ρ c v = v → v = 0 := by
    intro v hv
    have hfixed : v ∈ fixedSpace ρ (R.map q) := by
      rw [hm,←hgen]
      exact (mem_fixedSpace_zpowers_iff ρ c v).mpr hv
    have hh := (NormalElementaryQuotient.mem_fixedSpace_image W q hq hker R v).mp hfixed
    have hh0 : (v.toMul : X) = 1 :=
      (centralThreeResidual_fixed_free S W hseed hZ hk e).le ⟨v.toMul.property,hh⟩
    exact Additive.toMul.injective (Subtype.ext hh0)
  have hZS : Z' ≤ fixedSpace ρ (S' : Subgroup HeisenbergExtension) := by
    apply NormalElementaryQuotient.subgroupSpace_fixed_of_centralizes W q hq hker Z S
    intro s hs z hz
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 s hs).symm
  obtain ⟨hmove,hdim⟩ := Representation.InvertedCubicSeed.moved_seed_and_finrank ρ c s hc hi hf Z'
    (fun v hv => hZS hv ⟨s,hs⟩)
  have hZcard : Nat.card Z' = 4 := by
    have hh := Nat.card_congr (NormalElementaryQuotient.subgroupSpaceEquiv W Z hseed).toEquiv
    exact hh.symm.trans ((Nat.card_congr (Additive.toMul : Additive Z ≃ Z)).trans hZ)
  have hZdim : Module.finrank (ZMod 2) Z' = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hZcard
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hZcard
  rw [hZdim,hgen,←hm] at hdim
  rw [hgen,←hm] at hmove
  have hMW : ⁅Z,R⁆ ≤ W :=
    (commutator_mono hseed le_top).trans (commutator_le_left W ⊤)
  let : IsElementaryAbelian 2 (⁅Z,R⁆ : Subgroup X) := IsElementaryAbelian.of_le hMW
  have hMdim : Module.finrank (ZMod 2) (NormalElementaryQuotient.subgroupSpace W ⁅Z,R⁆) = 4 := by
    rw [NormalElementaryQuotient.subgroupSpace_commutator W q hq hker Z R hseed]
    exact hdim
  have hZcomm : Z ≤ ⁅Z,R⁆ := by
    intro z hz
    have hh := hmove (show Additive.ofMul (⟨z,hseed hz⟩ : W) ∈ Z' from hz)
    rw [←NormalElementaryQuotient.subgroupSpace_commutator W q hq hker Z R hseed] at hh
    exact hh
  refine ⟨?_,?_⟩
  · apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      rintro _ ⟨r,hr,z,hz,rfl⟩
      have hc : ⁅r,z⁆ ∈ ⁅Z,R⁆ := by
        rw [commutator_comm]
        exact commutator_mem_commutator hr hz
      have hh := (⁅Z,R⁆).mul_mem hc (hZcomm hz)
      change r*z*r⁻¹ ∈ ⁅Z,R⁆
      have he : ⁅r,z⁆ * z = r*z*r⁻¹ := by
        simp only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one]
      exact he ▸ hh
    · exact (commutator_mono (le_conjugateSpanBy Z R) le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy Z R))
  calc
    _ = Nat.card (Additive (⁅Z,R⁆ : Subgroup X)) :=
      (Nat.card_congr (Additive.toMul : Additive (⁅Z,R⁆ : Subgroup X) ≃ (⁅Z,R⁆ : Subgroup X))).symm
    _ = Nat.card (NormalElementaryQuotient.subgroupSpace W ⁅Z,R⁆) :=
      Nat.card_congr (NormalElementaryQuotient.subgroupSpaceEquiv W ⁅Z,R⁆ hMW).toEquiv
    _ = 16 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hMdim]
      norm_num
end MarkedCubicRecognition
