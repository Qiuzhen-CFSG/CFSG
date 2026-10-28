module
public import Theory.GroupAction.MarkedCubicRecognition.BinaryDegree
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.GroupTheory.PResidual.OddImage
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The literal central three-residual in the Heisenberg alternative

The native Heisenberg subgroup is exactly the three-core. Its central
cubic has no fixed vectors in a faithful binary action with a Sylow fixed
plane. Taking the full preimage of this intrinsic center in X/O₂(X),
then its two-residual, preserves the central cubic image. Descent through
the same kernel quotient therefore makes this actual residual fixed-point-free
on the original omega module. Relative normality is retained upstairs.

The original-pair application, including escape from N_G(L), is in
Chapter13 Section04 `Amalgam.CentralResidual`.
Source: Aschbacher--Smith 13.4.7(3), printed p.903.
-/

open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
public noncomputable section
namespace MarkedCubicRecognition
local instance : Finite HeisenbergExtension := Finite.of_equiv (HeisenbergPrime 3 × Four)
  (SemidirectProduct.equivProd (N := HeisenbergPrime 3) (G := Four)
    (φ := heisenbergAction)).symm

theorem heisenberg_threeCore_eq : pCore 3 HeisenbergExtension =
    (SemidirectProduct.inl : HeisenbergPrime 3 →* HeisenbergExtension).range := by
  let P : Subgroup HeisenbergExtension := SemidirectProduct.inl.range
  let r : HeisenbergExtension →* Four := SemidirectProduct.rightHom
  have he : P = r.ker := SemidirectProduct.range_inl_eq_ker_rightHom
  let : P.Normal := he ▸ inferInstance
  have hP : Nat.card P = 27 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective
      (SemidirectProduct.inl_injective (φ := heisenbergAction))).toEquiv,
      HeisenbergPrime.card]
    norm_num
  have hfour : IsPGroup 2 Four := IsPGroup.of_card (n := 2) (by
    norm_num [Four,C2,Nat.card_prod,Nat.card_zmod])
  apply le_antisymm
  · rw [show (SemidirectProduct.inl : HeisenbergPrime 3 →* HeisenbergExtension).range = r.ker from he]
    apply (Subgroup.map_eq_bot_iff _).mp
    have hd := IsPGroup.disjoint_of_ne 3 2 (by decide)
      ((pCore 3 HeisenbergExtension).map r) ((pCore 3 HeisenbergExtension).map r)
      (pCore_isPGroup.map r) (hfour.to_subgroup _)
    simpa only [inf_idem] using hd.eq_bot
  · exact le_sSup ⟨inferInstance,IsPGroup.of_card (n := 3) hP⟩

theorem heisenberg_center_fixedSpace_eq_bot
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) HeisenbergExtension V)
    (hf : Function.Injective ρ) (S : Sylow 2 HeisenbergExtension)
    (hfix : Module.finrank (ZMod 2) (fixedSpace ρ (S : Subgroup HeisenbergExtension)) ≤ 2) :
    fixedSpace ρ ((center (pCore 3 HeisenbergExtension)).map (pCore 3 HeisenbergExtension).subtype) = ⊥ := by
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
  rw [heisenberg_threeCore_eq]
  exact (ExtraspecialSmallFixedSpace.finrank_six ρ hf P S hP hn S.isPGroup' hS hfix).2

theorem heisenberg_threeCore_center_card :
    Nat.card ((center (pCore 3 HeisenbergExtension)).map
      (pCore 3 HeisenbergExtension).subtype) = 3 := by
  rw [card_map_of_injective (pCore 3 HeisenbergExtension).subtype_injective,
    heisenberg_threeCore_eq]
  let e : HeisenbergPrime 3 ≃* (SemidirectProduct.inl :
      HeisenbergPrime 3 →* HeisenbergExtension).range :=
    MonoidHom.ofInjective SemidirectProduct.inl_injective
  let : IsExtraspecial 3 (SemidirectProduct.inl :
      HeisenbergPrime 3 →* HeisenbergExtension).range :=
    IsExtraspecial.of_mulEquiv e (HeisenbergPrime.isExtraspecial (by decide))
  exact IsExtraspecial.center_order_p 3 _

/-- The full preimage of the center of the three-core in the two-core quotient. -/
@[expose] def centralThreePreimage (X : Type*) [Group X] : Subgroup X :=
  ((center (pCore 3 (X ⧸ pCore 2 X))).map (pCore 3 (X ⧸ pCore 2 X)).subtype).comap
    (QuotientGroup.mk' (pCore 2 X))

/-- The source subgroup Y₂ is the two-residual of that full preimage. -/
@[expose] def centralThreeResidual (X : Type*) [Group X] : Subgroup X :=
  (pResidual 2 (centralThreePreimage X)).map (centralThreePreimage X).subtype

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem centralThreeResidual_normal : (centralThreeResidual X).Normal := by
  let : (((center (pCore 3 (X ⧸ pCore 2 X))).map
    (pCore 3 (X ⧸ pCore 2 X)).subtype)).Normal := inferInstance
  let : (centralThreePreimage X).Normal := inferInstanceAs
    (Subgroup.comap (QuotientGroup.mk' (pCore 2 X))
      ((center (pCore 3 (X ⧸ pCore 2 X))).map (pCore 3 (X ⧸ pCore 2 X)).subtype)).Normal
  exact ConjAct.normal_of_characteristic_of_normal

theorem centralThreeResidual_image
    (e : (X ⧸ pCore 2 X) ≃* HeisenbergExtension) :
    (centralThreeResidual X).map (QuotientGroup.mk' (pCore 2 X)) =
      (center (pCore 3 (X ⧸ pCore 2 X))).map (pCore 3 (X ⧸ pCore 2 X)).subtype := by
  let Q := X ⧸ pCore 2 X
  let C := (center (pCore 3 Q)).map (pCore 3 Q).subtype
  have hm : C.map e.toMonoidHom = (center (pCore 3 HeisenbergExtension)).map
      (pCore 3 HeisenbergExtension).subtype := by
    dsimp only [C]
    rw [map_embeddedCenter _ _ e.injective,pCore_map_iso]
  have hC : Nat.card C = 3 := by
    rw [←card_map_of_injective (f := e.toMonoidHom) e.injective,hm,heisenberg_threeCore_center_card]
  change ((pResidual 2 (centralThreePreimage X)).map (centralThreePreimage X).subtype).map _ = C
  rw [map_embedded_pResidual,centralThreePreimage,
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  change (pResidual 2 C).map C.subtype = C
  have ht : pResidual 2 C = ⊤ := by
    apply top_unique
    intro c _
    apply mem_pResidual_of_orderOf_coprime
    exact (by decide : Nat.Coprime 2 3).of_dvd_right (hC ▸ orderOf_dvd_natCard c)
  rw [ht,←MonoidHom.range_eq_map,range_subtype]

/-- The same original kernel quotient makes the literal central residual
fixed-point-free on a reduced omega module with a central four-group. -/
theorem centralThreeResidual_fixed_free
    (S : Sylow 2 X) (W : Subgroup X) [W.Normal] [IsElementaryAbelian 2 W]
    (hseed : omegaOneCenterAmbient (S : Subgroup X) ≤ W)
    (hZ : Nat.card (omegaOneCenterAmbient (S : Subgroup X)) = 4)
    (hk : centralizer (W : Set X) = pCore 2 X)
    (e : (X ⧸ pCore 2 X) ≃* HeisenbergExtension) :
    W ⊓ centralizer (centralThreeResidual X : Set X) = ⊥ := by
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
  have hFcard : Nat.card (fixedSpace ρ (S' : Subgroup HeisenbergExtension)) = 4 := by
    calc
      _ = Nat.card (W ⊓ centralizer (S : Set X) : Subgroup X) := by
        simpa only [ρ,S',Sylow.coe_mapSurjective,Sylow.coe_coe] using
          Nat.card_congr (NormalElementaryQuotient.fixedSpaceEquiv W q hq hker S)
      _ = 4 := by rw [hfixed,hZ]
  have hFdim : Module.finrank (ZMod 2) (fixedSpace ρ (S' : Subgroup HeisenbergExtension)) ≤ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hFcard
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2) hFcard).le
  have hz := heisenberg_center_fixedSpace_eq_bot ρ
    (NormalElementaryQuotient.representation_injective W q hq hker) S' hFdim
  have hm : (centralThreeResidual X).map q =
      (center (pCore 3 HeisenbergExtension)).map (pCore 3 HeisenbergExtension).subtype := by
    dsimp only [q]
    rw [←map_map,centralThreeResidual_image e,map_embeddedCenter _ _ e.injective,
      pCore_map_iso]
  apply bot_unique
  intro w hw
  let v : Additive W := Additive.ofMul ⟨w,hw.1⟩
  have hv := (NormalElementaryQuotient.mem_fixedSpace_image W q hq hker
    (centralThreeResidual X) v).mpr hw.2
  rw [hm,hz] at hv
  have hv0 : v = 0 := hv
  exact congrArg (fun a : Additive W => (a.toMul : X)) hv0
end MarkedCubicRecognition
