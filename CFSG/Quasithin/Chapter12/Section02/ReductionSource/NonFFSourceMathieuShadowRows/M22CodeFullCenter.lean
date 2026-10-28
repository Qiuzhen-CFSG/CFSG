module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeHeldReduction
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeCoverCenter
public import Theory.GroupTheory.PrimeOrderLift

-- Evaluate only the original component quotient on representatives.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# The original M22 covering center in the remaining Held branch

The full center of the original L/O₂(L) is isomorphic to the center of
its original involution residual modulo its two-core. This follows by
restricting the original covering map to the perfect hexad preimage and
transporting across its two-kernel. Its order divides three.

If this center is nontrivial, a cubic in the original hexad kernel fixes
the original module. The established odd-normalizer control then places
its ambient normalizer inside N_G(L). In the remaining inside-core Held
configuration, this same cubic survives in the actual Held quotient.
The final theorem retains both this alternative and the centerless
alternative with the full original A₆ residual quotient. It does not
exclude Held, remove hcore, or assert the final M24-cocode selection.

Source: Aschbacher--Smith 8.2.2(1), printed p.715, using H.13 and
I.1.3(4), refs/quasithin.pdf. The possible odd center of the original
cover is retained throughout the literal subgroup and quotient maps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.Centralizer Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The original residual and full component retain the same covering center. -/
theorem sourceOrbit_m22_code_residual_center_equiv
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    Nonempty (center (localResidual L z ⧸ pCore 2 (localResidual L z)) ≃*
      center (L ⧸ pCore 2 L)) := by
  obtain ⟨B,hB,c,hc,hval,hker,hpre⟩ := D.sourceOrbit_m22_code_centralizer_cover d z hz hne
  let C := L ⊓ centralizer ({(z : G)} : Set G)
  let q := QuotientGroup.mk' (pCore 2 L)
  let k := d.componentEquiv.toMonoidHom.comp (D.orbitComponentQuotientHom h)
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  let : IsQuasisimple D.orbitComponent := D.orbitComponent_quasisimple h
  let : IsQuasisimple M22 := IsQuasisimple.of_mulEquiv d.componentEquiv
  let cf : Covering (L ⧸ pCore 2 L) M22 := {
    toMonoidHom := k
    surjective := d.componentEquiv.surjective.comp (D.orbitComponentQuotientHom_surjective h) }
  let P := (MulAction.stabilizer M22 B).comap k
  let : Group.IsPerfect P := NormalizedShadowRows.code_hexad_preimage_perfect
    (PerfectCentralCovering.ofCovering cf) hB
  have he : C.subgroupOf L = P.comap q := hpre
  let e : C ≃* P.comap q := (subgroupOfEquivOfLe (show C ≤ L from inf_le_left)).symm.trans
    (MulEquiv.subgroupCongr he)
  let f := q.subgroupComap P
  have hf : Function.Surjective f :=
    q.subgroupComap_surjective_of_surjective P (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    have hfk : f.ker = q.ker.subgroupOf (P.comap q) := by
      ext a
      change f a = 1 ↔ q a = 1
      exact Subtype.ext_iff
    rw [hfk,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let r := f.comp e.toMonoidHom
  have hr : Function.Surjective r := hf.comp e.surjective
  have hrk : IsPGroup 2 r.ker := by
    rw [←MonoidHom.comap_ker]
    exact hk.comap_of_injective _ e.injective
  let s := r.comp (solvableResidual C).subtype
  have hs : Function.Surjective s := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,range_subtype,map_solvableResidual_eq r hr,solvableResidual_eq_top]
  have hsk : IsPGroup 2 s.ker := by
    rw [←MonoidHom.comap_ker]
    exact hrk.comap_subtype
  let b : solvableResidual C ≃* localResidual L z :=
    (solvableResidual C).equivMapOfInjective C.subtype C.subtype_injective
  let bq := QuotientGroup.congr _ _ b.symm (pCore_map_iso 2 b.symm)
  let a := bq.trans (s.pCoreQuotientEquiv hs hsk)
  obtain ⟨az⟩ := NormalizedShadowRows.code_hexad_cover_center_equiv
    (PerfectCentralCovering.ofCovering cf) (pCore_quotient_pCore_eq_bot 2) hB
  exact ⟨(centerCongr a).trans az⟩

/-- Removing the original two-core leaves at most the cubic multiplier kernel. -/
theorem sourceOrbit_m22_code_full_center_card_dvd_three
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation) : Nat.card (center (L ⧸ pCore 2 L)) ∣ 3 := by
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  let : IsQuasisimple D.orbitComponent := D.orbitComponent_quasisimple h
  let : IsQuasisimple M22 := IsQuasisimple.of_mulEquiv d.componentEquiv
  let cf : Covering (L ⧸ pCore 2 L) M22 := {
    toMonoidHom := d.componentEquiv.toMonoidHom.comp (D.orbitComponentQuotientHom h)
    surjective := d.componentEquiv.surjective.comp (D.orbitComponentQuotientHom_surjective h) }
  exact NormalizedShadowRows.code_cover_center_card_dvd_three
    (PerfectCentralCovering.ofCovering cf) (pCore_quotient_pCore_eq_bot 2)

omit [Finite G] in
private theorem code_kernel_centralizes
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (l : L) (hl : D.orbitComponentHom l = 1) :
    (l : G) ∈ centralizer (D.sourceOrbit : Set G) := by
  let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
  have hr : m22OuterCodeRepresentation.comp m22ToPairStabilizer = m22CodeRepresentation := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    exact m22OuterCodeRepresentation_restrict g v
  intro v hv
  let w : Additive D.sourceOrbit := Additive.ofMul ⟨v,hv⟩
  have he := D.sourceOrbit_m22_component_coordinates m22CodeRepresentation
    m22OuterCodeRepresentation hr d l w
  have hm : d.componentEquiv (D.orbitComponentHom l) = 1 :=
    (congrArg d.componentEquiv hl).trans d.componentEquiv.map_one
  rw [hm,map_one] at he
  have hh := congrArg (fun w : Additive D.sourceOrbit => (w.toMul : G)) (E.injective he)
  change (l : G) * v * (l : G)⁻¹ = v at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- A nontrivial covering center supplies an actual cubic in the original
point residual and original module kernel, surviving its two-core quotient. -/
theorem sourceOrbit_m22_code_residual_cubic_kernel
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hcub : Nat.card (center (localResidual L z ⧸ pCore 2 (localResidual L z))) = 3) :
    ∃ x : localResidual L z, orderOf x = 3 ∧
      (x : G) ∈ centralizer (D.sourceOrbit : Set G) ∧
      QuotientGroup.mk' (pCore 2 (localResidual L z)) x ≠ 1 := by
  obtain ⟨B,hB,c,hc,hval,_,_⟩ := D.sourceOrbit_m22_code_centralizer_cover d z hz hne
  let C := L ⊓ centralizer ({(z : G)} : Set G)
  let R := localResidual L z
  let j : R →* C := inclusion (localResidual_le L z)
  let f := c.comp j
  let b : solvableResidual C ≃* R :=
    (solvableResidual C).equivMapOfInjective C.subtype C.subtype_injective
  let : Group.IsPerfect (MulAction.stabilizer M22 B) := m22HexadStabilizer_isPerfect hB
  have hs : Function.Surjective (c.comp (solvableResidual C).subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,range_subtype,map_solvableResidual_eq c hc,solvableResidual_eq_top]
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := hs y
    exact ⟨b x,hx⟩
  obtain ⟨_,⟨e⟩⟩ := D.sourceOrbit_m22_code_centralizer_projective h d z hz hne
  obtain ⟨x,hfx,hx,hqx⟩ := NormalizedShadowRows.code_hexad_cubic_kernel hB f hf e hcub
  refine ⟨x,hx,?_,hqx⟩
  let l : L := ⟨x,(localResidual_le L z x.property).1⟩
  have hl : D.orbitComponentHom l = 1 := by
    exact d.componentEquiv.map_eq_one_iff.mp
      ((hval (j x)).symm.trans (congrArg Subtype.val hfx))
  exact D.code_kernel_centralizes d l hl

/-- Odd-normalizer control applies to the actual cubic lifted from the
remaining covering center of the original involution residual. -/
theorem sourceOrbit_m22_code_residual_cubic_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hcub : Nat.card (center (localResidual L z ⧸ pCore 2 (localResidual L z))) = 3) :
    ∃ x : G, orderOf x = 3 ∧ x ∈ localResidual L z ∧
      x ∈ centralizer (D.sourceOrbit : Set G) ∧
      normalizer (zpowers x : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨x,hx,hxV,_⟩ := D.sourceOrbit_m22_code_residual_cubic_kernel
    h.toHypothesis1221 d z hz hne hcub
  have ho : orderOf (x : G) = 3 := (orderOf_coe x).trans hx
  have hm : HasMathieuCentralQuotient D.orbitComponent := by
    have hzC : center D.orbitComponent = ⊥ := by
      have he := FixedElementary.map_center d.componentEquiv
      rw [m22_center_eq_bot] at he
      exact (map_eq_bot_iff_of_injective _ d.componentEquiv.injective).mp he
    exact Or.inr (Or.inl ⟨((QuotientGroup.quotientMulEquivOfEq hzC).trans
      QuotientGroup.quotientBot).trans d.componentEquiv⟩)
  refine ⟨x,ho,x.property,hxV,?_⟩
  apply D.sourceOrbit_mathieu_odd_normalizer_le h hmany hV hm hnon
  · intro he
    have hx1 := mem_bot.mp (he ▸ mem_zpowers (x : G))
    simp only [hx1,orderOf_one] at ho
    omega
  · apply zpowers_le.mpr
    exact ⟨L.le_normalizer (localResidual_le L z x.property).1,hxV⟩
  · rw [Nat.card_zpowers,ho]
    decide

/-- The remaining Held component keeps either the full original A6 section
or an actual controlled cubic from the original cover, surviving in Held. -/
theorem sourceOrbit_m22_code_inside_core_held_cover_alternatives
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    let X := (pResidual 2 H).map H.subtype
    ∃ z : D.sourceOrbit, z ≠ 1 ∧ orderOf (z : G) = 2 ∧
      H ≤ centralizer ({(z : G)} : Set G) ∧
      ∃ P K : Subgroup G,
        Chapter1.XiEmbedding.LocalInput 3 (T : Subgroup G) X P (centralizer ({(z : G)} : Set G)) ∧
        K ∈ cComponentsIn (centralizer ({(z : G)} : Set G)) ∧
        localResidual L z ≤ K ∧
        centralizer ({(z : G)} : Set G) ≤ normalizer (K : Set G) ∧
        IsQuasisimple (K ⧸ pCore 2 K) ∧ center (K ⧸ pCore 2 K) = ⊥ ∧
        X ≤ K ∧ Nonempty (P ≃* Chapter1.XiEmbedding.Plane 3) ∧
        ∃ eK : (K ⧸ pCore 2 K) ≃* Held.He,
          (center (L ⧸ pCore 2 L) = ⊥ ∧
            Nonempty ((localResidual L z ⧸ pCore 2 (localResidual L z)) ≃*
              alternatingGroup (Fin 6))) ∨
          (Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
            ∃ x : K, orderOf x = 3 ∧ (x : G) ∈ localResidual L z ∧
              (x : G) ∈ centralizer (D.sourceOrbit : Set G) ∧
              orderOf (eK (QuotientGroup.mk' (pCore 2 K) x)) = 3 ∧
              normalizer (zpowers (x : G) : Set G) ≤ normalizer (L : Set G)) := by
  obtain ⟨z,hne,ho,hHC,P,K,hin,hK,hRK,hnK,hq,hzK,hXK,hP,⟨eK⟩,hR,⟨eR⟩⟩ :=
    D.sourceOrbit_m22_code_inside_core_held_component h hmany hV hnon d hH hcore
  have hz : (z : G) ∈ centralizer (T : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hHC (hH.1.1.2 ht))
  obtain ⟨eZ⟩ := D.sourceOrbit_m22_code_residual_center_equiv h.toHypothesis1221 d z hz hne
  have hd := D.sourceOrbit_m22_code_full_center_card_dvd_three h.toHypothesis1221 d
  refine ⟨z,hne,ho,hHC,P,K,hin,hK,hRK,hnK,hq,hzK,hXK,hP,eK,?_⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · have hr1 := (Nat.card_congr eZ.toEquiv).trans h1
    exact Or.inl ⟨card_eq_one.mp h1,
      ⟨GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6 eR hr1⟩⟩
  · have hr3 := (Nat.card_congr eZ.toEquiv).trans h3
    obtain ⟨x,hx,hxR,hxV,hNx⟩ := D.sourceOrbit_m22_code_residual_cubic_normalizer
      h hmany hV hnon d z hz hne hr3
    let xK : K := ⟨x,hRK hxR⟩
    have hxK : orderOf xK = 3 := (orderOf_coe xK).symm.trans hx
    have hk : IsPGroup 2 (QuotientGroup.mk' (pCore 2 K)).ker := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup
    refine Or.inr ⟨h3,xK,hxK,hxR,hxV,?_,hNx⟩
    exact (eK.orderOf_eq _).trans
      (((QuotientGroup.mk' (pCore 2 K)).orderOf_map_eq_of_coprime_of_isPGroup_ker
        hk xK (by rw [hxK]; decide)).trans hxK)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
