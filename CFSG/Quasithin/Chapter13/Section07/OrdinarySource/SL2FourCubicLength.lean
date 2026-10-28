module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.ComponentNormality
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.CoverProjection
public import Theory.Representation.SL2FourNaturalOrbits.CubicFixedSpace
public import Theory.Representation.BinaryConjugationSection.CubicLength
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Actor
public import Theory.GroupTheory.InvolutionCentralizerControl
/-!
# Cubic length on the original natural SL₂(4) source span

An order-three subgroup survives the component two-core with the same order.
The actual natural central cover preserves its fixed index, since the cover
kernel is fixed. The literal conjugation section then transfers fixed index
16 to cubic length two on U_H; the source line has cubic length zero.

Source: Aschbacher–Smith, 13.7.13 and the SL₂(4) case of 13.7.21,
printed pp.943 and 945–946.
-/
public section
open Subgroup Representation Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section08.Source
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ModelExclusions
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Utilde H V₃ V₁)]
include d

/-- Cubics in the original local residual have natural fixed index 16. -/
theorem source_sl2Four_cubic_fixedIndex
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Hstar H) (Additive (Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* SL2FourNatural.SL)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH SL2FourNatural.PointCommutator.representation eK)
    (A : Subgroup G) (hAL : A ≤ sourceOne L T V₁) (hA : Nat.card A = 3) :
    BinaryFixedPoints.fixedIndex
      (ρ.comp ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion (hAL.trans (hL₁K.trans hKH))))) = 16 := by
  obtain ⟨_,hgen⟩ := component_normal_and_span_of_one_le d hH hF9 hKH hK hL₁K
  obtain ⟨p,hp⟩ := exists_cover_of_section hKH hK ρ hρ hgen.symm
    SL2FourNatural.PointCommutator.representation eK hs
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hqker : q.ker = pCore 2 K := by
    ext k
    change eK (QuotientGroup.mk' (pCore 2 K) k) = 1 ↔ k ∈ pCore 2 K
    rw [eK.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff k
  let hAK := hAL.trans hL₁K
  let B := A.subgroupOf K
  have hB : Nat.card B = 3 := (Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv).trans hA
  let C := B.map q
  have hC : Nat.card C = 3 := GLS3.Chapter5.cubic_image_card_of_two_kernel q
    (hqker.symm ▸ (pCore_isPGroup (p := 2) (G := K))) B hB
  let j := (subgroupOfEquivOfLe hAK).symm
  let f : A →* C := (q.subgroupMap B).comp j.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective B).comp j.surjective
  let σ := SL2FourNatural.PointCommutator.representation.comp C.subtype
  let τ := ρ.comp ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion (hAL.trans (hL₁K.trans hKH))))
  have he (a : A) (u) : p (τ a u) = (σ.comp f) a (p u) := by
    have hfa : C.subtype (f a) = eK (QuotientGroup.mk' (pCore 2 K) (inclusion hAK a)) := rfl
    change p (ρ (QuotientGroup.mk' (pCore 2 H) (inclusion (hAL.trans (hL₁K.trans hKH)) a)) u) =
      SL2FourNatural.PointCommutator.representation (C.subtype (f a)) (p u)
    rw [hfa]
    have hh := IntertwiningMap.isIntertwining _ _ p (eK (QuotientGroup.mk' (pCore 2 K) (inclusion hAK a))) u
    have hie : inclusion hKH (inclusion hAK a) = inclusion (hAL.trans (hL₁K.trans hKH)) a := Subtype.ext rfl
    simpa only [τ,σ,f,j,q,MonoidHom.comp_apply,modelActor_mk,hie] using hh
  let : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨a,ha⟩ := IsCyclic.exists_generator (α := A)
  have hc : a^3=1 := hA ▸ pow_card_eq_one'
  have hk (u) (hu : p u=0) : τ a u=u := by
    have hh := hp.2.1 hu (eK (QuotientGroup.mk' (pCore 2 K) (inclusion hAK a)))
    have hie : inclusion hKH (inclusion hAK a) = inclusion (hAL.trans (hL₁K.trans hKH)) a := Subtype.ext rfl
    simpa only [τ,MonoidHom.comp_apply,modelActor_mk,hie] using hh
  have hidx := BinaryFixedPoints.fixedIndex_eq_of_surjective_trivial_kernel
    τ (σ.comp f) a ha hc p.toLinearMap hp.1 he hk
  rw [hidx]
  let := BinaryFixedPoints.action (σ.comp f)
  have ht := BinaryFixedPoints.fixedIndex_eq_of_equivariant σ f hf
    (MulEquiv.refl (Multiplicative SL2FourNatural.V)) (fun _ _ => rfl)
  exact ht.trans (SL2FourNatural.cubic_fixedIndex C hC)


-- The normal instance also occurs in the quotient's elementary binary module structure.
set_option linter.unusedSectionVars false in
/-- The literal conjugation section gives cubic length two on the full source span. -/
theorem source_sl2Four_uh_cubic_length
    [IsElementaryAbelian 2 (UH H V₃)]
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Hstar H) (Additive (Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* SL2FourNatural.SL)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH SL2FourNatural.PointCommutator.representation eK)
    (c : BinaryConjugationSection H (UH H V₃) V₁ (ρ.comp (QuotientGroup.mk' (pCore 2 H))))
    (A : Subgroup G) (hAL : A ≤ sourceOne L T V₁) (hA : Nat.card A = 3) :
    conjugationCubicLength A (UH H V₃) = 2 := by
  have hAH := hAL.trans (hL₁K.trans hKH)
  have hpA : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hpU : IsPGroup 2 (UH H V₃) := IsElementaryAbelian.isPGroup 2 _
  have hh := c.sectionCubicLength_eq_fixedIndex A hAH hpA hpU
  have hi := source_sl2Four_cubic_fixedIndex d hH hF9 hKH hK hL₁K ρ hρ eK hs A hAL hA
  have he : (ρ.comp (QuotientGroup.mk' (pCore 2 H))).comp (inclusion hAH) =
      ρ.comp ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hAH)) := rfl
  rw [he,hi] at hh
  have hAn : A ≤ normalizer (V₁ : Set G) := hAL.trans ((one_le L T V₁).trans inf_le_right)
  have hAc : A ≤ centralizer (V₁ : Set G) :=
    hAn.trans (Subgroup.normalizer_le_centralizer_of_card_two V₁ d.line_card)
  have hz : conjugationCubicLength A V₁ = 0 := by
    unfold conjugationCubicLength
    rw [relIndex_eq_one.mpr (le_centralizer_iff.mp hAc)]
    decide
  unfold sectionCubicLength at hh
  rw [hz] at hh
  norm_num at hh
  exact hh
end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
