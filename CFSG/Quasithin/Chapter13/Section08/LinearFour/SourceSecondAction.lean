module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceExteriorTensor
public import Theory.Representation.BinaryParabolicExteriorSquare.PointDisplacement
public import Theory.GroupTheory.ConjugateSpanElementaryQuotient
public import Theory.GroupTheory.PCoreImage
public import Theory.Representation.BinaryConjugationSection.QuotientSection

/-!
# The actual second-tensor quotient and its three-dimensional seed

The original I₂ core identity puts the elementary V_H inside Q₂. The
natural point-quotient kernel and the compatible exterior marking then give
[Q₂,V_H] ≤ U₀. A normalized commutator preimage propagates this bound to
V₀ = ⟨V_H^{G₂}⟩. Consequently V₀/U₀ is abelian and has exponent two;
its literal conjugation action descends through the supplied G₂/Q₂ map.
V₀ itself is not assumed elementary abelian.

The original exterior three-space computes the V_H-image dimension as
three and proves K₂-minimality of the interval U₀ ≤ V_H. The final source
application constructs the quotient action and this seed from the natural
and exterior markings, retaining the original I₂ and quotient maps. The
already established same-g intersection makes the seed and its actual g
translate disjoint, and the G₂ orbit generates the whole quotient.

The original-seed consumer calls SourceExteriorTensor to construct its
compatible exterior marking first, so neither that marking nor an action
on V₀/U₀ is supplied. The original relatively normal I₂ contains Q_H and
retains its exact two-core centralizer identity throughout.
Identification of this generated quotient with the two second-tensor rows,
extra-line movement, chief accounting and full 13.8.28 remain with this
owner; earlier 13.8.27 and final 13.8.1 retain their existing source owners.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29(4), printed p.964, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement MatrixGroups
open Atlas.Order20160A8.Bivectors
open Representation.BinaryParabolicExteriorSquare.PlaneSpan

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G K W : Type*} [Group G] [Group K] [AddCommGroup W] [Module (ZMod 2) W]

/-- The original relatively normal I₂ and its exact core place V_H in Q₂. -/
theorem source_VH_le_Q2_of_I2
    (H VH V2 A : Subgroup G) [IsElementaryAbelian 2 VH]
    (hVH : VH ≤ H) (hnVH : H ≤ normalizer VH) (h2V : V2 ≤ VH)
    (hQA : H.pCoreIn 2 ≤ A) (hAG : A ≤ G2 V2)
    (hnA : G2 V2 ≤ normalizer A)
    (hAc : A.pCoreIn 2 = A ⊓ centralizer (V2:Set G)) : VH ≤ Q2 V2 := by
  have hVQ := le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 VH) hVH hnVH
  have hc : VH ≤ centralizer (V2:Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative VH)).trans
      (centralizer_le h2V)
  have hVA : VH ≤ A.pCoreIn 2 := hAc.symm ▸ le_inf (hVQ.trans hQA) hc
  exact hVA.trans (pCoreIn_mono_of_normalizes hAG hnA)

/-- The natural point kernel and exterior marking bound the actual core displacement. -/
theorem source_VH_core_commutator
    (H UH VH V1 V2 : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π₄ : H →* SL(4,ZMod 2))
    (hnatural : ∀ h x, ρ h x = (π₄ h).val.mulVec x)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {Pi.single 0 1})
    (ξ : Representation (ZMod 2) H Six)
    (p : BinaryConjugationSection H VH UH ξ)
    (hact : ∀ h x, ξ h x = exteriorMap (π₄ h).val x)
    (hfirst : p.imageSpace (U0 UH V2) = firstSpace)
    (hcore : Q2 V2 ≤ H) (hc : ⁅Q2 V2,UH⁆ ≤ V2) :
    ⁅Q2 V2,VH⁆ ≤ U0 UH V2 := by
  apply commutator_le.mpr
  intro a ha v hv
  let aH : H := ⟨a,hcore ha⟩
  have hdisp (w : Fin 4 → ZMod 2) :
      (π₄ aH).val.mulVec w - w ∈ Submodule.span (ZMod 2) {Pi.single 0 1} := by
    have hh := d.displacement_range_le_imageSpace_of_commutator_le (Q2 V2) V2 hc aH ha
      (show (ρ aH - 1) w ∈ LinearMap.range (ρ aH - 1) from ⟨w,rfl⟩)
    simpa only [hpoint,LinearMap.sub_apply,Module.End.one_apply,hnatural] using hh
  let z : VH := ⟨⁅a,v⁆, by
    rw [commutatorElement_def]
    exact VH.mul_mem ((mem_normalizer_iff.mp (p.normalized (hcore ha)) v).mp hv)
      (VH.inv_mem hv)⟩
  apply (p.coordinates_mem_imageSpace_iff_of_kernel_le (U0 UH V2) (UH_le_U0 UH V2) z).mp
  have hz : (p.coordinates z).toAdd = ξ aH (p.coordinates ⟨v,hv⟩).toAdd -
      (p.coordinates ⟨v,hv⟩).toAdd := by
    change (p.coordinates
      (⟨a*v*a⁻¹,(mem_normalizer_iff.mp (p.normalized (hcore ha)) v).mp hv⟩ *
        (⟨v,hv⟩:VH)⁻¹)).toAdd = _
    rw [map_mul,map_inv]
    simp only [toAdd_mul,toAdd_inv,←sub_eq_add_neg]
    exact congrArg (fun w => w - (p.coordinates ⟨v,hv⟩).toAdd) (p.equivariant aH ⟨v,hv⟩)
  rw [hz,hact,hfirst]
  exact BinaryParabolicExteriorSquare.exterior_displacement_of_point_displacement _ hdisp _

/-- The same displacement bound extends to every G₂ conjugate of V_H. -/
theorem source_V0_core_commutator (UH VH V2 : Subgroup G)
    (hVG : VH ≤ G2 V2) (hc : ⁅Q2 V2,VH⁆ ≤ U0 UH V2) :
    ⁅Q2 V2,V0 VH V2⁆ ≤ U0 UH V2 := by
  have hQN : G2 V2 ≤ normalizer (Q2 V2 : Set G) :=
    (G2 V2).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (G2 V2)))
  let C := commutatorPreimage (G2 V2) (Q2 V2) (U0 UH V2)
  have hVC : VH ≤ C := le_commutatorPreimage hVG (by rwa [commutator_comm])
  have hGC : G2 V2 ≤ normalizer C := commutatorPreimage_normalized
    (G2 V2) (Q2 V2) (U0 UH V2) (G2 V2) (G2_normalizes_U0 UH V2) (G2 V2).le_normalizer hQN
      (G2_normalizes_U0 UH V2)
  rw [commutator_comm]
  exact (commutator_mono (conjugateSpanBy_le hVC hGC) le_rfl).trans
    (commutator_commutatorPreimage_le (G2 V2) (Q2 V2) (U0 UH V2)
      (G2_normalizes_U0 UH V2))

/-- Construct the elementary quotient action through the supplied map, preserving its literal coordinates. -/
theorem source_second_quotient_action
    {D : Type*} [Group D]
    (UH VH V2 : Subgroup G) [IsElementaryAbelian 2 VH]
    (hUV : U0 UH V2 ≤ VH) (hVQ : VH ≤ Q2 V2)
    (hc : ⁅Q2 V2,VH⁆ ≤ U0 UH V2)
    (π : G2 V2 →* D) (hπ : Function.Surjective π)
    (hπker : π.ker = pCore 2 (G2 V2)) :
    ∃ hn : ((U0 UH V2).subgroupOf (V0 VH V2)).Normal,
      let := hn
      ∃ he : IsElementaryAbelian 2 (V0 VH V2 ⧸ (U0 UH V2).subgroupOf (V0 VH V2)),
        let := he
        ∃ (ξ : Representation (ZMod 2) D
          (Additive (V0 VH V2 ⧸ (U0 UH V2).subgroupOf (V0 VH V2))))
          (q : BinaryConjugationSection (G2 V2) (V0 VH V2) (U0 UH V2) (ξ.comp π)),
          ∀ v : V0 VH V2, (q.coordinates v).toAdd =
            Additive.ofMul (QuotientGroup.mk' ((U0 UH V2).subgroupOf (V0 VH V2)) v) := by
  have hVG := hVQ.trans (Q2_le_G2 V2)
  have hV0G : V0 VH V2 ≤ G2 V2 := conjugateSpanBy_le_self hVG
  have hV0Q : V0 VH V2 ≤ Q2 V2 := conjugateSpanBy_le hVQ
    ((G2 V2).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (G2 V2))))
  have hU0V0 := hUV.trans (VH_le_V0 VH V2)
  have hn : ((U0 UH V2).subgroupOf (V0 VH V2)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hU0V0).mpr (hV0G.trans (G2_normalizes_U0 UH V2))
  let := hn
  have hc0 := source_V0_core_commutator UH VH V2 hVG hc
  have hcc : commutator (V0 VH V2) ≤ (U0 UH V2).subgroupOf (V0 VH V2) := by
    rw [←map_le_map_iff_of_injective (V0 VH V2).subtype_injective,
      (V0 VH V2).map_subtype_commutator,map_subgroupOf_eq_of_le hU0V0]
    exact (commutator_mono hV0Q le_rfl).trans hc0
  let : ((U0 UH V2).subgroupOf (conjugateSpanBy VH (G2 V2))).Normal := hn
  let : IsMulCommutative (conjugateSpanBy VH (G2 V2) ⧸
      (U0 UH V2).subgroupOf (conjugateSpanBy VH (G2 V2))) :=
    Normal.quotient_commutative_iff_commutator_le.mpr hcc
  have he : IsElementaryAbelian 2 (V0 VH V2 ⧸ (U0 UH V2).subgroupOf (V0 VH V2)) :=
    conjugateSpan_quotient_elementary 2 VH (G2 V2) (U0 UH V2)
  let := he
  refine ⟨hn,he,?_⟩
  apply BinaryConjugationSection.exists_descended_actor (G2 V2) (V0 VH V2) (U0 UH V2)
    hV0G hU0V0 (G2_normalizes_V0 VH V2) (G2_normalizes_U0 UH V2) π hπ
  intro a ha v hv
  have haQ : (a:G) ∈ Q2 V2 := by
    apply mem_map_of_mem (G2 V2).subtype
    change a ∈ π.ker at ha
    rwa [←hπker]
  exact hc0 (commutator_mem_commutator haQ hv)

/-- The original exterior marking gives a three-dimensional K₂-minimal seed in the second quotient. -/
theorem source_second_seed_geometry [Finite G]
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (H UH VH V2 : Subgroup G)
    (ξ : Representation (ZMod 2) H Six)
    (p : BinaryConjugationSection H VH UH ξ)
    (π₄ : H →* SL(4,ZMod 2))
    (hact : ∀ h x, ξ h x = exteriorMap (π₄ h).val x)
    (hfirst : p.imageSpace (U0 UH V2) = firstSpace)
    (hUV : U0 UH V2 ≤ VH)
    (hactors : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j →
      ∃ k : K2 H V2,
        (π₄ (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k)).val =
          Matrix.transvection i j 1)
    (τ : Representation (ZMod 2) (G2 V2) Y)
    (q : BinaryConjugationSection (G2 V2) (V0 VH V2) (U0 UH V2) τ) :
    Module.finrank (ZMod 2) (q.imageSpace VH) = 3 ∧
      ∀ B : Subgroup G, U0 UH V2 ≤ B → B ≤ VH → K2 H V2 ≤ normalizer B →
        B = U0 UH V2 ∨ B = VH := by
  let : Finite Y := Finite.of_surjective (fun v : V0 VH V2 => (q.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp q.onto)
  have h0 : UH.relIndex (U0 UH V2) = 8 := by
    rw [←p.imageSpace_card_eq_relIndex _ hUV,hfirst,
      Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,firstSpace_finrank]
    rfl
  have ht : UH.relIndex VH = 64 := by
    rw [p.relIndex_eq_card,Module.natCard_eq_pow_finrank (K:=ZMod 2),
      Nat.card_zmod,Module.finrank_fin_fun]
    rfl
  have hi : (U0 UH V2).relIndex VH = 8 := by
    have hh := relIndex_mul_relIndex UH (U0 UH V2) VH (UH_le_U0 UH V2) hUV
    rw [h0,ht] at hh
    omega
  constructor
  · have hh := q.imageSpace_card_eq_relIndex VH (VH_le_V0 VH V2)
    rw [hi,Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (by decide : 1 < 2)) hh
  · intro B hUB hBV hnB
    have hs := BinaryParabolicExteriorSquare.PointQuotient.invariant_above_first
      (p.imageSpace B) (hfirst ▸ p.imageSpace_mono hUB) (by
        intro i j hi hj hij x hx
        obtain ⟨k,hk⟩ := hactors i j hi hj hij
        have hh := p.imageSpace_apply_mem B
          (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k) (hnB k.property) x hx
        rwa [hact,hk] at hh)
    rcases hs with hs | hs
    · left
      apply le_antisymm ?_ hUB
      intro b hb
      apply (p.coordinates_mem_imageSpace_iff_of_kernel_le (U0 UH V2)
        (UH_le_U0 UH V2) ⟨b,hBV hb⟩).mp
      rw [hfirst,←hs]
      exact (p.mem_imageSpace_iff B _).mpr ⟨⟨b,hBV hb⟩,hb,rfl⟩
    · right
      exact le_antisymm hBV ((p.le_sup_kernel_of_image_top B hs).trans
        (sup_le le_rfl ((UH_le_U0 UH V2).trans hUB)))

/-- Construct the second quotient from the original factor data, with its generating seed and same-g disjoint translate. -/
theorem source_second_action_of_natural_exterior [Finite G]
    {D : Type*} [Group D]
    (H UH VH V1 V2 A : Subgroup G) [IsElementaryAbelian 2 VH]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π₄ : H →* SL(4,ZMod 2))
    (hnatural : ∀ h x, ρ h x = (π₄ h).val.mulVec x)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {Pi.single 0 1})
    (κ : ↥(H ⊓ G2 V2) →* K) (σ : Representation (ZMod 2) K W)
    (dU : BinaryConjugationSection (H ⊓ G2 V2) UH V2 (σ.comp κ))
    (hκ : κ.ker = pCore 2 ↥(H ⊓ G2 V2)) (hcore : Q2 V2 ≤ H)
    (ξ : Representation (ZMod 2) H Six)
    (p : BinaryConjugationSection H VH UH ξ)
    (hact : ∀ h x, ξ h x = exteriorMap (π₄ h).val x)
    (hfirst : p.imageSpace (U0 UH V2) = firstSpace)
    (hUV : U0 UH V2 ≤ VH)
    (hactors : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j →
      ∃ k : K2 H V2,
        (π₄ (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k)).val =
          Matrix.transvection i j 1)
    (g : G2 V2) (hint : VH ⊓ VH.conjBy ((g:G)⁻¹) = U0 UH V2)
    (hQA : H.pCoreIn 2 ≤ A) (hAG : A ≤ G2 V2)
    (hnA : G2 V2 ≤ normalizer A)
    (hAc : A.pCoreIn 2 = A ⊓ centralizer (V2:Set G))
    (π : G2 V2 →* D) (hπ : Function.Surjective π)
    (hπker : π.ker = pCore 2 (G2 V2)) :
    ∃ hn : ((U0 UH V2).subgroupOf (V0 VH V2)).Normal,
      let := hn
      ∃ he : IsElementaryAbelian 2 (V0 VH V2 ⧸ (U0 UH V2).subgroupOf (V0 VH V2)),
        let := he
        ∃ (τ : Representation (ZMod 2) D
          (Additive (V0 VH V2 ⧸ (U0 UH V2).subgroupOf (V0 VH V2))))
          (q : BinaryConjugationSection (G2 V2) (V0 VH V2) (U0 UH V2) (τ.comp π)),
          (∀ v : V0 VH V2, (q.coordinates v).toAdd =
            Additive.ofMul (QuotientGroup.mk' ((U0 UH V2).subgroupOf (V0 VH V2)) v)) ∧
          Module.finrank (ZMod 2) (q.imageSpace VH) = 3 ∧
          Disjoint (q.imageSpace VH) ((q.imageSpace VH).map (τ (π g⁻¹))) ∧
          (⨆ a : G2 V2, (q.imageSpace VH).map (τ (π a))) = ⊤ ∧
          ∀ B : Subgroup G, U0 UH V2 ≤ B → B ≤ VH → K2 H V2 ≤ normalizer B →
            B = U0 UH V2 ∨ B = VH := by
  have hVQ := source_VH_le_Q2_of_I2 H VH V2 A p.section_le p.normalized
    (dU.kernel_le.trans p.kernel_le) hQA hAG hnA hAc
  have hc := source_U0_core_commutator H UH V2 κ σ dU hκ hcore
  have hc' : ⁅Q2 V2,UH⁆ ≤ V2 :=
    (commutator_mono le_rfl (UH_le_U0 UH V2)).trans hc
  obtain ⟨hn,he,τ,q,hq⟩ := source_second_quotient_action UH VH V2 hUV hVQ
    (source_VH_core_commutator H UH VH V1 V2 ρ d π₄ hnatural hpoint ξ p hact hfirst hcore hc')
    π hπ hπker

  let := hn
  let := he
  obtain ⟨hd,hmin⟩ := source_second_seed_geometry H UH VH V2 ξ p π₄ hact hfirst
    hUV hactors (τ.comp π) q
  refine ⟨hn,he,τ,q,hq,hd,?_,?_,hmin⟩
  · have hUB : U0 UH V2 ≤ VH.conjBy ((g:G)⁻¹) := hint ▸ inf_le_right
    have hdis : Disjoint (q.imageSpace VH) (q.imageSpace (VH.conjBy ((g:G)⁻¹))) := by
      apply Submodule.disjoint_def.mpr
      intro w hw hwg
      obtain ⟨v,hv,rfl⟩ := (q.mem_imageSpace_iff VH w).mp hw
      have hvg := (q.coordinates_mem_imageSpace_iff_of_kernel_le _ hUB v).mp hwg
      exact (q.coordinates_eq_one_iff v).mpr (hint ▸ ⟨hv,hvg⟩)
    have hh := q.imageSpace_conjBy VH (VH_le_V0 VH V2) g⁻¹
    change q.imageSpace (VH.conjBy ((g:G)⁻¹)) =
      (q.imageSpace VH).map (τ (π g⁻¹)) at hh
    rwa [hh] at hdis
  · exact (q.imageSpace_conjugateSpan VH (VH_le_V0 VH V2)).symm.trans q.imageSpace_self


end CFSG.Quasithin.Chapter13.Section08.LinearFour

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open BinaryParabolicExteriorSquare SingularPresentation
open PlaneSpan (pointSpace firstSpace planeSpace)
open BinaryLinear.FlagCoordinates
open Theory.LinearAlgebra BinaryFivePointStabilizer
variable {G K U W : Type*} [Group G] [Finite G] [Group K]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  [AddCommGroup W] [Module (ZMod 2) W]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- Construct the second quotient from the original seed, constructing its
exterior marking first and retaining the supplied I₂, quotient maps and g. -/
theorem source_second_action_from_original_seed
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hab : IsMulCommutative (conjugateSpanBy V G₁))
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (hHeq : H = normalizer (V₁:Set G))
    (A L2 : Subgroup G)
    (hK : ((K2 H V₂).subgroupOf (G2 V₂)).Normal)
    (hG : G2 V₂ = K2 H V₂ ⊔ L2 ⊔ (T:Subgroup G))
    (hV : L2 ⊔ (T:Subgroup G) ≤ normalizer (V:Set G))
    (π : G2 V₂ →* K × Equiv.Perm (Fin 3)) (hπ : Function.Surjective π)
    (hπker : π.ker = pCore 2 (G2 V₂)) (hcore : Q2 V₂ ≤ H)
    (σ : Representation (ZMod 2) K U)
    (κ : ↥(H ⊓ G2 V₂) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V₂) (Source.UH H V₃) V₂ (σ.comp κ))
    (hκker : κ.ker = pCore 2 ↥(H ⊓ G2 V₂))
    (hκ : Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V₂))))
    (hπK : ∀ k : K2 H V₂,
      π (inclusion ((K2_le_localNormalizer H V₂).trans inf_le_right) k) =
        (κ (inclusion (K2_le_localNormalizer H V₂) k),1))
    (eI : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hAcore : A.pCoreIn 2 = A ⊓ centralizer (V₂:Set G))
    (hQA : H.pCoreIn 2 ≤ A) (hnA : G2 V₂ ≤ normalizer A)
    (hALT : A ≤ L ⊔ (T:Subgroup G)) (hVA : V ≤ A) (hAG : A ≤ G2 V₂)
    (hπI : ∀ a : A, π (inclusion hAG a) = (1,eI (QuotientGroup.mk' (pCore 2 A) a)))
    (hgen : Source.UH H V₃ = conjugateSpanBy V₃ (K2 H V₂))
    (hdim : Module.finrank (ZMod 2) U = 3)
    (g : A) (hg : (g:G) ∉ H)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π₄ : H →* SL(4,ZMod 2))
    (hker : π₄.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π₄)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π₄ h).val w)
    (hpoint : d.imageSpace V₂ = Submodule.span (ZMod 2) {Pi.single 0 1})
    (hplane : d.imageSpace V₃ = plane)
    (eU : QuotientSpace (Pi.single 0 1 : Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U)
    (hcoords : ∀ u : Source.UH H V₃, (dU.coordinates u).toAdd =
      eU ((line (Pi.single 0 1)).mkQ (d.coordinates u).toAdd))
    (hUcard : Nat.card (Source.UH H V₃) = 32)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T:Subgroup G) ≤ N → N = M)
    (hgenerate : L ⊔ (T:Subgroup G) ≤ H ⊔ zpowers (g:G)) :
    ∃ hn : ((U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂)).Normal,
      let := hn
      ∃ he : IsElementaryAbelian 2
          (V0 (Source.VH H V) V₂ ⧸ (U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂)),
        let := he
        ∃ (τ : Representation (ZMod 2) (K × Equiv.Perm (Fin 3))
          (Additive (V0 (Source.VH H V) V₂ ⧸
            (U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂))))
          (q : BinaryConjugationSection (G2 V₂) (V0 (Source.VH H V) V₂)
            (U0 (Source.UH H V₃) V₂) (τ.comp π)),
          (∀ v : V0 (Source.VH H V) V₂, (q.coordinates v).toAdd =
            Additive.ofMul (QuotientGroup.mk'
              ((U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂)) v)) ∧
          Module.finrank (ZMod 2) (q.imageSpace (Source.VH H V)) = 3 ∧
          Disjoint (q.imageSpace (Source.VH H V))
            ((q.imageSpace (Source.VH H V)).map (τ (π (inclusion hAG g)⁻¹))) ∧
          (⨆ a : G2 V₂, (q.imageSpace (Source.VH H V)).map (τ (π a))) = ⊤ ∧
          ∀ B : Subgroup G, U0 (Source.UH H V₃) V₂ ≤ B → B ≤ Source.VH H V →
            K2 H V₂ ≤ normalizer B → B = U0 (Source.UH H V₃) V₂ ∨ B = Source.VH H V := by
  let ds := s.toLocalSetup hab
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := ds.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.2.1)
  obtain ⟨p₆,_,hpU,_,_,hint⟩ := source_exterior_geometry_from_original_seed s hab h hH
    hcentral hHeq A L2 hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK
    eI hAcore hALT hVA hAG hπI hgen hdim g hg ρ d π₄ hker honto hnatural
    hpoint hplane eU hcoords hUcard hu hgenerate
  have hUV := source_U0_le_VH_of_normal_factors H (Source.UH H V₃) V₂ V₃ V L2 (T:Subgroup G)
    hK hG hV hgen s.seed_le
  have hactors := fun (i j : Fin 4) (_ : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) =>
    source_K2_point_actors H (Source.UH H V₃) V₁ V₂ ρ d π₄ honto hnatural
      s.line_le_plane dU.kernel_le hpoint i j hj hij
  exact source_second_action_of_natural_exterior H (Source.UH H V₃) (Source.VH H V) V₁ V₂ A
    ρ d π₄ hnatural hpoint κ σ dU hκker hcore (action π₄) p₆ (fun _ _ => rfl)
    hpU hUV hactors (inclusion hAG g) hint hQA hAG hnA hAcore π hπ hπker

end CFSG.Quasithin.Chapter13.Section08.LinearFour
