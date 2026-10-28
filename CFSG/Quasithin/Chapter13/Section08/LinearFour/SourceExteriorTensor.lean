module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceExteriorPresentation
public import Theory.Representation.BinaryConjugationSection.NestedCoordinates

/-!
# The compatible exterior marking from the original first tensor

The first tensor gives a K₂-equivariant map from the natural U_H/V₂ row
into V_H/U_H by conjugating with the supplied g⁻¹. Choose a representative
of the marked vector e₁ in V₃. The already proved intersection
U_H ∩ U_H^g = V₂ makes its image nonzero. Two actual K₂ transvections
transport the natural identity e₁ + a(e₁) = b(e₁) to the required local
singular-line relation.
The index |V:V₃|=2 makes this nonzero vector generate the original V-image.

The source application constructs the unmarked action on the literal
V_H/U_H quotient, applies the first-tensor construction, then uses this
line relation to recognize the exterior module for the same natural
four-space quotient map. It feeds the original L₁ span and same-conjugator
intersection consumers, obtaining their marked images, index 64 and
V_H ∩ V_H^g = U₀. All elementary-abelian instances follow from the original
13.8.2 span assumption; no exterior representation is an input.

The second tensor, extra-line movement, chief obstruction and final
13.8.28 contradiction remain with this owner. Earlier 13.8.27 retains
qt-d-138-six-g2-source, and final 13.8.1 assembly retains qt-d-1381-source.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
B.4.13 and 13.8.29(3),(5)--30, printed pp.97--98,964.
-/

public noncomputable section
open Subgroup Representation
open scoped TensorProduct MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open CyclicSeedTensor QuadraticFourGroup.TensorClassification
variable {G K I U W : Type*} [Group G] [Group K] [Group I]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]

/-- The row selected by the original g descends into V_H/U_H, equivariantly
for the original K₂ factor and retaining the literal conjugation coordinates. -/
theorem source_tensor_conjugate_row
    (H UH V2 V : Subgroup G)
    (π : G2 V2 →* K × I) (σ : Representation (ZMod 2) K U)
    (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
    (dt : BinaryConjugationSection (G2 V2) (U0 UH V2) V2 ((externalTensor σ μ).comp π))
    (κ : ↥(H ⊓ G2 V2) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V2) UH V2 (σ.comp κ))
    (hU : ∀ u : UH, (dt.coordinates (inclusion (UH_le_U0 UH V2) u)).toAdd =
      (dU.coordinates u).toAdd ⊗ₜ[ZMod 2] first)
    (hπK : ∀ k : K2 H V2,
      π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k) =
        (κ (inclusion (K2_le_localNormalizer H V2) k),1))
    (ξ : Representation (ZMod 2) H W)
    (p : BinaryConjugationSection H (Source.VH H V) UH ξ)
    (hUV : U0 UH V2 ≤ Source.VH H V)
    (g : G2 V2) (hg : (π g⁻¹).1 = 1) :
    ∃ f : U →ₗ[ZMod 2] W,
      (∀ k : K2 H V2, ∀ u,
        f (σ (κ (inclusion (K2_le_localNormalizer H V2) k)) u) =
          ξ (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k) (f u)) ∧
      ∀ u : UH, f (dU.coordinates u).toAdd =
        (p.coordinates ⟨(g:G)⁻¹ * u * (g:G),
          hUV (by simpa using ((mem_normalizer_iff.mp (dt.normalized g⁻¹.property) u).mp
            (UH_le_U0 UH V2 u.property)))⟩).toAdd := by
  obtain ⟨F,hF,hact⟩ := dt.exists_nested_coordinate_map p hUV dU.kernel_le
  let y := μ (π g⁻¹).2 first
  let f : U →ₗ[ZMod 2] W := F.comp ((TensorProduct.mk (ZMod 2) U (Fin 2 → ZMod 2)).flip y)
  have hf (u : U) : f u = F (u ⊗ₜ[ZMod 2] y) := rfl
  refine ⟨f,?_,?_⟩
  · intro k u
    have hh := hact (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k)
      (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k) rfl
      (u ⊗ₜ[ZMod 2] y)
    simpa only [MonoidHom.comp_apply,hπK,externalTensor_apply,TensorProduct.map_tmul,map_one,
      Module.End.one_apply,←hf] using hh
  · intro u
    have hh := dt.equivariant g⁻¹ (inclusion (UH_le_U0 UH V2) u)
    rw [hU] at hh
    change (dt.coordinates _).toAdd =
      externalTensor σ μ (π g⁻¹) ((dU.coordinates u).toAdd ⊗ₜ[ZMod 2] first) at hh
    rw [externalTensor_apply,TensorProduct.map_tmul,hg,map_one,Module.End.one_apply] at hh
    rw [hf,←hh,hF]
    congr 2
    exact Subtype.ext (by simp)
end CFSG.Quasithin.Chapter13.Section08.LinearFour

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open CyclicSeedTensor QuadraticFourGroup.TensorClassification
open BinaryLinear.FlagCoordinates
open Theory.LinearAlgebra BinaryFivePointStabilizer
open Atlas.Order20160A8.Bivectors (exteriorMap)
open BinaryParabolicExteriorSquare (Six)
variable {G K I U W : Type*} [Group G] [Finite G] [Group K] [Group I]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]

/-- The compatible first tensor supplies the nonzero seed and local exterior
line relation. Both actors are lifted from the original K₂; g is unchanged. -/
theorem source_exterior_line_from_tensor
    (H UH V1 V2 V3 V : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π₄ : H →* SL(4,ZMod 2)) (hπ₄ : Function.Surjective π₄)
    (hnatural : ∀ h x, ρ h x = (π₄ h).val.mulVec x)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ UH)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {Pi.single 0 1})
    (hplane : d.imageSpace V3 = plane)
    (h3U : V3 ≤ UH) (h3V : V3 ≤ V) (hindex : V3.relIndex V = 2)
    (π : G2 V2 →* K × I) (σ : Representation (ZMod 2) K U)
    (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
    (dt : BinaryConjugationSection (G2 V2) (U0 UH V2) V2 ((externalTensor σ μ).comp π))
    (κ : ↥(H ⊓ G2 V2) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V2) UH V2 (σ.comp κ))
    (eU : QuotientSpace (Pi.single 0 1 : Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U)
    (hcoords : ∀ u : UH, (dU.coordinates u).toAdd =
      eU ((line (Pi.single 0 1)).mkQ (d.coordinates u).toAdd))
    (hU : ∀ u : UH, (dt.coordinates (inclusion (UH_le_U0 UH V2) u)).toAdd =
      (dU.coordinates u).toAdd ⊗ₜ[ZMod 2] first)
    (hπK : ∀ k : K2 H V2,
      π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k) =
        (κ (inclusion (K2_le_localNormalizer H V2) k),1))
    (ξ : Representation (ZMod 2) H W)
    (p : BinaryConjugationSection H (Source.VH H V) UH ξ)
    (hUV : U0 UH V2 ≤ Source.VH H V)
    (g : G2 V2) (hg : (π g⁻¹).1 = 1)
    (hgV : (g:G) ∈ normalizer (V:Set G))
    (hint : UH ⊓ UH.conjBy ((g:G)⁻¹) = V2) :
    ∃ (v : W) (a b : H), v ≠ 0 ∧
      p.imageSpace V = Submodule.span (ZMod 2) {v} ∧
      exteriorMap (π₄ a).val (Pi.single 0 1) = (Pi.single 1 1 : Six) ∧
      exteriorMap (π₄ b).val (Pi.single 0 1) = (Pi.single 0 1 + Pi.single 1 1 : Six) ∧
      v + ξ a v = ξ b v := by
  obtain ⟨f,hf,hfc⟩ := source_tensor_conjugate_row H UH V2 V π σ μ dt κ dU hU hπK ξ p hUV g hg
  obtain ⟨z,hz,hzc⟩ := (d.mem_imageSpace_iff V3 (Pi.single 1 1)).mp
    (hplane.symm ▸ (by simp [plane] : (Pi.single 1 1 : Fin 4 → ZMod 2) ∈ plane))
  let zg : Source.VH H V := ⟨(g:G)⁻¹*z*(g:G),
    hUV (by simpa using ((mem_normalizer_iff.mp (dt.normalized g⁻¹.property) z).mp
      (UH_le_U0 UH V2 z.property)))⟩
  let v := f (dU.coordinates z).toAdd
  have hvcoord : v = (p.coordinates zg).toAdd := hfc z
  have hzV : (zg:G) ∈ V :=
    by simpa [zg] using (mem_normalizer_iff.mp ((normalizer (V:Set G)).inv_mem hgV) z).mp (h3V hz)
  have hvI : v ∈ p.imageSpace V := (p.mem_imageSpace_iff V v).mpr ⟨zg,hzV,hvcoord.symm⟩
  have hv0 : v ≠ 0 := by
    intro hv0
    have hzgU : (zg:G) ∈ UH := (p.coordinates_eq_one_iff zg).mp (hvcoord.symm.trans hv0)
    have hzg2 : (zg:G) ∈ V2 := hint ▸ ⟨hzgU,⟨z,z.property,by simp [zg]⟩⟩
    have hz2 : (z:G) ∈ V2 := by
      have hh := (mem_normalizer_iff.mp g.property (zg:G)).mp hzg2
      simpa [zg,mul_assoc] using hh
    have hcoord2 : (d.coordinates z).toAdd ∈ d.imageSpace V2 :=
      (d.mem_imageSpace_iff V2 _).mpr ⟨z,hz2,rfl⟩
    rw [hzc,hpoint] at hcoord2
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hcoord2
    have hh := congrFun hc 1
    simp at hh
  let : Finite W := Finite.of_surjective (fun x : Source.VH H V => (p.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp p.onto)
  have hdim : Module.finrank (ZMod 2) (p.imageSpace V) = 1 := by
    have hc := p.imageSpace_card_le_relative_index V V3 h3U
    rw [hindex,Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod] at hc
    have hb : Module.finrank (ZMod 2) (p.imageSpace V) ≤ 1 :=
      (pow_le_pow_iff_right₀ (by decide : (1:ℕ) < 2)).mp hc
    have hn : Module.finrank (ZMod 2) (p.imageSpace V) ≠ 0 := by
      intro he
      have hz := Submodule.finrank_eq_zero.mp he
      rw [hz] at hvI
      exact hv0 hvI
    omega
  have hseed := eq_span_singleton_of_mem_of_finrank_eq_one hdim hvI hv0
  obtain ⟨r,hr⟩ := source_K2_point_actors H UH V1 V2 ρ d π₄ hπ₄ hnatural h12 h2U hpoint 1 2 (by decide) (by decide)
  obtain ⟨s,hs⟩ := source_K2_point_actors H UH V1 V2 ρ d π₄ hπ₄ hnatural h12 h2U hpoint 2 1 (by decide) (by decide)
  let a := inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) (r*s)
  let b := inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) s
  have ha : (π₄ a).val = Matrix.transvection 1 2 1 * Matrix.transvection 2 1 1 := by
    simp only [a,map_mul,Matrix.SpecialLinearGroup.coe_mul,hr,hs]
  have hb : (π₄ b).val = Matrix.transvection 2 1 1 := hs
  have hrow (k : K2 H V2) :
      σ (κ (inclusion (K2_le_localNormalizer H V2) k)) (dU.coordinates z).toAdd =
        eU ((line (Pi.single 0 1)).mkQ
          ((π₄ (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k)).val.mulVec
            (Pi.single 1 1))) := by
    have hh := dU.equivariant (inclusion (K2_le_localNormalizer H V2) k) z
    change (dU.coordinates _).toAdd = σ (κ (inclusion (K2_le_localNormalizer H V2) k))
      (dU.coordinates z).toAdd at hh
    rw [←hh,hcoords]
    have hd := d.equivariant
      (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k) z
    rw [hnatural,hzc] at hd
    exact congrArg (fun x => eU ((line (Pi.single 0 1)).mkQ x)) hd
  refine ⟨v,a,b,hv0,hseed,?_,?_,?_⟩
  · rw [ha]
    decide +kernel
  · rw [hb]
    decide +kernel
  · change f (dU.coordinates z).toAdd + ξ a (f (dU.coordinates z).toAdd) =
      ξ b (f (dU.coordinates z).toAdd)
    rw [←hf,←hf,hrow,hrow,hcoords,hzc]
    change f (eU ((line _).mkQ (Pi.single 1 1))) +
      f (eU ((line _).mkQ ((π₄ a).val.mulVec (Pi.single 1 1)))) =
      f (eU ((line _).mkQ ((π₄ b).val.mulVec (Pi.single 1 1))))
    rw [←map_add,←map_add,←map_add,ha,hb]
    congr 3
    decide +kernel
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

/-- Construct the exterior marking, its actual marked images, the index-64
span and the same-g intersection from the original first-tensor inputs.
No exterior action or local line relation is assumed. -/
theorem source_exterior_geometry_from_original_seed
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
    ∃ p₆ : BinaryConjugationSection H (Source.VH H V) (Source.UH H V₃) (action π₄),
      p₆.imageSpace V = pointSpace ∧
      p₆.imageSpace (U0 (Source.UH H V₃) V₂) = firstSpace ∧
      p₆.imageSpace (conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)) = planeSpace ∧
      V.relIndex (conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)) = 64 ∧
      Source.VH H V ⊓ (Source.VH H V).conjBy ((g:G)⁻¹) = U0 (Source.UH H V₃) V₂ := by
  let ds := s.toLocalSetup hab
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := ds.span_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le (le_conjugateSpanBy V G₁)
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.2.1)
  obtain ⟨e,_,hVS,_,dt,_,hU,_,hprod,hint,hindex⟩ := source_tensor_from_original_seed ds
    H (Source.UH H V₃) A L2 hHeq hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK
    eI hAcore hALT hVA hAG hπI (le_conjugateSpanBy _ _) hgen hdim g hg
  have hUV := source_U0_le_VH_of_normal_factors H (Source.UH H V₃) V₂ V₃ V L2 (T:Subgroup G)
    hK hG hV hgen s.seed_le
  have hVH : V ≤ H := by
    rw [hHeq]
    exact ((commutator_eq_bot_iff_le_centralizer.mp
      (commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative V))).trans
      (centralizer_le (s.line_le_plane.trans (s.plane_le_seed.trans s.seed_le)))).trans
      (Subgroup.centralizer_le_normalizer _)
  let : ((Source.UH H V₃).subgroupOf (Source.VH H V)).Normal := normal_of_isMulCommutative _
  obtain ⟨ξ,p,_⟩ := BinaryConjugationSection.exists_descended_actor
    H (Source.VH H V) (Source.UH H V₃) (conjugateSpanBy_le_self hVH)
    (conjugateSpanBy_mono s.seed_le le_rfl) (le_normalizer_conjugateSpanBy _ _) d.normalized
    (MonoidHom.id H) Function.surjective_id (by
      intro a ha z hz
      change a = 1 at ha
      subst a
      simp)
  have hVcard : Nat.card V = 16 := by
    rw [Nat.card_congr s.coordinate.toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    rfl
  have hi : V₃.relIndex V = 2 := by
    have hh := relIndex_mul_card_of_le s.seed_le
    rw [s.seed_card,hVcard] at hh
    omega
  obtain ⟨v,a,b,hv0,hseed,ha,hb,hline⟩ := source_exterior_line_from_tensor
    H (Source.UH H V₃) V₁ V₂ V₃ V ρ d π₄ honto hnatural s.line_le_plane dU.kernel_le
    hpoint hplane (le_conjugateSpanBy _ _) s.seed_le hi π σ
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp e.toMonoidHom)
    dt κ dU eU hcoords hU hπK ξ p hUV (inclusion hAG g)
    (congrArg Prod.fst (hπI g⁻¹)) (s.normalizes_V (hALT g.property)) hint
  have hproper : ¬ V ≤ Source.UH H V₃ := by
    intro hle
    have hv : v ∈ p.imageSpace V := hseed.symm ▸ Submodule.subset_span (Set.mem_singleton v)
    obtain ⟨z,hz,hzv⟩ := (p.mem_imageSpace_iff V v).mp hv
    exact hv0 (hzv.symm.trans ((p.coordinates_eq_one_iff z).mpr (hle hz)))
  obtain ⟨p₆,hpV,hpU,hpS,hi64⟩ := source_cubic_span_of_one_line s h hH hcentral
    ρ d π₄ hker honto hnatural hpoint hplane ξ p v hseed hproper a b ha hb hline
    hUV hVS hindex hUcard
  refine ⟨p₆,hpV,hpU,hpS,hi64,?_⟩
  have hk : π.ker ≤ H.subgroupOf (G2 V₂) := by
    rw [hπker]
    intro x hx
    exact hcore (mem_map_of_mem (G2 V₂).subtype hx)
  have hseedg : V₃.conjBy ((g:G)⁻¹) ≤ V := by
    rintro x ⟨z,hz,rfl⟩
    exact (mem_normalizer_iff.mp (s.normalizes_V (hALT g⁻¹.property)) z).mp (s.seed_le hz)
  have hactors := fun (i j : Fin 4) (_ : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) =>
    source_K2_point_actors H (Source.UH H V₃) V₁ V₂ ρ d π₄ honto hnatural
      s.line_le_plane dU.kernel_le hpoint i j hj hij
  have hne : Source.VH H V ≠ ⊥ := by
    intro he
    have hz : Source.VH H V ≤ Source.UH H V₃ := by rw [he]; exact bot_le
    exact hproper ((le_conjugateSpanBy V H).trans hz)
  exact source_tensor_intersection_of_product L (T:Subgroup G) H M (Source.UH H V₃) V₂ V₃ V π hk
    (fun k => congrArg Prod.snd (hπK k)) (inclusion hAG g)
    (congrArg Prod.fst (hπI g)) hgen s.seed_le hseedg hprod (action π₄) p₆ π₄
    (fun _ _ => rfl) hpU hactors (IsElementaryAbelian.isPGroup 2 _) hne hu hH.2.2 hgenerate
end CFSG.Quasithin.Chapter13.Section08.LinearFour
