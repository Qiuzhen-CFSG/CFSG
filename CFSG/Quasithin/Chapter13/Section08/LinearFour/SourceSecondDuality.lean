module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSecondAction
public import Theory.Representation.BinaryConjugationSection.LagrangianDuality
public import Theory.Representation.BinaryParabolicExteriorSquare.PointDuality
public import Theory.Representation.BinaryConjugationSection.CoordinateEmbedding

/-!
# The actual dual-natural seed of the second tensor

The exterior Pfaffian pairs U₀/U_H perfectly with V_H/U₀. Restriction of
its coordinates constructs both literal sections for N_H(V₂), with the
inverse-dual action and an explicit pairing equation. Inclusion in the
constructed V₀/U₀ then gives an injective equivariant seed map.

The original first tensor identifies U₀/U_H with the supplied natural K₂
module: its row selected by the same g has zero kernel by
U_H intersect U_H^g = V₂, and dimensions make it onto. Dualizing this
identification gives an actual intertwiner from the dual of that supplied
module into V₀/U₀, whose image is precisely V_H/U₀. Both original quotient
factor maps are unchanged.

The final application constructs the exterior marking, second quotient and
first tensor from the original seed inputs. It retains canonical second
quotient coordinates, the same-g disjoint seed translate and orbit generation.
No dual-natural embedding is an input. Recognizing the two full second-tensor
rows, extra-line movement, chief-factor accounting and the original
13.8.28--32 contradiction remain with this owner. Earlier source inputs and
final 13.8.1 assembly retain their existing owners.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29(4), printed p.964, combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
open Atlas.Order20160A8.Bivectors (exteriorMap)
open Representation.BinaryParabolicExteriorSquare.PlaneSpan
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G : Type*} [Group G]

/-- The actual point-normalizer sections U₀/U_H and V_H/U₀ are paired duals.
The coordinates are restrictions of the supplied exterior marking. -/
theorem source_second_dual_sections
    (H UH VH V2 : Subgroup G)
    (ξ : Representation (ZMod 2) H Six)
    (p : BinaryConjugationSection H VH UH ξ)
    (π₄ : H →* SL(4,ZMod 2))
    (hact : ∀ h x, ξ h x = exteriorMap (π₄ h).val x)
    (hfirst : p.imageSpace (U0 UH V2) = firstSpace)
    (hUV : U0 UH V2 ≤ VH) (hVG : VH ≤ G2 V2) :
    ∃ (σ : Representation (ZMod 2) ↥(H ⊓ G2 V2) (p.imageSpace (U0 UH V2)))
      (s : BinaryConjugationSection (H ⊓ G2 V2) (U0 UH V2) UH σ)
      (t : BinaryConjugationSection (H ⊓ G2 V2) VH (U0 UH V2) σ.dual),
      (∀ u : U0 UH V2, ((s.coordinates u).toAdd : Six) =
        (p.coordinates (inclusion hUV u)).toAdd) ∧
      ∀ v : VH, ∀ u : U0 UH V2,
        (t.coordinates v).toAdd (s.coordinates u).toAdd =
          BinaryParabolicExteriorSquare.PointDuality.form (p.coordinates v).toAdd
            (p.coordinates (inclusion hUV u)).toAdd := by
  let r := p.restrictActor (show H ⊓ G2 V2 ≤ H from inf_le_left)
    (le_inf p.section_le hVG)
  apply r.exists_lagrangian_dual_sections (U0 UH V2) (UH_le_U0 UH V2) hUV
    (inf_le_right.trans (G2_normalizes_U0 UH V2))
    BinaryParabolicExteriorSquare.PointDuality.form
    BinaryParabolicExteriorSquare.PointDuality.form_alt
    BinaryParabolicExteriorSquare.PointDuality.form_nondegenerate
  · intro a x y
    change BinaryParabolicExteriorSquare.PointDuality.form
      (ξ (inclusion (show H ⊓ G2 V2 ≤ H from inf_le_left) a) x)
      (ξ (inclusion (show H ⊓ G2 V2 ≤ H from inf_le_left) a) y) = _
    rw [hact,hact]
    exact BinaryParabolicExteriorSquare.PointDuality.form_invariant _ (π₄ _).property x y
  · change BinaryParabolicExteriorSquare.PointDuality.form.orthogonal
      (p.imageSpace (U0 UH V2)) = p.imageSpace (U0 UH V2)
    rw [hfirst]
    exact BinaryParabolicExteriorSquare.PointDuality.firstSpace_orthogonal

/-- The dual seed embeds into the literal second quotient, retaining both
coordinate maps and the action of every original point-normalizer element. -/
theorem source_second_dual_seed_embedding
    {D Y : Type*} [Group D] [AddCommGroup Y] [Module (ZMod 2) Y]
    (H UH VH V2 : Subgroup G)
    (ξ : Representation (ZMod 2) H Six)
    (p : BinaryConjugationSection H VH UH ξ)
    (π₄ : H →* SL(4,ZMod 2))
    (hact : ∀ h x, ξ h x = exteriorMap (π₄ h).val x)
    (hfirst : p.imageSpace (U0 UH V2) = firstSpace)
    (hUV : U0 UH V2 ≤ VH) (hVG : VH ≤ G2 V2)
    (π : G2 V2 →* D) (τ : Representation (ZMod 2) D Y)
    (q : BinaryConjugationSection (G2 V2) (V0 VH V2) (U0 UH V2) (τ.comp π)) :
    ∃ (σ : Representation (ZMod 2) ↥(H ⊓ G2 V2) (p.imageSpace (U0 UH V2)))
      (s : BinaryConjugationSection (H ⊓ G2 V2) (U0 UH V2) UH σ)
      (t : BinaryConjugationSection (H ⊓ G2 V2) VH (U0 UH V2) σ.dual)
      (f : Module.Dual (ZMod 2) (p.imageSpace (U0 UH V2)) →ₗ[ZMod 2] Y),
      Function.Injective f ∧ f.range = q.imageSpace VH ∧
      (∀ v : VH, f (t.coordinates v).toAdd =
        (q.coordinates (inclusion (VH_le_V0 VH V2) v)).toAdd) ∧
      (∀ a w, f (σ.dual a w) =
        τ (π (inclusion (show H ⊓ G2 V2 ≤ G2 V2 from inf_le_right) a)) (f w)) ∧
      (∀ u : U0 UH V2, ((s.coordinates u).toAdd : Six) =
        (p.coordinates (inclusion hUV u)).toAdd) ∧
      ∀ v : VH, ∀ u : U0 UH V2,
        (t.coordinates v).toAdd (s.coordinates u).toAdd =
          BinaryParabolicExteriorSquare.PointDuality.form (p.coordinates v).toAdd
            (p.coordinates (inclusion hUV u)).toAdd := by
  obtain ⟨σ,s,t,hs,ht⟩ := source_second_dual_sections H UH VH V2 ξ p π₄ hact hfirst hUV hVG
  obtain ⟨f,hf,hc,ha,hr⟩ := q.exists_coordinate_embedding t inf_le_right (VH_le_V0 VH V2)
  exact ⟨σ,s,t,f,hf,hr,hc,fun a w => (ha a w).symm,hs,ht⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open CyclicSeedTensor QuadraticFourGroup.TensorClassification
open scoped TensorProduct
variable {G K I U : Type*} [Group G] [Group K] [Group I]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]

/-- The same-g first-tensor row identifies the actual exterior three-space
with the original natural K₂ module, preserving its supplied factor map. -/
theorem source_first_exterior_row_equiv
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
    (ξ : Representation (ZMod 2) H Six)
    (p : BinaryConjugationSection H (Source.VH H V) UH ξ)
    (hUV : U0 UH V2 ≤ Source.VH H V)
    (hfirst : p.imageSpace (U0 UH V2) = firstSpace)
    (hdim : Module.finrank (ZMod 2) U = 3)
    (g : G2 V2) (hg : (π g⁻¹).1 = 1)
    (hint : UH ⊓ UH.conjBy ((g:G)⁻¹) = V2) :
    ∃ e : U ≃ₗ[ZMod 2] p.imageSpace (U0 UH V2),
      (∀ k : K2 H V2, ∀ u,
        (e (σ (κ (inclusion (K2_le_localNormalizer H V2) k)) u) : Six) =
          ξ (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k) (e u)) ∧
      ∀ u : UH, (e (dU.coordinates u).toAdd : Six) =
        (p.coordinates ⟨(g:G)⁻¹ * u * (g:G),
          hUV (by simpa using ((mem_normalizer_iff.mp (dt.normalized g⁻¹.property) u).mp
            (UH_le_U0 UH V2 u.property)))⟩).toAdd := by
  obtain ⟨f,ha,hc⟩ := source_tensor_conjugate_row H UH V2 V π σ μ dt κ dU hU hπK ξ p hUV g hg
  have hi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro u hu
    obtain ⟨v,hv⟩ := dU.onto (Multiplicative.ofAdd u)
    have hz : f (dU.coordinates v).toAdd = 0 := by rw [hv]; exact hu
    rw [hc] at hz
    have hcv := (p.coordinates_eq_one_iff _).mp hz
    have hcg : (g:G)⁻¹ * v * (g:G) ∈ UH.conjBy ((g:G)⁻¹) :=
      ⟨v,v.property,by simp⟩
    have hc2 : (g:G)⁻¹ * v * (g:G) ∈ V2 := hint.le ⟨hcv,hcg⟩
    have hv2 : (v:G) ∈ V2 :=
      (mem_normalizer_iff.mp (show (g:G)⁻¹ ∈ normalizer (V2:Set G) from g⁻¹.property) v).mpr
        (by simpa using hc2)
    have hzero := (dU.coordinates_eq_one_iff v).mpr hv2
    exact congrArg Multiplicative.toAdd (hv.symm.trans hzero)
  have hf (u : U) : f u ∈ p.imageSpace (U0 UH V2) := by
    obtain ⟨v,hv⟩ := dU.onto (Multiplicative.ofAdd u)
    rw [←show (dU.coordinates v).toAdd = u from congrArg Multiplicative.toAdd hv,hc]
    exact (p.mem_imageSpace_iff _ _).mpr ⟨_,
      by simpa using ((mem_normalizer_iff.mp (dt.normalized g⁻¹.property) v).mp
        (UH_le_U0 UH V2 v.property)),rfl⟩
  let f' := f.codRestrict (p.imageSpace (U0 UH V2)) hf
  have hi' : Function.Injective f' := fun u v h => hi (congrArg Subtype.val h)
  have hd : Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) (p.imageSpace (U0 UH V2)) := by
    rw [hdim,hfirst,firstSpace_finrank]
  let e : U ≃ₗ[ZMod 2] p.imageSpace (U0 UH V2) :=
    LinearEquiv.ofBijective f' ⟨hi', (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi'⟩
  exact ⟨e,ha,hc⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open CyclicSeedTensor QuadraticFourGroup.TensorClassification
open scoped TensorProduct
variable {G K I U Y : Type*} [Group G] [Group K] [Group I]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- The original first tensor and exterior marking construct the dual-natural
K₂ embedding in the second quotient, with the original K₂ quotient map. -/
theorem source_second_dual_natural_embedding
    (H UH V2 V : Subgroup G)
    (π : G2 V2 →* K × I) (σ : Representation (ZMod 2) K U)
    (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
    (dt : BinaryConjugationSection (G2 V2) (U0 UH V2) V2 ((externalTensor σ μ).comp π))
    (κ : ↥(H ⊓ G2 V2) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V2) UH V2 (σ.comp κ))
    (hκ : Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V2))))
    (hU : ∀ u : UH, (dt.coordinates (inclusion (UH_le_U0 UH V2) u)).toAdd =
      (dU.coordinates u).toAdd ⊗ₜ[ZMod 2] first)
    (hπK : ∀ k : K2 H V2,
      π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k) =
        (κ (inclusion (K2_le_localNormalizer H V2) k),1))
    (ξ : Representation (ZMod 2) H Six)
    (p : BinaryConjugationSection H (Source.VH H V) UH ξ)
    (π₄ : H →* SL(4,ZMod 2))
    (hact : ∀ h x, ξ h x = exteriorMap (π₄ h).val x)
    (hUV : U0 UH V2 ≤ Source.VH H V)
    (hfirst : p.imageSpace (U0 UH V2) = firstSpace)
    (hdim : Module.finrank (ZMod 2) U = 3)
    (g : G2 V2) (hg : (π g⁻¹).1 = 1)
    (hint : UH ⊓ UH.conjBy ((g:G)⁻¹) = V2)
    (τ : Representation (ZMod 2) (K × I) Y)
    (q : BinaryConjugationSection (G2 V2) (V0 (Source.VH H V) V2) (U0 UH V2) (τ.comp π)) :
    ∃ f : σ.dual.IntertwiningMap (τ.comp (MonoidHom.inl K I)),
      Function.Injective f ∧ f.range.toSubmodule = q.imageSpace (Source.VH H V) := by
  obtain ⟨e,he,_⟩ := source_first_exterior_row_equiv H UH V2 V π σ μ dt κ dU hU hπK
    ξ p hUV hfirst hdim g hg hint
  obtain ⟨ψ,s,t,z,hz,hr,hc,ha,hs,_⟩ := source_second_dual_seed_embedding H UH (Source.VH H V) V2
    ξ p π₄ hact hfirst hUV ((VH_le_V0 _ _).trans q.section_le) π τ q
  have hψ (a : ↥(H ⊓ G2 V2)) (w : p.imageSpace (U0 UH V2)) :
      (ψ a w : Six) = ξ (inclusion (show H ⊓ G2 V2 ≤ H from inf_le_left) a) w := by
    obtain ⟨u,hu⟩ := s.onto (Multiplicative.ofAdd w)
    have hwu : (s.coordinates u).toAdd = w := congrArg Multiplicative.toAdd hu
    rw [←hwu,←s.equivariant,hs,hs]
    exact p.equivariant (inclusion (show H ⊓ G2 V2 ≤ H from inf_le_left) a) (inclusion hUV u)
  have he' (k : K2 H V2) (u : U) :
      e (σ (κ (inclusion (K2_le_localNormalizer H V2) k)) u) =
        ψ (inclusion (K2_le_localNormalizer H V2) k) (e u) := by
    apply Subtype.ext
    rw [hψ]
    exact he k u
  let E : Module.Dual (ZMod 2) U ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (p.imageSpace (U0 UH V2)) :=
    e.symm.dualMap
  have hE (k : K2 H V2) (w : Module.Dual (ZMod 2) U) :
      E (σ.dual (κ (inclusion (K2_le_localNormalizer H V2) k)) w) =
        ψ.dual (inclusion (K2_le_localNormalizer H V2) k) (E w) := by
    ext v
    obtain ⟨u,rfl⟩ := e.surjective v
    change w (σ (κ (inclusion (K2_le_localNormalizer H V2) k))⁻¹ (e.symm (e u))) =
      w (e.symm (ψ (inclusion (K2_le_localNormalizer H V2) k)⁻¹ (e u)))
    rw [e.symm_apply_apply]
    have hh := he' k⁻¹ u
    simp only [map_inv] at hh
    rw [←hh,e.symm_apply_apply]
  let F := z.comp E.toLinearMap
  have hF (k : K) (w : Module.Dual (ZMod 2) U) :
      F (σ.dual k w) = τ (k,1) (F w) := by
    obtain ⟨a,rfl⟩ := hκ k
    change z (E (σ.dual (κ (inclusion (K2_le_localNormalizer H V2) a)) w)) = _
    rw [hE,ha]
    change τ (π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) a)) (z (E w)) = _
    rw [hπK]
    rfl
  let f : σ.dual.IntertwiningMap (τ.comp (MonoidHom.inl K I)) :=
    .mk F (fun k => LinearMap.ext (hF k))
  refine ⟨f,hz.comp E.injective,?_⟩
  change LinearMap.range F = _
  rw [LinearMap.range_comp,LinearMap.range_eq_top.mpr E.surjective,Submodule.map_top]
  exact hr
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

/-- Construct the dual-natural seed in the literal second quotient from the
original inputs, retaining both factor maps, its orbit and the same g. -/
theorem source_second_dual_seed_from_original_seed
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
          (∃ f : σ.dual.IntertwiningMap (τ.comp (MonoidHom.inl K (Equiv.Perm (Fin 3)))),
            Function.Injective f ∧ f.range.toSubmodule = q.imageSpace (Source.VH H V)) ∧
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
  obtain ⟨hn,he,τ,q,hq,hd,hdis,hspan,hmin⟩ := source_second_action_of_natural_exterior H (Source.UH H V₃) (Source.VH H V) V₁ V₂ A
    ρ d π₄ hnatural hpoint κ σ dU hκker hcore (action π₄) p₆ (fun _ _ => rfl)
    hpU hUV hactors (inclusion hAG g) hint hQA hAG hnA hAcore π hπ hπker

  let := hn
  let := he
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le (le_conjugateSpanBy V G₁)
  obtain ⟨e,_,_,_,dt,_,hU,_,_,hint₁,_⟩ := source_tensor_from_original_seed ds
    H (Source.UH H V₃) A L2 hHeq hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK
    eI hAcore hALT hVA hAG hπI (le_conjugateSpanBy _ _) hgen hdim g hg
  obtain ⟨f,hf,hr⟩ := source_second_dual_natural_embedding
    H (Source.UH H V₃) V₂ V π σ
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp e.toMonoidHom)
    dt κ dU hκ hU hπK (action π₄) p₆ π₄ (fun _ _ => rfl) hUV hpU hdim
    (inclusion hAG g) (congrArg Prod.fst (hπI g⁻¹)) hint₁ τ q
  exact ⟨hn,he,τ,q,hq,⟨f,hf,hr⟩,hd,hdis,hspan,hmin⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour
