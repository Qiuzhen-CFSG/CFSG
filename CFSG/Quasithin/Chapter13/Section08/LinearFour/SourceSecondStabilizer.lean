module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSecondDuality

/-!
# The actual point stabilizer on the second-tensor seed

A pure second-factor element fixing the first natural line acts trivially on
U_H/V₂, by the original first tensor. In the natural four-space its displacement
therefore lies in the first point, so its exterior displacement lies in U₀/U_H.
Consequently it fixes V_H/U₀ pointwise.

The literal V/V₂ section lifts the full natural-line stabilizer into H: fixing
its marked line normalizes V₃, whose perpendicular is V₁. The original-input
application constructs that section, the first tensor, the exterior marking
and the second quotient before applying this argument. It retains the supplied
factor maps, the dual-natural seed, canonical quotient coordinates and original g.
No pointwise fixation on the second quotient is assumed.

This supplies the stabilizer premise for the permutation tensor cover in
13.8.29(4). Its kernel classification, extra-line movement and the subsequent
chief-factor obstruction remain required for the full 13.8.28--32 argument.
Source: Aschbacher--Smith, The Classification of Quasithin Groups,
combined manuscript of 1 March 2004, printed p.964.
-/

public noncomputable section
open Subgroup Representation
open scoped TensorProduct MatrixGroups commutatorElement IsMulCommutative
open CyclicSeedTensor QuadraticFourGroup.TensorClassification
open Atlas.Order20160A8.Bivectors (exteriorMap)
open BinaryParabolicExteriorSquare.PlaneSpan
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G K I U Y : Type*} [Group G] [Group K] [Group I]
  [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- First-tensor fixation propagates through the exterior marking to the actual second seed. -/
theorem source_second_seed_fixed_of_first_row
    (H UH VH V1 V2 : Subgroup G)
    (π : G2 V2 →* K × I) (σ : Representation (ZMod 2) K U)
    (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
    (dt : BinaryConjugationSection (G2 V2) (U0 UH V2) V2 ((externalTensor σ μ).comp π))
    (κ : ↥(H ⊓ G2 V2) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V2) UH V2 (σ.comp κ))
    (hU : ∀ u : UH, (dt.coordinates (inclusion (UH_le_U0 UH V2) u)).toAdd =
      (dU.coordinates u).toAdd ⊗ₜ[ZMod 2] first)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π₄ : H →* SL(4,ZMod 2))
    (hnatural : ∀ h x, ρ h x = (π₄ h).val.mulVec x)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {Pi.single 0 1})
    (ξ : Representation (ZMod 2) H Six)
    (p : BinaryConjugationSection H VH UH ξ)
    (hact : ∀ h x, ξ h x = exteriorMap (π₄ h).val x)
    (hfirst : p.imageSpace (U0 UH V2) = firstSpace)
    (τ : Representation (ZMod 2) (K × I) Y)
    (q : BinaryConjugationSection (G2 V2) (V0 VH V2) (U0 UH V2) (τ.comp π))
    (a : ↥(H ⊓ G2 V2)) (i : I)
    (hai : π (inclusion (show H ⊓ G2 V2 ≤ G2 V2 from inf_le_right) a) = (1,i))
    (hifirst : μ i first = first) :
    ∀ w ∈ q.imageSpace VH, τ (1,i) w = w := by
  let aH : H := ⟨a,a.property.1⟩
  let aG : G2 V2 := ⟨a,a.property.2⟩
  change π aG = (1,i) at hai
  have hc (u : UH) : ⁅(a:G),(u:G)⁆ ∈ V2 := by
    let z : U0 UH V2 :=
      ⟨⁅(a:G),(u:G)⁆, by
        rw [commutatorElement_def]
        exact (U0 UH V2).mul_mem
          ((mem_normalizer_iff.mp (dt.normalized aG.property) u).mp (UH_le_U0 UH V2 u.property))
          ((U0 UH V2).inv_mem (UH_le_U0 UH V2 u.property))⟩
    apply (dt.coordinates_eq_one_iff z).mp
    apply Multiplicative.toAdd.injective
    change (dt.coordinates
      (⟨(a:G)*u*(a:G)⁻¹, (mem_normalizer_iff.mp (dt.normalized aG.property) u).mp (UH_le_U0 UH V2 u.property)⟩ * (inclusion (UH_le_U0 UH V2) u)⁻¹)).toAdd = 0
    rw [map_mul,map_inv]
    simp only [toAdd_mul,toAdd_inv,←sub_eq_add_neg]
    change (dt.coordinates ⟨(a:G)*u*(a:G)⁻¹, (mem_normalizer_iff.mp (dt.normalized aG.property) u).mp (UH_le_U0 UH V2 u.property)⟩).toAdd -
      (dt.coordinates (inclusion (UH_le_U0 UH V2) u)).toAdd = 0
    have heq := dt.equivariant aG (inclusion (UH_le_U0 UH V2) u)
    change (dt.coordinates ⟨(a:G)*u*(a:G)⁻¹,
      (mem_normalizer_iff.mp (dt.normalized aG.property) u).mp (UH_le_U0 UH V2 u.property)⟩).toAdd = _ at heq
    rw [heq]
    change externalTensor σ μ (π aG) _ - _ = 0
    rw [hai,hU,externalTensor_apply,TensorProduct.map_tmul,hifirst]
    simp
  have hdisp (w : Fin 4 → ZMod 2) :
      (π₄ aH).val.mulVec w - w ∈ Submodule.span (ZMod 2) {Pi.single 0 1} := by
    obtain ⟨u,hu⟩ := d.onto (Multiplicative.ofAdd w)
    let z : UH := ⟨⁅(a:G),(u:G)⁆, by
      rw [commutatorElement_def]
      exact UH.mul_mem ((mem_normalizer_iff.mp (d.normalized aH.property) u).mp u.property)
        (UH.inv_mem u.property)⟩
    have hz : (d.coordinates z).toAdd = ρ aH (d.coordinates u).toAdd - (d.coordinates u).toAdd := by
      change (d.coordinates (⟨(a:G)*u*(a:G)⁻¹,(mem_normalizer_iff.mp (d.normalized aH.property) u).mp u.property⟩ * u⁻¹)).toAdd = _
      rw [map_mul,map_inv]
      simp only [toAdd_mul,toAdd_inv,←sub_eq_add_neg]
      change (d.coordinates ⟨(a:G)*u*(a:G)⁻¹,(mem_normalizer_iff.mp (d.normalized aH.property) u).mp u.property⟩).toAdd - (d.coordinates u).toAdd = _
      rw [d.equivariant aH]
    rw [←hnatural,←show (d.coordinates u).toAdd = w from congrArg Multiplicative.toAdd hu,←hz,←hpoint]
    exact (d.mem_imageSpace_iff _ _).mpr ⟨z,hc u,rfl⟩
  intro w hw
  obtain ⟨v,hv,rfl⟩ := (q.mem_imageSpace_iff VH w).mp hw
  let vH : VH := ⟨v,hv⟩
  let z : VH := ⟨⁅(a:G),(v:G)⁆, by
    rw [commutatorElement_def]
    exact VH.mul_mem ((mem_normalizer_iff.mp (p.normalized aH.property) v).mp hv) (VH.inv_mem hv)⟩
  have hz : (p.coordinates z).toAdd = ξ aH (p.coordinates vH).toAdd - (p.coordinates vH).toAdd := by
    change (p.coordinates (⟨(a:G)*v*(a:G)⁻¹,(mem_normalizer_iff.mp (p.normalized aH.property) v).mp hv⟩ * vH⁻¹)).toAdd = _
    rw [map_mul,map_inv]
    simp only [toAdd_mul,toAdd_inv,←sub_eq_add_neg]
    change (p.coordinates ⟨(a:G)*v*(a:G)⁻¹,(mem_normalizer_iff.mp (p.normalized aH.property) v).mp hv⟩).toAdd - (p.coordinates vH).toAdd = _
    rw [p.equivariant aH vH]
  have hzU : (z:G) ∈ U0 UH V2 := by
    apply (p.coordinates_mem_imageSpace_iff_of_kernel_le _ (UH_le_U0 UH V2) z).mp
    rw [hz,hact,hfirst]
    exact BinaryParabolicExteriorSquare.exterior_displacement_of_point_displacement _ hdisp _
  have hzq := (q.coordinates_eq_one_iff (inclusion (VH_le_V0 VH V2) z)).mpr hzU
  have hh := congrArg Multiplicative.toAdd hzq
  change (q.coordinates (⟨(a:G)*v*(a:G)⁻¹,(mem_normalizer_iff.mp (q.normalized aG.property) v).mp v.property⟩ * v⁻¹)).toAdd = 0 at hh
  rw [map_mul,map_inv] at hh
  simp only [toAdd_mul,toAdd_inv,←sub_eq_add_neg] at hh
  change (q.coordinates ⟨(a:G)*v*(a:G)⁻¹,(mem_normalizer_iff.mp (q.normalized aG.property) v).mp v.property⟩).toAdd - (q.coordinates v).toAdd = 0 at hh
  rw [q.equivariant aG v] at hh
  change τ (π aG) (q.coordinates v).toAdd - (q.coordinates v).toAdd = 0 at hh
  rw [hai] at hh
  exact sub_eq_zero.mp hh
end CFSG.Quasithin.Chapter13.Section08.LinearFour

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open SourceCompletion TransvectionRecognition.Component.ModelExtension
variable {G K U Y : Type*} [Group G] [Finite G] [Group K]
  [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup Y] [Module (ZMod 2) Y]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}

/-- Fixing the original seed line places the actual I₂ lift in H. -/
theorem source_seed_stabilizer_lift
    (ds : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (H A : Subgroup G) (hHeq : H = normalizer (V₁:Set G))
    (hALT : A ≤ L ⊔ (T:Subgroup G))
    (ι : A →* Equiv.Perm (Fin 3)) (hι : Function.Surjective ι)
    (μ : Representation (ZMod 2) (Equiv.Perm (Fin 3)) (Fin 2 → ZMod 2))
    (c : BinaryConjugationSection A V V₂ (μ.comp ι))
    (hpoint : c.imageSpace V₃ = Submodule.span (ZMod 2) {first})
    (i : Equiv.Perm (Fin 3)) (hi : μ i first = first) :
    ∃ a : A, ι a = i ∧ (a:G) ∈ H := by
  obtain ⟨a,ha⟩ := hι i
  refine ⟨a,ha,?_⟩
  have hn : (a:G) ∈ normalizer (V₃:Set G) := by
    rw [←c.subspacePreimage_imageSpace V₃ ds.seed_le ds.plane_le_seed,
      c.mem_normalizer_subspacePreimage_iff,hpoint,Submodule.map_span,Set.image_singleton]
    change Submodule.span (ZMod 2) {μ (ι a) first} = _
    rw [ha,hi]
  by_contra hh
  rw [hHeq] at hh
  exact source_seed_moved_of_point_moved ds ⟨a,hALT a.property⟩ hh hn

/-- The full stabilizer of the marked first-tensor line fixes the actual
second seed, with the original I₂ quotient map unchanged. -/
theorem source_second_seed_stabilizer
    (ds : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (H UH VH A : Subgroup G) (hHeq : H = normalizer (V₁:Set G))
    (hALT : A ≤ L ⊔ (T:Subgroup G)) (hAG : A ≤ G2 V₂)
    (ι : A →* Equiv.Perm (Fin 3)) (hι : Function.Surjective ι)
    (π : G2 V₂ →* K × Equiv.Perm (Fin 3))
    (hπI : ∀ a : A, π (inclusion hAG a) = (1,ι a))
    (σ : Representation (ZMod 2) K U)
    (μ : Representation (ZMod 2) (Equiv.Perm (Fin 3)) (Fin 2 → ZMod 2))
    (c : BinaryConjugationSection A V V₂ (μ.comp ι))
    (hc : c.imageSpace V₃ = Submodule.span (ZMod 2) {first})
    (dt : BinaryConjugationSection (G2 V₂) (U0 UH V₂) V₂ ((externalTensor σ μ).comp π))
    (κ : ↥(H ⊓ G2 V₂) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V₂) UH V₂ (σ.comp κ))
    (hU : ∀ u : UH, (dt.coordinates (inclusion (UH_le_U0 UH V₂) u)).toAdd =
      (dU.coordinates u).toAdd ⊗ₜ[ZMod 2] first)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V₁ ρ)
    (π₄ : H →* SL(4,ZMod 2))
    (hnatural : ∀ h x, ρ h x = (π₄ h).val.mulVec x)
    (hpoint : d.imageSpace V₂ = Submodule.span (ZMod 2) {Pi.single 0 1})
    (ξ : Representation (ZMod 2) H Six)
    (p : BinaryConjugationSection H VH UH ξ)
    (hact : ∀ h x, ξ h x = exteriorMap (π₄ h).val x)
    (hfirst : p.imageSpace (U0 UH V₂) = firstSpace)
    (τ : Representation (ZMod 2) (K × Equiv.Perm (Fin 3)) Y)
    (q : BinaryConjugationSection (G2 V₂) (V0 VH V₂) (U0 UH V₂) (τ.comp π)) :
    ∀ i, μ i first = first → ∀ w ∈ q.imageSpace VH, τ (1,i) w = w := by
  intro i hi
  obtain ⟨a,ha,haH⟩ := source_seed_stabilizer_lift ds H A hHeq hALT ι hι μ c hc i hi
  exact source_second_seed_fixed_of_first_row H UH VH V₁ V₂ π σ μ dt κ dU hU
    ρ d π₄ hnatural hpoint ξ p hact hfirst τ q ⟨a,haH,hAG a.property⟩ i
    ((hπI a).trans (by rw [ha])) hi
end CFSG.Quasithin.Chapter13.Section08.LinearFour

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open SourceCompletion TransvectionRecognition.Component.ModelExtension BinaryPermutation
open BinaryLinear.OuterCyclic
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open BinaryParabolicExteriorSquare SingularPresentation
open PlaneSpan (pointSpace firstSpace planeSpace)
open BinaryLinear.FlagCoordinates
open Theory.LinearAlgebra BinaryFivePointStabilizer
variable {G K U W : Type*} [Group G] [Finite G] [Group K]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  [AddCommGroup W] [Module (ZMod 2) W]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The original inputs construct the dual-natural second seed together with
pointwise fixation by the stabilizer of the compatible natural first line. -/
theorem source_second_stabilizer_from_original_seed_marked
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
        ∃ (e : Equiv.Perm (Fin 3) ≃* LinearGroup 2)
          (τ : Representation (ZMod 2) (K × Equiv.Perm (Fin 3))
          (Additive (V0 (Source.VH H V) V₂ ⧸
            (U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂))))
          (q : BinaryConjugationSection (G2 V₂) (V0 (Source.VH H V) V₂)
            (U0 (Source.UH H V₃) V₂) (τ.comp π)),
          (∃ cV : BinaryConjugationSection A V V₂
            ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp e.toMonoidHom).comp
              (eI.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A)))),
            cV.imageSpace V₃ = Submodule.span (ZMod 2) {first}) ∧
          (∀ v : V0 (Source.VH H V) V₂, (q.coordinates v).toAdd =
            Additive.ofMul (QuotientGroup.mk'
              ((U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂)) v)) ∧
          (∃ f : σ.dual.IntertwiningMap (τ.comp (MonoidHom.inl K (Equiv.Perm (Fin 3)))),
            Function.Injective f ∧ f.range.toSubmodule = q.imageSpace (Source.VH H V)) ∧
          Module.finrank (ZMod 2) (q.imageSpace (Source.VH H V)) = 3 ∧
          Disjoint (q.imageSpace (Source.VH H V))
            ((q.imageSpace (Source.VH H V)).map (τ (π (inclusion hAG g)⁻¹))) ∧
          (⨆ a : G2 V₂, (q.imageSpace (Source.VH H V)).map (τ (π a))) = ⊤ ∧
          (∀ i, e i first = first → ∀ w ∈ q.imageSpace (Source.VH H V), τ (1,i) w = w) ∧
          e (eI (QuotientGroup.mk' (pCore 2 A) g⁻¹)) first = second ∧
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
  let ι := eI.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hι : Function.Surjective ι := eI.surjective.comp (QuotientGroup.mk'_surjective _)
  have hιker : ∀ a : A, ι a = 1 ↔ (a:G) ∈ centralizer (V₂:Set G) := by
    intro a
    change eI (QuotientGroup.mk' (pCore 2 A) a) = 1 ↔ _
    rw [eI.map_eq_one_iff]
    change (QuotientGroup.mk a : A ⧸ pCore 2 A) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro ha
      have hh : (a:G) ∈ A.pCoreIn 2 := mem_map_of_mem A.subtype ha
      rw [hAcore] at hh
      exact hh.2
    · intro ha
      have hh : (a:G) ∈ A.pCoreIn 2 := hAcore ▸ ⟨a.property,ha⟩
      exact (mem_map_iff_mem A.subtype_injective).mp hh
  have hgmove := source_seed_moved_of_point_moved ds ⟨g,hALT g.property⟩ (by
    change (g:G) ∉ normalizer (V₁:Set G)
    rwa [← hHeq])
  obtain ⟨e,cV,E,hcoord,hseedpoint,ha,b,hb₀,hb₁⟩ :=
    source_seed_natural_marking ds A hALT hVA hAG ι hι hιker g hgmove
  have hindex : V₂.relIndex V₃ = 2 := by
    have hh := (V₂.subgroupOf V₃).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe ds.plane_le_seed).toEquiv,ds.plane_card,ds.seed_card] at hh
    change 4 * V₂.relIndex V₃ = 8 at hh
    omega
  obtain ⟨hVS,u₀,dt,hu,hU,hseed,hprod,hint₁,hcard⟩ :=
    source_tensor_from_local_sections H (Source.UH H V₃) V₂ V₃ V A L2 (T:Subgroup G)
      hK hG hV ds.seed_le π hπ hπker hcore σ
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp e.toMonoidHom)
      κ dU hκker hκ hπK ι hι cV hAG hπI (le_conjugateSpanBy _ _) hgen hindex hseedpoint hdim
      (ι g⁻¹) b ha hb₀ hb₁ (inclusion hAG g) (hπI g⁻¹)
  obtain ⟨f,hf,hr⟩ := source_second_dual_natural_embedding
    H (Source.UH H V₃) V₂ V π σ
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp e.toMonoidHom)
    dt κ dU hκ hU hπK (action π₄) p₆ π₄ (fun _ _ => rfl) hUV hpU hdim
    (inclusion hAG g) (congrArg Prod.fst (hπI g⁻¹)) hint₁ τ q
  have hfix := source_second_seed_stabilizer ds H (Source.UH H V₃) (Source.VH H V) A
    hHeq hALT hAG ι hι π hπI σ
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp e.toMonoidHom)
    cV hseedpoint dt κ dU hU ρ d π₄ hnatural hpoint (action π₄) p₆
    (fun _ _ => rfl) hpU τ q
  exact ⟨hn,he,e,τ,q,⟨cV,hseedpoint⟩,hq,⟨f,hf,hr⟩,hd,hdis,hspan,hfix,ha,hmin⟩

/-- The original public stabilizer interface, retaining its established statement. -/
theorem source_second_stabilizer_from_original_seed
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
        ∃ (e : Equiv.Perm (Fin 3) ≃* LinearGroup 2)
          (τ : Representation (ZMod 2) (K × Equiv.Perm (Fin 3))
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
          (∀ i, e i first = first → ∀ w ∈ q.imageSpace (Source.VH H V), τ (1,i) w = w) ∧
          e (eI (QuotientGroup.mk' (pCore 2 A) g⁻¹)) first = second ∧
          ∀ B : Subgroup G, U0 (Source.UH H V₃) V₂ ≤ B → B ≤ Source.VH H V →
            K2 H V₂ ≤ normalizer B → B = U0 (Source.UH H V₃) V₂ ∨ B = Source.VH H V := by
  obtain ⟨hn,he,e,τ,q,_,hq,hf,hd,hdis,hspan,hfix,ha,hmin⟩ :=
    source_second_stabilizer_from_original_seed_marked s hab h hH hcentral hHeq A L2 hK hG hV
      π hπ hπker hcore σ κ dU hκker hκ hπK eI hAcore hQA hnA hALT hVA hAG hπI
      hgen hdim g hg ρ d π₄ hker honto hnatural hpoint hplane eU hcoords hUcard hu hgenerate
  exact ⟨hn,he,e,τ,q,hq,hf,hd,hdis,hspan,hfix,ha,hmin⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour
