module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSecondCover
public import Theory.Representation.TransitiveSeedCover.Kernel
public import Theory.Representation.BinaryConjugationSection.SubspacePreimages

/-!
# The invariant kernel of the literal second tensor cover

The actual K₂-minimal interval U₀ < V_H makes the marked dual-natural seed
irreducible: lift an invariant subspace through the original quotient map.
The specified disjoint g-translate then forces every kernel vector of the
three-point permutation tensor cover to be constant. Irreducibility leaves
exactly zero or the whole dual-natural tensor constant line.

The original-input theorem constructs this dichotomy without an additional
kernel or irreducibility premise and preserves both actor maps, the seed
slice and the same g. Identifying the two quotient rows and the subsequent
chief-factor obstruction remain separate steps of the source proof.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29(4), printed p.964.
-/

public noncomputable section
open Subgroup Representation
open scoped TensorProduct
open QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour

variable {G K I U Y : Type*} [Group G] [Group K] [Group I]
  [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- The original minimal subgroup interval makes its equivariantly marked seed irreducible. -/
theorem source_second_seed_irreducible
    (H UH VH V2 : Subgroup G) (hUV : U0 UH V2 ≤ VH)
    (π : G2 V2 →* K × I) (τ : Representation (ZMod 2) (K × I) Y)
    (q : BinaryConjugationSection (G2 V2) (V0 VH V2) (U0 UH V2) (τ.comp π))
    (σ : Representation (ZMod 2) K U)
    (κ : K2 H V2 →* K)
    (hπK : ∀ k : K2 H V2,
      π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k) = (κ k,1))
    (f : σ.IntertwiningMap (τ.comp (MonoidHom.inl K I)))
    (hf : Function.Injective f) (hr : f.range.toSubmodule = q.imageSpace VH)
    (hmin : ∀ B : Subgroup G, U0 UH V2 ≤ B → B ≤ VH → K2 H V2 ≤ normalizer B →
      B = U0 UH V2 ∨ B = VH)
    (S : Submodule (ZMod 2) U) (hS : ∀ g u, u ∈ S → σ g u ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  let P := S.map f.toLinearMap
  let B := q.subspacePreimage P
  have hPB : P ≤ q.imageSpace VH := by
    rw [←hr]
    rintro _ ⟨u,_,rfl⟩
    exact ⟨u,rfl⟩
  have hclosed (k : K2 H V2) (w : Y) (hw : w ∈ P) :
      τ (π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k)) w ∈ P := by
    obtain ⟨u,hu,rfl⟩ := hw
    refine ⟨σ (κ k) u,hS _ _ hu,?_⟩
    rw [hπK]
    exact IntertwiningMap.isIntertwining _ _ f (κ k) u
  have hnorm : K2 H V2 ≤ normalizer B := by
    intro k hk
    let a : K2 H V2 := ⟨k,hk⟩
    let b := inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) a
    apply (q.mem_normalizer_subspacePreimage_iff P b).mpr
    apply le_antisymm
    · rintro _ ⟨w,hw,rfl⟩
      exact hclosed a w hw
    · intro w hw
      refine ⟨τ (π b⁻¹) w,hclosed a⁻¹ w hw,?_⟩
      change τ (π b) (τ (π b⁻¹) w) = w
      simp only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  have hkernel : q.imageSpace (U0 UH V2) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro w hw
    obtain ⟨u,hu,rfl⟩ := (q.mem_imageSpace_iff _ w).mp hw
    rw [(q.coordinates_eq_one_iff u).mpr hu]
    exact Submodule.zero_mem _
  rcases hmin B (q.kernel_le_subspacePreimage P)
    (q.subspacePreimage_le_of_imageSpace_le P VH hUV hPB) hnorm with hB | hB
  · left
    have hP : P = ⊥ := by rw [←q.imageSpace_subspacePreimage P]; change q.imageSpace B = ⊥; rw [hB,hkernel]
    apply le_antisymm ?_ bot_le
    intro u hu
    have hfu : f u ∈ P := ⟨u,hu,rfl⟩
    rw [hP] at hfu
    exact hf ((show f u = 0 from hfu).trans (map_zero f).symm)
  · right
    have hP : P = f.range.toSubmodule := by
      rw [hr,←q.imageSpace_subspacePreimage P]; change q.imageSpace B = _; rw [hB]
    apply top_unique
    intro u _
    have hfu : f u ∈ P := hP ▸ (show f u ∈ f.range.toSubmodule from ⟨u,rfl⟩)
    obtain ⟨v,hv,he⟩ := hfu
    exact hf he ▸ hv

end CFSG.Quasithin.Chapter13.Section08.LinearFour

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open scoped MatrixGroups IsMulCommutative
open CyclicSeedTensor
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

/-- Classify the kernel of the actual second quotient cover, preserving the
marked seed, both factor maps and the original conjugator. -/
theorem source_second_kernel_from_original_seed
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
            Function.Injective f ∧ f.range.toSubmodule = q.imageSpace (Source.VH H V) ∧
            ∃ F : (externalTensor σ.dual
              (TransitiveSeedCover.permutation (k:=ZMod 2)
                (TransitiveSeedCover.pointAction e.toMonoidHom))).IntertwiningMap τ,
              Function.Surjective F ∧
              (F.ker.toSubmodule = ⊥ ∨ F.ker.toSubmodule = LinearMap.range
                (TransitiveSeedCover.constantTensor (k:=ZMod 2) (U:=Module.Dual (ZMod 2) U)
                  (X:=TransitiveSeedCover.PlanePoint))) ∧ ∀ u,
                F (u ⊗ₜ[ZMod 2] Pi.single TransitiveSeedCover.basePoint 1) = f u) ∧
          Module.finrank (ZMod 2) (Additive (V0 (Source.VH H V) V₂ ⧸
            (U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂))) ≤ 9 ∧
          Module.finrank (ZMod 2) (q.imageSpace (Source.VH H V)) = 3 ∧
          Disjoint (q.imageSpace (Source.VH H V))
            ((q.imageSpace (Source.VH H V)).map (τ (π (inclusion hAG g)⁻¹))) ∧
          (⨆ a : G2 V₂, (q.imageSpace (Source.VH H V)).map (τ (π a))) = ⊤ ∧
          (∀ i, e i first = first → ∀ w ∈ q.imageSpace (Source.VH H V), τ (1,i) w = w) ∧
          e (eI (QuotientGroup.mk' (pCore 2 A) g⁻¹)) first = second ∧
          ∀ B : Subgroup G, U0 (Source.UH H V₃) V₂ ≤ B → B ≤ Source.VH H V →
            K2 H V₂ ≤ normalizer B → B = U0 (Source.UH H V₃) V₂ ∨ B = Source.VH H V := by
  obtain ⟨hn,he,e,τ,q,hseed,hq,⟨f,hf,hr,F,hF,hmark⟩,hbound,hd,hdis,hspan,hfix,ha,hmin⟩ :=
    source_second_cover_from_original_seed_marked s hab h hH hcentral hHeq A L2 hK hG hV
      π hπ hπker hcore σ κ dU hκker hκ hπK eI hAcore hQA hnA hALT hVA hAG hπI
      hgen hdim g hg ρ d π₄ hker honto hnatural hpoint hplane eU hcoords hUcard hu hgenerate
  let := hn
  let := he
  have hUV := source_U0_le_VH_of_normal_factors H (Source.UH H V₃) V₂ V₃ V L2 (T:Subgroup G)
    hK hG hV hgen s.seed_le
  have hirr := source_second_seed_irreducible H (Source.UH H V₃) (Source.VH H V) V₂
    hUV π τ q σ.dual (κ.comp (inclusion (K2_le_localNormalizer H V₂))) hπK f hf hr hmin
  let c := eI (QuotientGroup.mk' (pCore 2 A) g⁻¹)
  have hc : TransitiveSeedCover.basePoint ≠
      TransitiveSeedCover.pointAction e.toMonoidHom c TransitiveSeedCover.basePoint := by
    intro heq
    have hh := congrArg Subtype.val heq
    change first = e c first at hh
    rw [ha] at hh
    exact (by decide : (first : Fin 2 → ZMod 2) ≠ second) hh
  have hd' : Disjoint f.range.toSubmodule (f.range.toSubmodule.map (τ (1,c))) := by
    rw [hr]
    have hp := hπI g⁻¹
    change π (inclusion hAG g)⁻¹ = (1,c) at hp
    rwa [hp] at hdis
  have hkerF := TransitiveSeedCover.tensor_kernel_dichotomy_of_disjoint τ σ.dual
    (TransitiveSeedCover.pointAction e.toMonoidHom) F
    (TransitiveSeedCover.pointAction_surjective e.toMonoidHom e.surjective)
    TransitiveSeedCover.basePoint c hc f hf hmark hd' hirr
  exact ⟨hn,he,e,τ,q,hseed,hq,⟨f,hf,hr,F,hF,hkerF,hmark⟩,hbound,hd,hdis,hspan,hfix,ha,hmin⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour
