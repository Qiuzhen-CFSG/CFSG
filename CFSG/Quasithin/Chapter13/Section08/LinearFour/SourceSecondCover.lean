module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSecondStabilizer
public import Theory.Representation.TransitiveSeedCover

/-!
# The permutation tensor cover of the literal second quotient

The actual dual-natural K₂ seed is fixed by the stabilizer of the original
natural I₂ line. Its three-point orbit therefore constructs a surjective
intertwiner from the dual-natural module tensored with the three-point
permutation module onto V₀/U₀. The marked slice is exactly V_H/U₀, and
conjugate generation proves surjectivity. In particular this quotient has
binary dimension at most nine.

The full original-input application constructs the seed, its point stabilizer
and both quotient actions, preserving the canonical quotient projection and
the specified g. The natural and natural-plus-trivial alternatives still
require the kernel classification of this cover; neither row is an input or
asserted here. The subsequent movement and chief-factor obstruction remain
with the same source-theorem owner.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
combined manuscript of 1 March 2004, 13.8.29(4), printed p.964.
-/

public noncomputable section
open Subgroup Representation
open scoped TensorProduct MatrixGroups IsMulCommutative
open CyclicSeedTensor QuadraticFourGroup.TensorClassification
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

/-- Construct the actual second quotient as a quotient of the dual-natural
module tensored with the three-point permutation module, preserving the
marked seed, both factor maps and the original conjugator. -/
theorem source_second_cover_from_original_seed_marked
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
              Function.Surjective F ∧ ∀ u,
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
  obtain ⟨hn,he,e,τ,q,hseed,hq,⟨f,hf,hr⟩,hd,hdis,hspan,hfix,ha,hmin⟩ :=
    source_second_stabilizer_from_original_seed_marked s hab h hH hcentral hHeq A L2 hK hG hV
      π hπ hπker hcore σ κ dU hκker hκ hπK eI hAcore hQA hnA hALT hVA hAG hπI
      hgen hdim g hg ρ d π₄ hker honto hnatural hpoint hplane eU hcoords hUcard hu hgenerate
  let := hn
  let := he
  have hspan' : (⨆ a : K × Equiv.Perm (Fin 3), f.range.toSubmodule.map (τ a)) = ⊤ := by
    apply top_unique
    rw [←hspan]
    apply iSup_le
    intro a
    rw [←hr]
    exact le_iSup (fun b : K × Equiv.Perm (Fin 3) => f.range.toSubmodule.map (τ b)) (π a)
  obtain ⟨F,hF,hmark⟩ := TransitiveSeedCover.exists_binary_plane_cover
    e.toMonoidHom τ σ.dual f e.surjective
      (fun i hi u => hfix i hi _ (hr ▸ (show f u ∈ f.range.toSubmodule from ⟨u,rfl⟩))) hspan'
  have hbound := LinearMap.finrank_le_finrank_of_surjective (f:=F.toLinearMap) hF
  rw [Module.finrank_tensorProduct,Subspace.dual_finrank_eq,hdim,
    Module.finrank_pi,TransitiveSeedCover.planePoint_card] at hbound
  exact ⟨hn,he,e,τ,q,hseed,hq,⟨f,hf,hr,F,hF,hmark⟩,hbound,hd,hdis,hspan,hfix,ha,hmin⟩

/-- The original public cover interface, retaining its established statement. -/
theorem source_second_cover_from_original_seed
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
            Function.Injective f ∧ f.range.toSubmodule = q.imageSpace (Source.VH H V) ∧
            ∃ F : (externalTensor σ.dual
              (TransitiveSeedCover.permutation (k:=ZMod 2)
                (TransitiveSeedCover.pointAction e.toMonoidHom))).IntertwiningMap τ,
              Function.Surjective F ∧ ∀ u,
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
  obtain ⟨hn,he,e,τ,q,_,hq,hf,hbound,hd,hdis,hspan,hfix,ha,hmin⟩ :=
    source_second_cover_from_original_seed_marked s hab h hH hcentral hHeq A L2 hK hG hV
      π hπ hπker hcore σ κ dU hκker hκ hπK eI hAcore hQA hnA hALT hVA hAG hπI
      hgen hdim g hg ρ d π₄ hker honto hnatural hpoint hplane eU hcoords hUcard hu hgenerate
  exact ⟨hn,he,e,τ,q,hq,hf,hbound,hd,hdis,hspan,hfix,ha,hmin⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour
