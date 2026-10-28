module
public import Theory.Representation.BinaryConjugationSection.FactorEmbedding
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceNormalizerProduct
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceTensorIntersection

/-!
# Compatible coordinates for the first source tensor

Choose the first factor of G₂/O₂(G₂) to be exactly the action on the
literal U_H/V₂ constructed from the given natural four-space. The I₂
factor retains its original quotient map. Thus the natural section and
the product quotient use one marking, with the same coordinate projection
from U_H/V₁.

The inclusions of U_H/V₂ and V/V₂ into U₀/V₂ now construct both tensor
seed embeddings. A single element of V₃ represents their shared nonzero
vector. The original K₂-conjugate generation and |V₃:V₂| = 2 supply
cyclicity. The resulting tensor equivalence retains both coordinate maps,
the specified conjugator, the intersection of its two U_H copies, and
the index |U₀:V| = 16. The final application discharges the independent
embedding and cyclicity premises in the literal V_H intersection argument.

The action on U₀/V₂ through the product quotient and the marked natural
V/V₂ section remain explicit inputs. The exterior and second-tensor
markings, extra-line movement and chief-factor obstruction still need
proof; this does not complete 13.8.28. Earlier 13.8.27 remains with
qt-d-138-six-g2-source, and final 13.8.1 assembly with qt-d-1381-source.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29(2--3), printed p.964, combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Representation BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G : Type*} [Group G] [Finite G]

/-- Choose the product quotient so that its first factor is the action on
the literal natural point quotient, retaining the supplied I₂ quotient map. -/
theorem source_product_with_natural_section
    (H UH V1 V2 : Subgroup G) [IsMulCommutative UH]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (φ : H →* LinearGroup 4) (hφ : Function.Surjective φ)
    (hnatural : ∀ h x, ρ h x = φ h x) (hker : IsPGroup 2 φ.ker)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ UH)
    (v : Fin 4 → ZMod 2) (hv : v ≠ 0)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {v})
    (I : Subgroup (G2 V2)) [I.Normal]
    (eI : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3))
    (hgen : I ⊔ H.subgroupOf (G2 V2) = ⊤) :
    ∃ (κ : ↥(H ⊓ G2 V2) →* LinearGroup 3)
      (dU : BinaryConjugationSection (H ⊓ G2 V2) UH V2
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp κ))
      (eU : Theory.LinearAlgebra.BinaryFivePointStabilizer.QuotientSpace v ≃ₗ[ZMod 2]
        (Fin 3 → ZMod 2))
      (π : G2 V2 →* LinearGroup 3 × Equiv.Perm (Fin 3)),
      Function.Surjective κ ∧ κ.ker = pCore 2 ↥(H ⊓ G2 V2) ∧
      Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V2))) ∧
      Function.Surjective π ∧ π.ker = pCore 2 (G2 V2) ∧
      (∀ u : UH, (dU.coordinates u).toAdd =
        eU ((Theory.LinearAlgebra.BinaryFivePointStabilizer.line v).mkQ (d.coordinates u).toAdd)) ∧
      (∀ k : K2 H V2,
        π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k) =
          (κ (inclusion (K2_le_localNormalizer H V2) k),1)) ∧
      ∀ i : I, π i = (1,eI (QuotientGroup.mk' (pCore 2 I) i)) := by
  obtain ⟨κ,dU,eU,hκ,hκker,hK,hKker,hcoord⟩ := source_point_quotient_marking
    H UH V1 V2 ρ d φ hφ hnatural hker h12 h2U v hv hpoint
  obtain ⟨eK,e,hKe,hIe⟩ := source_normalizer_product_quotient
    H UH V1 V2 ρ d φ hφ hnatural hker h12 h2U v hv hpoint I eI hgen
  let f := κ.comp (inclusion (K2_le_localNormalizer H V2))
  let c := (QuotientGroup.quotientMulEquivOfEq hKker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hK)
  let r := (eK.symm.trans c).prodCongr (MulEquiv.refl (Equiv.Perm (Fin 3)))
  let e' := e.trans r
  let π := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (G2 V2)))
  have hπ : Function.Surjective π := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : π.ker = pCore 2 (G2 V2) := by
    dsimp only [π]
    rw [MonoidHom.ker_comp_of_injective _ _ e'.injective,QuotientGroup.ker_mk']
  refine ⟨κ,dU,eU,π,hκ,hκker,hK,hπ,hk,hcoord,?_,?_⟩
  · intro k
    change r (e (QuotientGroup.mk' (pCore 2 (G2 V2)) _)) = _
    rw [hKe]
    change (c (eK.symm (eK _)),1) = _
    rw [eK.symm_apply_apply]
    rfl
  · intro i
    change r (e (QuotientGroup.mk' (pCore 2 (G2 V2)) i)) = _
    rw [hIe]
    change (c (eK.symm 1),_) = _
    rw [map_one,map_one]
    rfl
end CFSG.Quasithin.Chapter13.Section08.LinearFour

public noncomputable section
open Subgroup Representation
open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification
open scoped TensorProduct
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G K I U W : Type*} [Group G] [Finite G] [Group K] [Group I]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
  (H UH V2 V3 V A : Subgroup G) (π : G2 V2 →* K × I)
  (ρ : Representation (ZMod 2) (K × I) W)
  (σ : Representation (ZMod 2) K U) (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
  (d : BinaryConjugationSection (G2 V2) (U0 UH V2) V2 (ρ.comp π))
  (κ : ↥(H ⊓ G2 V2) →* K)
  (dU : BinaryConjugationSection (H ⊓ G2 V2) UH V2 (σ.comp κ))
  (hκ : Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V2))))
  (hπK : ∀ k : K2 H V2,
    π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k) =
      (κ (inclusion (K2_le_localNormalizer H V2) k),1))
  (ι : A →* I) (hι : Function.Surjective ι)
  (dV : BinaryConjugationSection A V V2 (μ.comp ι))
  (hAG : A ≤ G2 V2)
  (hπI : ∀ a : A, π (inclusion hAG a) = (1,ι a))
  (hVS : V ≤ U0 UH V2) (h3U : V3 ≤ UH)
  (hgen : UH = conjugateSpanBy V3 (K2 H V2))
  (hindex : V2.relIndex V3 = 2)
  (hpoint : dV.imageSpace V3 = Submodule.span (ZMod 2) {first})

include hκ hπK hι hAG hπI h3U hgen hindex hpoint in
/-- The two literal section maps construct compatible seed embeddings.
The common vector is represented by one element of V₃, and the original
K₂-conjugate generation proves its cyclicity. -/
theorem source_tensor_seeds_from_sections :
    ∃ (f : σ.IntertwiningMap (ρ.comp (MonoidHom.inl K I)))
      (t : μ.IntertwiningMap (ρ.comp (MonoidHom.inr K I))) (u₀ : U),
      Function.Injective f ∧ f.range.toSubmodule = d.imageSpace UH ∧
      t.range.toSubmodule = d.imageSpace V ∧ t first = f u₀ ∧ u₀ ≠ 0 ∧
      Submodule.span (ZMod 2) (Set.range fun k => σ k u₀) = ⊤ ∧
      (∀ u : UH, f (dU.coordinates u).toAdd =
        (d.coordinates (inclusion (UH_le_U0 UH V2) u)).toAdd) ∧
      ∀ v : V, t (dV.coordinates v).toAdd =
        (d.coordinates (inclusion hVS v)).toAdd := by
  obtain ⟨f,hf,hfimage,hfc⟩ := d.exists_factor_embedding π κ (MonoidHom.inl K I)
    dU inf_le_right (UH_le_U0 UH V2) (K2_le_localNormalizer H V2) hκ hπK
  obtain ⟨t,_,htimage,htc⟩ := d.exists_factor_embedding π ι (MonoidHom.inr K I)
    dV hAG hVS le_rfl (by intro i; obtain ⟨a,rfl⟩ := hι i; exact ⟨a,rfl⟩) hπI
  obtain ⟨z,hz,hzc⟩ := (dV.mem_imageSpace_iff V3 first).mp
    (hpoint.symm ▸ Submodule.subset_span (Set.mem_singleton first))
  let zU : UH := ⟨z,h3U hz⟩
  let u₀ : U := (dU.coordinates zU).toAdd
  have hfirst0 : (first : Fin 2 → ZMod 2) ≠ 0 := by
    intro he
    have hh := congrFun he 0
    simp [first] at hh
  have hu : u₀ ≠ 0 := by
    intro hu
    have hz2 : (z:G) ∈ V2 := (dU.coordinates_eq_one_iff zU).mp hu
    have he : (dV.coordinates z).toAdd = 0 := (dV.coordinates_eq_one_iff z).mpr hz2
    exact hfirst0 (hzc.symm.trans he)
  have hseed : dU.imageSpace V3 = Submodule.span (ZMod 2) {u₀} :=
    eq_span_singleton_of_mem_of_finrank_eq_one
      (dU.imageSpace_finrank_of_index V3 h3U 1 (by simpa using hindex))
      ((dU.mem_imageSpace_iff V3 u₀).mpr ⟨zU,hz,rfl⟩) hu
  refine ⟨f,t,u₀,hf,hfimage,htimage,?_,hu,?_,hfc,htc⟩
  · rw [←hzc,htc,hfc]
    rfl
  · exact dU.cyclic_of_seed_span κ (K2 H V2) V3 (K2_le_localNormalizer H V2)
      hgen u₀ hseed

include hκ hπK hι hAG hπI h3U hgen hindex hpoint in
/-- The original section coordinates give the tensor model, both conjugate
copies, their intersection and the order-sixteen section over V. -/
theorem source_tensor_from_sections [FiniteDimensional (ZMod 2) U]
    (hdim : Module.finrank (ZMod 2) U = 3)
    (a b : I) (ha : μ a first = second)
    (hb0 : μ b first = first) (hb1 : μ b second = first + second)
    (g : G2 V2) (hg : π g⁻¹ = (1,a)) :
    ∃ (u₀ : U) (E : (externalTensor σ μ).Equiv ρ), u₀ ≠ 0 ∧
      (∀ u : UH, E ((dU.coordinates u).toAdd ⊗ₜ[ZMod 2] first) =
        (d.coordinates (inclusion (UH_le_U0 UH V2) u)).toAdd) ∧
      (∀ v : V, E (u₀ ⊗ₜ[ZMod 2] (dV.coordinates v).toAdd) =
        (d.coordinates (inclusion hVS v)).toAdd) ∧
      U0 UH V2 = UH ⊔ UH.conjBy ((g:G)⁻¹) ∧
      UH ⊓ UH.conjBy ((g:G)⁻¹) = V2 ∧ V.relIndex (U0 UH V2) = 16 := by
  obtain ⟨f,t,u₀,hf,hfimage,htimage,ht,hu,hcyclic,hfc,htc⟩ :=
    source_tensor_seeds_from_sections H UH V2 V3 V A π ρ σ μ d κ dU hκ hπK
      ι hι dV hAG hπI hVS h3U hgen hindex hpoint
  let E := source_tensor_coordinates UH V2 π ρ σ μ d f hfimage u₀ hcyclic
    t ht a ha hf b hb0 hb1
  have hp := source_tensor_two_conjugates UH V2 π ρ σ μ d f hfimage u₀ hcyclic
    t ht a ha hf b hb0 hb1 g hg dU.kernel_le
  refine ⟨u₀,E,hu,?_,?_,hp.1,hp.2,?_⟩
  · intro u
    change tensorMap ρ σ f a ((dU.coordinates u).toAdd ⊗ₜ[ZMod 2] first) = _
    rw [tensorMap_tmul]
    simpa [first] using hfc u
  · intro v
    exact (seed_tensor ρ σ μ f a u₀ t ht ha _).trans (htc v)
  · exact source_tensor_seed_index UH V2 π ρ σ μ d f hfimage u₀ hcyclic
      t ht a ha hf b hb0 hb1 hdim hu V dV.kernel_le hVS htimage

include d dU dV hκ hπK hι hAG hπI hVS h3U hgen hindex hpoint in
/-- The literal section construction discharges the seed-embedding and
cyclic-vector premises in the original tensor-intersection application. -/
theorem source_tensor_intersection_from_sections
    (L T M : Subgroup G)
    (a b : I) (ha : μ a first = second)
    (hb0 : μ b first = first) (hb1 : μ b second = first + second)
    (hker : π.ker ≤ H.subgroupOf (G2 V2))
    (g : G2 V2) (hg : π g⁻¹ = (1,a))
    (h3V : V3 ≤ V) (hseed : V3.conjBy ((g:G)⁻¹) ≤ V)
    (ξ : Representation (ZMod 2) H BinaryParabolicExteriorSquare.PlaneSpan.Six)
    (dx : BinaryConjugationSection H (Source.VH H V) UH ξ)
    (π₄ : H →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (hact : ∀ h x, ξ h x = Atlas.Order20160A8.Bivectors.exteriorMap (π₄ h).val x)
    (hfirst : dx.imageSpace (U0 UH V2) = BinaryParabolicExteriorSquare.PlaneSpan.firstSpace)
    (hactors : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j →
      ∃ k : K2 H V2,
        (π₄ (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k)).val =
          Matrix.transvection i j 1)
    (hp : IsPGroup 2 (Source.VH H V)) (hne : Source.VH H V ≠ ⊥)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N → N = M)
    (hHM : ¬ H ≤ M) (hgenerate : L ⊔ T ≤ H ⊔ zpowers (g:G)) :
    Source.VH H V ⊓ (Source.VH H V).conjBy ((g:G)⁻¹) = U0 UH V2 := by
  obtain ⟨f,t,u₀,hf,hfimage,_,ht,_,hcyclic,_,_⟩ :=
    source_tensor_seeds_from_sections H UH V2 V3 V A π ρ σ μ d κ dU hκ hπK
      ι hι dV hAG hπI hVS h3U hgen hindex hpoint
  exact source_first_tensor_intersection L T H M UH V2 V3 V π ρ σ μ d f hfimage
    u₀ hcyclic t ht a ha hf b hb0 hb1 hker (fun k => congrArg Prod.snd (hπK k))
    g hg dU.kernel_le hgen h3V hseed ξ dx π₄ hact hfirst hactors hp hne hu hHM hgenerate

end CFSG.Quasithin.Chapter13.Section08.LinearFour
