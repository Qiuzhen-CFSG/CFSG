module
public import Theory.GroupTheory.PCoreSurjective.Supplement
public import Theory.GroupTheory.PResidual.SylowSupplement
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceNormalizerFactors

/-!
# The full marked normalizer product in 13.8.29

The normal S₃ image of I₂ splits off in G₂/O₂(G₂). Its centralizer has
trivial two-core. The original point normalizer maps onto that centralizer,
and K₂ maps onto the point normalizer's two-core quotient. Thus K₂ maps
onto the full complementary factor with kernel exactly O₂(K₂). This
identifies G₂/O₂(G₂) with PSL₃(2) × S₃, retaining both intrinsic quotient
maps. Sylow supplementation also proves G₂ = K₂ L₂,₊ T using the original
I₂ = O₂(H)L₂,₊ definition.

The original F.9 application supplies the shared Sylow subgroup and the
I₂-transitivity argument. The tensor-intersection application uses the
constructed product coordinates for the same source conjugator. The
natural marking remains an input, as do the tensor product and exterior
markings; this does not complete the linear-four exclusion.

Source: Aschbacher--Smith, The Classification of Quasithin Groups, combined
manuscript of 1 March 2004, 13.8.29(1--3), printed pp.963--964.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G : Type*} [Group G] [Finite G]

private theorem source_I2_complement_core (V2 : Subgroup G)
    (I : Subgroup (G2 V2)) [I.Normal] :
    pCore 2 (centralizer (I.map (QuotientGroup.mk' (pCore 2 (G2 V2))) :
      Set (G2 V2 ⧸ pCore 2 (G2 V2)))) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 (G2 V2))
  let J := I.map q
  let C := centralizer (J : Set (G2 V2 ⧸ pCore 2 (G2 V2)))
  let : J.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hh := (inferInstance : C.Normal).isSubnormal.pCore_subgroupOf 2
  rw [pCore_quotient_pCore_eq_bot,bot_subgroupOf] at hh
  exact hh.symm

open Representation BinaryLinear.OuterCyclic
open Theory.GroupTheory.NormalSymmetricThreeFactor

theorem source_K2_complement_map
    (H UH V1 V2 : Subgroup G) [IsMulCommutative UH]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (φ : H →* LinearGroup 4) (hφ : Function.Surjective φ)
    (hnatural : ∀ h x, ρ h x = φ h x) (hker : IsPGroup 2 φ.ker)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ UH)
    (v : Fin 4 → ZMod 2) (hv : v ≠ 0)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {v})
    (I : Subgroup (G2 V2)) [I.Normal]
    (hgen : I ⊔ H.subgroupOf (G2 V2) = ⊤)
    (π : G2 V2 →* centralizer (I.map (QuotientGroup.mk' (pCore 2 (G2 V2))) :
      Set (G2 V2 ⧸ pCore 2 (G2 V2))) × Equiv.Perm (Fin 3))
    (hπ : Function.Surjective π) (hπker : π.ker = pCore 2 (G2 V2))
    (hI : ∀ i : I, (π i).1 = 1) :
    let j := inclusion ((K2_le_localNormalizer H V2).trans inf_le_right)
    let f := (MonoidHom.fst _ _).comp (π.comp j)
    Function.Surjective f ∧ f.ker = pCore 2 (K2 H V2) ∧
      ∀ k : K2 H V2, (π (j k)).2 = 1 := by
  dsimp only
  let C := centralizer (I.map (QuotientGroup.mk' (pCore 2 (G2 V2))) :
      Set (G2 V2 ⧸ pCore 2 (G2 V2)))
  let f := (MonoidHom.fst C (Equiv.Perm (Fin 3))).comp π
  have hf : Function.Surjective f := fun c => by
    obtain ⟨x,hx⟩ := hπ (c,1)
    exact ⟨x,congrArg Prod.fst hx⟩
  have hfP := MonoidHom.surjective_on_supplement I (H.subgroupOf (G2 V2)) hgen f hf
    (fun i hi => hI ⟨i,hi⟩)
  let P := H ⊓ G2 V2
  let jP : P →* G2 V2 := inclusion inf_le_right
  have hP : Function.Surjective (f.comp jP) := by
    intro c
    obtain ⟨x,hx⟩ := hfP c
    exact ⟨⟨(x.val:G),x.property,x.val.property⟩,hx⟩
  obtain ⟨ψ,_,_,_,hψ,hK,_,_⟩ := source_point_quotient_marking
    H UH V1 V2 ρ d φ hφ hnatural hker h12 h2U v hv hpoint
  let jK := inclusion (K2_le_localNormalizer H V2)
  have hfK : Function.Surjective ((f.comp jP).comp jK) :=
    MonoidHom.surjective_comp_of_core_quotient (f.comp jP) hP
      (source_I2_complement_core V2 I) ψ hψ jK hK
  let : Group.IsPerfect (K2 H V2) := source_K2_isPerfect
    H UH V1 V2 ρ d φ hφ hnatural hker h12 h2U v hv hpoint
  let j := inclusion ((K2_le_localNormalizer H V2).trans inf_le_right)
  have hs (k : K2 H V2) : (π (j k)).2 = 1 := perfect_hom_eq_one
    ((MonoidHom.snd _ _).comp (π.comp j)) k
  have he : (f.comp j).ker = (π.comp j).ker := by
    ext k
    change (π (j k)).1 = 1 ↔ π (j k) = 1
    constructor
    · intro h
      exact Prod.ext h (hs k)
    · exact fun h => congrArg Prod.fst h
  have hp : IsPGroup 2 (f.comp j).ker := by
    rw [he,←MonoidHom.comap_ker,hπker]
    exact pCore_isPGroup.comap_of_injective j (inclusion_injective _)
  have hc := (f.comp j).comap_pCore_of_ker_isPGroup hfK hp
  rw [source_I2_complement_core V2 I,MonoidHom.comap_bot] at hc
  exact ⟨hfK,hc,hs⟩


/-- The two literal factor maps identify the whole normalizer quotient. -/
theorem source_normalizer_product_quotient
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
    ∃ (eK : (K2 H V2 ⧸ pCore 2 (K2 H V2)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
      (e : (G2 V2 ⧸ pCore 2 (G2 V2)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) × Equiv.Perm (Fin 3)),
      (∀ k : K2 H V2, e (QuotientGroup.mk' (pCore 2 (G2 V2))
        (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k)) =
        (eK (QuotientGroup.mk' (pCore 2 (K2 H V2)) k),1)) ∧
      ∀ i : I, e (QuotientGroup.mk' (pCore 2 (G2 V2)) i) =
        (1,eI (QuotientGroup.mk' (pCore 2 I) i)) := by
  obtain ⟨π,hπ,hπker,hI⟩ := source_I2_product_quotient V2 I eI
  obtain ⟨hf,hfker,hs⟩ := source_K2_complement_map
    H UH V1 V2 ρ d φ hφ hnatural hker h12 h2U v hv hpoint I hgen
    π hπ hπker (fun i => congrArg Prod.fst (hI i))
  obtain ⟨eK⟩ := source_K2_quotient_three
    H UH V1 V2 ρ d φ hφ hnatural hker h12 h2U v hv hpoint
  let j := inclusion ((K2_le_localNormalizer H V2).trans inf_le_right)
  let f := (MonoidHom.fst _ _).comp (π.comp j)
  let c := (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  let r := (c.symm.trans eK).prodCongr (MulEquiv.refl (Equiv.Perm (Fin 3)))
  let e := (QuotientGroup.quotientMulEquivOfEq hπker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective π hπ).trans r)
  refine ⟨eK,e,?_,?_⟩
  · intro k
    change (eK (c.symm (π (j k)).1),(π (j k)).2) = _
    apply Prod.ext
    · apply congrArg eK
      apply c.injective
      rw [c.apply_symm_apply]
      rfl
    · exact hs k
  · intro i
    change r (π i) = _
    rw [hI]
    change (eK (c.symm 1),eI (QuotientGroup.mk' (pCore 2 I) i)) = _
    rw [map_one,map_one]


/-- The original I₂ definition and Sylow subgroup give the literal generating factors. -/
theorem source_normalizer_generated_factors
    (H V2 L2plus : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) (hT2 : (T : Subgroup G) ≤ G2 V2)
    (I : Subgroup (G2 V2))
    (hgen : I ⊔ H.subgroupOf (G2 V2) = ⊤)
    (hI : I.map (G2 V2).subtype = H.pCoreIn 2 ⊔ L2plus) :
    G2 V2 = K2 H V2 ⊔ L2plus ⊔ (T : Subgroup G) := by
  have hTP : (T : Subgroup G) ≤ H ⊓ G2 V2 := le_inf hTH hT2
  have hs := congrArg (Subgroup.map (H ⊓ G2 V2).subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTP))
  have hP : K2 H V2 ⊔ (T : Subgroup G) = H ⊓ G2 V2 := by
    simpa only [K2,Subgroup.map_sup,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTP,←MonoidHom.range_eq_map,range_subtype] using hs
  have hg := congrArg (Subgroup.map (G2 V2).subtype) hgen
  rw [Subgroup.map_sup,subgroupOf_map_subtype,←MonoidHom.range_eq_map,range_subtype,
    hI,←hP] at hg
  have hc : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hTH)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] at hh
  apply le_antisymm
  · rw [←hg]
    exact sup_le (sup_le (hc.trans le_sup_right) (le_sup_right.trans le_sup_left))
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  · rw [←hg]
    exact sup_le (sup_le (le_sup_left.trans le_sup_right) (le_sup_right.trans le_sup_left))
      (le_sup_right.trans le_sup_right)


/-- Original point transitivity and Sylow placement discharge the generation
and two-core containment premises in the full marked normalizer calculation. -/
theorem source_normalizer_factors
    (F : ChapterF.Section09.Setup G) (hF : F.Hypothesis)
    [IsMulCommutative (Source.UH F.H F.Vplus)]
    (V2 L2plus : Subgroup G) (h12 : F.V₁ ≤ V2)
    (h2U : V2 ≤ Source.UH F.H F.Vplus)
    (hT2 : (F.T : Subgroup G) ≤ G2 V2)
    (hH : F.H = normalizer (F.V₁ : Set G))
    (ρ : Representation (ZMod 2) F.H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection F.H (Source.UH F.H F.Vplus) F.V₁ ρ)
    (φ : F.H →* LinearGroup 4) (hφ : Function.Surjective φ)
    (hnatural : ∀ h x, ρ h x = φ h x) (hker : IsPGroup 2 φ.ker)
    (v : Fin 4 → ZMod 2) (hv : v ≠ 0)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {v})
    (I : Subgroup (G2 V2)) [I.Normal]
    (eI : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3))
    (hI : I.map (G2 V2).subtype = F.H.pCoreIn 2 ⊔ L2plus)
    (ht : ∀ a b : V2, a ≠ 1 → b ≠ 1 →
      ∃ i : I, ((i : G2 V2) : G) * (a:G) * ((i : G2 V2) : G)⁻¹ = b) :
    ((K2 F.H V2).subgroupOf (G2 V2)).IsCComponent ∧
    G2 V2 = K2 F.H V2 ⊔ L2plus ⊔ (F.T : Subgroup G) ∧
    ∃ (eK : (K2 F.H V2 ⧸ pCore 2 (K2 F.H V2)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
      (e : (G2 V2 ⧸ pCore 2 (G2 V2)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) × Equiv.Perm (Fin 3)),
      (∀ k : K2 F.H V2, e (QuotientGroup.mk' (pCore 2 (G2 V2))
        (inclusion ((K2_le_localNormalizer F.H V2).trans inf_le_right) k)) =
        (eK (QuotientGroup.mk' (pCore 2 (K2 F.H V2)) k),1)) ∧
      ∀ i : I, e (QuotientGroup.mk' (pCore 2 (G2 V2)) i) =
        (1,eI (QuotientGroup.mk' (pCore 2 I) i)) := by
  have hgen := source_I2_point_supplement F.H F.V₁ V2 hH h12 hF.point_card I ht
  refine ⟨source_K2_component F hF V2 h12 h2U hT2 hH ρ d φ hφ hnatural
    hker v hv hpoint I eI ht,
    source_normalizer_generated_factors F.H V2 L2plus F.T hF.T_le_H hT2 I hgen hI,?_⟩
  exact source_normalizer_product_quotient F.H (Source.UH F.H F.Vplus) F.V₁ V2
    ρ d φ hφ hnatural hker h12 h2U v hv hpoint I eI hgen

end CFSG.Quasithin.Chapter13.Section08.LinearFour

open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open Representation BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]

/-- Apply the constructed PSL₃(2) × S₃ quotient to the literal tensor
intersection. Both factor embeddings and the source conjugator use the
original quotient map; the tensor product and exterior marking remain explicit. -/
theorem source_tensor_intersection_of_normalizer_factors
    (L T H M UH V1 V2 V3 V : Subgroup G) [IsMulCommutative UH]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π₄ : H →* SL(4,ZMod 2)) (hπ₄ : Function.Surjective π₄)
    (hnatural : ∀ h x, ρ h x = (π₄ h).val.mulVec x)
    (hkernel : IsPGroup 2 π₄.ker)
    (h12 : V1 ≤ V2) (h23 : V2 ≤ V3) (h3U : V3 ≤ UH) (hproper : ¬ V3 ≤ V2)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {Pi.single 0 1})
    (I : Subgroup (G2 V2)) [I.Normal]
    (eI : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3))
    (hIP : I ⊔ H.subgroupOf (G2 V2) = ⊤) (hcore : Q2 V2 ≤ H)
    (g : G2 V2) (hgI : g ∈ I)
    (hV3 : V3 ≤ V) (hseed : V3.conjBy ((g:G)⁻¹) ≤ V)
    (hproduct : U0 UH V2 = UH ⊔ UH.conjBy ((g:G)⁻¹))
    (ξ : Representation (ZMod 2) H BinaryParabolicExteriorSquare.PlaneSpan.Six)
    (dx : BinaryConjugationSection H (Source.VH H V) UH ξ)
    (hact : ∀ h x, ξ h x = exteriorMap (π₄ h).val x)
    (hfirst : dx.imageSpace (U0 UH V2) = BinaryParabolicExteriorSquare.PlaneSpan.firstSpace)
    (hp : IsPGroup 2 (Source.VH H V)) (hne : Source.VH H V ≠ ⊥)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N → N = M)
    (hHM : ¬ H ≤ M) (hgen : L ⊔ T ≤ H ⊔ zpowers (g:G)) :
    Source.VH H V ⊓ (Source.VH H V).conjBy ((g:G)⁻¹) = U0 UH V2 := by
  let φ := (slEquivLinear 4).toMonoidHom.comp π₄
  have hφ : Function.Surjective φ := (slEquivLinear 4).surjective.comp hπ₄
  have hnat : ∀ h x, ρ h x = φ h x := fun h x =>
    (hnatural h x).trans (slEquivLinear_apply 4 (π₄ h) x).symm
  have hφker : IsPGroup 2 φ.ker := by
    have he : φ.ker = π₄.ker := by
      ext h
      change slEquivLinear 4 (π₄ h) = 1 ↔ π₄ h = 1
      exact (slEquivLinear 4).map_eq_one_iff
    exact he.symm ▸ hkernel
  have hv : (Pi.single 0 1 : Fin 4 → ZMod 2) ≠ 0 := by
    intro he
    have hh := congrFun he 0
    simp at hh
  obtain ⟨eK,e,hK,hI⟩ := source_normalizer_product_quotient H UH V1 V2 ρ d φ hφ
    hnat hφker h12 (h23.trans h3U) (Pi.single 0 1) hv hpoint I eI hIP
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (G2 V2)))
  have hker : π.ker ≤ H.subgroupOf (G2 V2) := by
    dsimp only [π]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    intro x hx
    exact hcore (mem_map_of_mem (G2 V2).subtype hx)
  have hUH := source_K2_seed_span H UH V1 V2 V3 ρ d φ hφ hnat hφker
    h12 h23 h3U hproper (Pi.single 0 1) hv hpoint
  exact source_tensor_intersection_of_product L T H M UH V2 V3 V π hker
    (fun k => congrArg Prod.snd (hK k)) g (congrArg Prod.fst (hI ⟨g,hgI⟩))
    hUH hV3 hseed hproduct ξ dx π₄ hact hfirst
    (fun i j _ hj hij => source_K2_point_actors H UH V1 V2 ρ d π₄ hπ₄ hnatural
      h12 (h23.trans h3U) hpoint i j hj hij) hp hne hu hHM hgen

end CFSG.Quasithin.Chapter13.Section08.LinearFour
