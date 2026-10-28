module
public import Theory.GroupTheory.NormalSymmetricThreeFactor
public import Theory.GroupTheory.TransitiveInvolutionNormalizer
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourcePointQuotient

/-!
# The actual normalizer factors in 13.8.29

The original normal I₂ with quotient S₃ centralizes the perfect K₂ image
modulo O₂(G₂). Normality of K₂ lifts through the two-core, and its already
constructed PSL₃(2) quotient makes it a C-component of the full G₂.
I₂-transitivity on V₂ minus the identity supplies G₂ = I₂ N_H(V₂);
the shared Sylow subgroup supplies the required two-core containment.

The actual two-core quotient splits off the marked S₃ factor, retaining
its map from I₂. This puts the source conjugator in that factor and K₂ in
the complementary factor. The literal tensor-intersection application
uses these constructed coordinates, the natural K₂ seed span and the
lifted exterior actors. It assumes no product quotient or factor-placement
callback. The complementary centralizer factor still needs its identification
with K₂/O₂(K₂) to complete the whole product assertion of 13.8.29(2).

The original 13.5.4 I₂ normality, symmetric quotient and transitivity, and
four-dimensional natural marking remain inputs from the earlier source
setup. The compatible tensor/exterior markings, seed-normalizer control,
extra-line movement and nine-factor/13.8.31 obstruction remain obligations
of this linear-four task. These results do not complete 13.8.28.

Source: Aschbacher--Smith, The Classification of Quasithin Groups, combined
manuscript of 1 March 2004, 13.8.29(1--3), printed pp.963--964.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open Representation BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]
/-- The original K₂ is normal in G₂: its perfect image centralizes the
normal S₃ image of I₂, and normality lifts through the actual two-core. -/
theorem source_K2_normal_of_symmetric_supplement
    (H UH V1 V2 : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (φ : H →* LinearGroup 4) (hφ : Function.Surjective φ)
    (hnatural : ∀ h x, ρ h x = φ h x) (hker : IsPGroup 2 φ.ker)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ UH)
    (v : Fin 4 → ZMod 2) (hv : v ≠ 0)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {v})
    (I : Subgroup (G2 V2)) [I.Normal]
    (eI : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3))
    (hgen : I ⊔ H.subgroupOf (G2 V2) = ⊤) (hcore : Q2 V2 ≤ H) :
    ((K2 H V2).subgroupOf (G2 V2)).Normal := by
  let R := (K2 H V2).subgroupOf (G2 V2)
  have hKG := (K2_le_localNormalizer H V2).trans inf_le_right
  let er := subgroupOfEquivOfLe hKG
  let : Group.IsPerfect (K2 H V2) := source_K2_isPerfect
    H UH V1 V2 ρ d φ hφ hnatural hker h12 h2U v hv hpoint
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := er.symm.toMonoidHom) er.symm.surjective
  have hp : IsPPerfect 2 R := (isPPerfect_embedded_pResidual 2 (H ⊓ G2 V2)).of_surjective
    er.symm.toMonoidHom er.symm.surjective
  have hn : H ⊓ G2 V2 ≤ normalizer (K2 H V2 : Set G) :=
    (H ⊓ G2 V2).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pResidual 2 (H ⊓ G2 V2 : Subgroup G)))
  apply Theory.GroupTheory.NormalSymmetricThreeFactor.normal_of_symmetric_supplement
    I (H.subgroupOf (G2 V2)) R eI hgen ?_ ?_ hp
  · rw [←subgroupOf_normalizer_eq hKG]
    intro x hx
    exact hn ⟨hx,x.property⟩
  · intro x hx
    exact hcore (mem_map_of_mem (G2 V2).subtype hx)

/-- The intrinsic PSL₃(2) quotient and the proved relative normality make
the literal K₂ a C-component of the full G₂. -/
theorem source_K2_component_of_symmetric_supplement
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
    (hgen : I ⊔ H.subgroupOf (G2 V2) = ⊤) (hcore : Q2 V2 ≤ H) :
    ((K2 H V2).subgroupOf (G2 V2)).IsCComponent := by
  let R := (K2 H V2).subgroupOf (G2 V2)
  have hKG := (K2_le_localNormalizer H V2).trans inf_le_right
  let er := subgroupOfEquivOfLe hKG
  let : R.Normal := source_K2_normal_of_symmetric_supplement
    H UH V1 V2 ρ d φ hφ hnatural hker h12 h2U v hv hpoint I eI hgen hcore
  have hp : IsPPerfect 2 R := (isPPerfect_embedded_pResidual 2 (H ⊓ G2 V2)).of_surjective
    er.symm.toMonoidHom er.symm.surjective
  obtain ⟨eK⟩ := source_K2_quotient_three H UH V1 V2 ρ d φ hφ hnatural hker h12 h2U v hv hpoint
  let eR := (QuotientGroup.congr (pCore 2 R) (pCore 2 (K2 H V2)) er
    (pCore_map_iso 2 er)).trans eK
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup (R ⧸ pCore 2 R) := eR.isSimpleGroup
  let : Group.IsPerfect (K2 H V2) := source_K2_isPerfect
    H UH V1 V2 ρ d φ hφ hnatural hker h12 h2U v hv hpoint
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := er.symm.toMonoidHom) er.symm.surjective
  let : Group.IsPerfect (R ⧸ pCore 2 R) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hz : center (R ⧸ pCore 2 R) = ⊥ := by
    rcases (inferInstance : (center (R ⧸ pCore 2 R)).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative (R ⧸ pCore 2 R)
        (center_eq_top_iff.mp hz)).elim
  let : Theory.GroupTheory.IsQuasisimple (R ⧸ pCore 2 R) :=
    { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    (inferInstance : R.Normal).isSubnormal hp

end CFSG.Quasithin.Chapter13.Section08.LinearFour

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open Representation BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Transitivity on the original nonidentity points gives G₂ = I₂ N_H(V₂),
with H equal to the original point normalizer. -/
theorem source_I2_point_supplement
    (H V1 V2 : Subgroup G) (hH : H = normalizer (V1:Set G))
    (h12 : V1 ≤ V2) (hV1 : Nat.card V1 = 2) (I : Subgroup (G2 V2))
    (ht : ∀ a b : V2, a ≠ 1 → b ≠ 1 →
      ∃ i : I, ((i : G2 V2) : G) * (a:G) * ((i : G2 V2) : G)⁻¹ = b) :
    I ⊔ H.subgroupOf (G2 V2) = ⊤ := by
  have hg := normalizer_eq_sup_point_normalizer_of_transitive
    V2 (I.map (G2 V2).subtype) V1 (map_subtype_le _) h12 hV1
    (fun a b ha hb => by
      obtain ⟨i,hi⟩ := ht a b ha hb
      exact ⟨i,mem_map_of_mem _ i.property,hi⟩)
  apply map_injective (G2 V2).subtype_injective
  rw [Subgroup.map_sup,subgroupOf_map_subtype,←MonoidHom.range_eq_map,range_subtype]
  rw [hH]
  exact hg.symm

/-- Original F.9 Sylow placement and I₂ transitivity discharge the core
and generation premises in the full-G₂ component assertion of 13.8.29(1). -/
theorem source_K2_component
    (F : ChapterF.Section09.Setup G) (hF : F.Hypothesis)
    [IsMulCommutative (Source.UH F.H F.Vplus)]
    (V2 : Subgroup G) (h12 : F.V₁ ≤ V2) (h2U : V2 ≤ Source.UH F.H F.Vplus)
    (hT2 : (F.T:Subgroup G) ≤ G2 V2)
    (hH : F.H = normalizer (F.V₁:Set G))
    (ρ : Representation (ZMod 2) F.H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection F.H (Source.UH F.H F.Vplus) F.V₁ ρ)
    (φ : F.H →* LinearGroup 4) (hφ : Function.Surjective φ)
    (hnatural : ∀ h x, ρ h x = φ h x) (hker : IsPGroup 2 φ.ker)
    (v : Fin 4 → ZMod 2) (hv : v ≠ 0)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {v})
    (I : Subgroup (G2 V2)) [I.Normal]
    (eI : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3))
    (ht : ∀ a b : V2, a ≠ 1 → b ≠ 1 →
      ∃ i : I, ((i : G2 V2) : G) * (a:G) * ((i : G2 V2) : G)⁻¹ = b) :
    ((K2 F.H V2).subgroupOf (G2 V2)).IsCComponent := by
  have hcore : Q2 V2 ≤ F.H := by
    have hh := pCoreIn_le_sylow (G2 V2) (F.T.subtype hT2)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hT2] at hh
    exact hh.trans hF.T_le_H
  exact source_K2_component_of_symmetric_supplement F.H (Source.UH F.H F.Vplus)
    F.V₁ V2 ρ d φ hφ hnatural hker h12 h2U v hv hpoint I eI
    (source_I2_point_supplement F.H F.V₁ V2 hH h12 hF.point_card I ht) hcore

end CFSG.Quasithin.Chapter13.Section08.LinearFour

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G : Type*} [Group G] [Finite G]

/-- The actual quotient by O₂(G₂) splits into the centralizer of the I₂
image and its marked S₃ factor, with the original intrinsic quotient map. -/
theorem source_I2_product_quotient (V2 : Subgroup G)
    (I : Subgroup (G2 V2)) [I.Normal]
    (eI : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) :
    let q := QuotientGroup.mk' (pCore 2 (G2 V2))
    let C := centralizer (I.map q : Set (G2 V2 ⧸ pCore 2 (G2 V2)))
    ∃ π : G2 V2 →* C × Equiv.Perm (Fin 3),
      Function.Surjective π ∧ π.ker = pCore 2 (G2 V2) ∧
      ∀ i : I, π i = (1,eI (QuotientGroup.mk' (pCore 2 I) i)) := by
  dsimp only
  obtain ⟨e,he⟩ := Theory.GroupTheory.NormalSymmetricThreeFactor.exists_core_product I eI
  let π := e.symm.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (G2 V2)))
  refine ⟨π,e.symm.surjective.comp (QuotientGroup.mk'_surjective _),?_,?_⟩
  · dsimp only [π]
    rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective,QuotientGroup.ker_mk']
  · intro i
    exact (congrArg e.symm (he i)).symm.trans (e.symm_apply_apply _)

end CFSG.Quasithin.Chapter13.Section08.LinearFour

open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open Representation BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]

/-- The normal I₂ quotient supplies the commuting factors for the literal
tensor intersection. No product quotient or coordinate placement for the
retained conjugator is assumed; the natural action also constructs the K₂
seed span and exterior actors. The tensor product and exterior marking remain explicit. -/
theorem source_tensor_intersection_of_normal_symmetric_factor
    (L T H M UH V1 V2 V3 V : Subgroup G) [IsMulCommutative UH]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π₄ : H →* SL(4,ZMod 2)) (hπ₄ : Function.Surjective π₄)
    (hnatural : ∀ h x, ρ h x = (π₄ h).val.mulVec x)
    (hkernel : IsPGroup 2 π₄.ker)
    (h12 : V1 ≤ V2) (h23 : V2 ≤ V3) (h3U : V3 ≤ UH) (hproper : ¬ V3 ≤ V2)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {Pi.single 0 1})
    (I : Subgroup (G2 V2)) [I.Normal]
    (eI : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) (hcore : Q2 V2 ≤ H)
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
  let : Group.IsPerfect (K2 H V2) := source_K2_isPerfect
    H UH V1 V2 ρ d φ hφ hnat hφker h12 (h23.trans h3U) (Pi.single 0 1) hv hpoint
  obtain ⟨π,hπ,hker,hI⟩ := source_I2_product_quotient V2 I eI
  have hK (k : K2 H V2) :
      (π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k)).2 = 1 :=
    Theory.GroupTheory.NormalSymmetricThreeFactor.perfect_hom_eq_one
      ((MonoidHom.snd _ _).comp (π.comp
        (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right)))) k
  have hUH := source_K2_seed_span H UH V1 V2 V3 ρ d φ hφ hnat hφker
    h12 h23 h3U hproper (Pi.single 0 1) hv hpoint
  apply source_tensor_intersection_of_product L T H M UH V2 V3 V π ?_ hK g
    (congrArg Prod.fst (hI ⟨g,hgI⟩)) hUH hV3 hseed hproduct ξ dx π₄ hact hfirst
    (fun i j _ hj hij => source_K2_point_actors H UH V1 V2 ρ d π₄ hπ₄ hnatural
      h12 (h23.trans h3U) hpoint i j hj hij) hp hne hu hHM hgen
  rw [hker]
  intro x hx
  exact hcore (mem_map_of_mem (G2 V2).subtype hx)

end CFSG.Quasithin.Chapter13.Section08.LinearFour
