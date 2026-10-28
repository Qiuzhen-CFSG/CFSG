module
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceTensorSeed
public import Theory.GroupTheory.QuotientConjugatePlacement
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.Representation.BinaryParabolicExteriorSquare.PointQuotient

/-!
# The exact tensor intersection in original 13.8.29(3)

The first tensor supplies U0 = UH UH^g. Commutation of the two quotient
factors, with the literal kernel inside H, puts the conjugate K2 seed span
inside VH and makes K2 normalize VH^g. Hence U0 lies in both groups.
In the exterior six-space, the point-parabolic transvections act irreducibly
modulo the marked three-space U0/UH. Therefore the intersection is U0 or VH.
The second alternative would put both H and LT in the normalizer of the
nontrivial two-group VH, contradicting the earlier unique maximal two-local
M and H not contained in M. All conjugates use the same original g.

The first tensor's compatible seed embeddings, the original quotient-factor
marking, the exterior marking and its parabolic actors still have to be
constructed by qt-d-138-linear-four-source. The earlier generation and
uniqueness setup is retained explicitly; qt-d-138-six-g2-source supplies
13.8.27 and qt-d-1381-source owns its final discharge. This conditional
intersection is not the full 13.8.29 or 13.8.28.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, combined
manuscript (1 March 2004), 13.8.29(3),(5), printed p.964. Source right
conjugation by g is expressed by Subgroup.conjBy g⁻¹.
-/

public section
open Subgroup Representation
open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G K I : Type*} [Group G] [Group K] [Group I]

/-- The commuting quotient factors put the original conjugate seed span inside VH
and make K2 normalize the same conjugate of VH. -/
theorem source_tensor_span_and_normalization
    (H UH V2 V3 V : Subgroup G) (π : G2 V2 →* K × I)
    (hker : π.ker ≤ H.subgroupOf (G2 V2))
    (hK : ∀ k : K2 H V2,
      (π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k)).2 = 1)
    (g : G2 V2) (hg : (π g).1 = 1)
    (hUH : UH = conjugateSpanBy V3 (K2 H V2))
    (hV3 : V3 ≤ V) (hseed : V3.conjBy ((g:G)⁻¹) ≤ V)
    (hproduct : U0 UH V2 = UH ⊔ UH.conjBy ((g:G)⁻¹)) :
    U0 UH V2 ≤ Source.VH H V ∧
      K2 H V2 ≤ normalizer ((Source.VH H V).conjBy ((g:G)⁻¹) : Set G) := by
  have hKH : K2 H V2 ≤ H := (K2_le_localNormalizer H V2).trans inf_le_left
  have hKP : K2 H V2 ≤ G2 V2 := (K2_le_localNormalizer H V2).trans inf_le_right
  have hc (k : K2 H V2) : Commute (π g) (π (inclusion hKP k)) := by
    change π g * π (inclusion hKP k) = π (inclusion hKP k) * π g
    apply Prod.ext
    · simp only [Prod.fst_mul,hg,one_mul,mul_one]
    · simp only [Prod.snd_mul,hK k,one_mul,mul_one]
  have hcInv (k : K2 H V2) : Commute (π g⁻¹) (π (inclusion hKP k)) := by
    simpa only [map_inv] using (hc k).inv_left
  have hHn : H ≤ normalizer (Source.VH H V : Set G) := le_normalizer_conjugateSpanBy V H
  have hKn := conjBy_le_of_commute_image (G2 V2) H (K2 H V2) hKP hKH π hker g⁻¹ hcInv
  have hU : UH ≤ Source.VH H V := by
    rw [hUH]
    exact conjugateSpanBy_mono hV3 hKH
  have hUg : UH.conjBy ((g:G)⁻¹) ≤ Source.VH H V := by
    change UH.map (MulAut.conj ((g:G)⁻¹)).toMonoidHom ≤ _
    rw [hUH,map_conjugateSpanBy]
    exact conjugateSpanBy_le (hseed.trans (le_conjugateSpanBy V H)) (hKn.trans hHn)
  exact ⟨hproduct ▸ sup_le hU hUg,
    le_normalizer_conjBy_inv_of_commute_image (G2 V2) H (K2 H V2)
      (Source.VH H V) hKP hKH hHn π hker g hc⟩

/-- Earlier uniqueness rules out equality of VH with its specified conjugate. -/
theorem source_conjugate_not_contains [Finite G]
    (L T H M VH : Subgroup G) (hH : H ≤ normalizer (VH:Set G))
    (hp : IsPGroup 2 VH) (hne : VH ≠ ⊥)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N → N = M)
    (hHM : ¬ H ≤ M) (g : G) (hgen : L ⊔ T ≤ H ⊔ zpowers g) :
    ¬ VH ≤ VH.conjBy g⁻¹ := by
  intro hh
  have he : VH = VH.conjBy g⁻¹ := eq_of_le_of_card_ge hh (by
    change Nat.card (VH.map _) ≤ Nat.card VH
    rw [card_map_of_injective (MulAut.conj _).injective])
  have hg : g⁻¹ ∈ normalizer (VH:Set G) := mem_normalizer_iff_map_conj_eq.mpr he.symm
  have hgn : zpowers g ≤ normalizer (VH:Set G) :=
    zpowers_le.mpr ((normalizer (VH:Set G)).inv_mem_iff.mp hg)
  exact hHM (hH.trans (normalizer_le_of_unique_maximalTwoLocal hu hp hne
    (hgen.trans (sup_le hH hgn))))

/-- The exterior point-parabolic calculation proves the exact intersection.
The quotient VH/U0 is not supplied as a new irreducible section. -/
theorem source_tensor_intersection_of_product [Finite G]
    (L T H M UH V2 V3 V : Subgroup G) (π : G2 V2 →* K × I)
    (hker : π.ker ≤ H.subgroupOf (G2 V2))
    (hK : ∀ k : K2 H V2,
      (π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k)).2 = 1)
    (g : G2 V2) (hg : (π g).1 = 1)
    (hUH : UH = conjugateSpanBy V3 (K2 H V2))
    (hV3 : V3 ≤ V) (hseed : V3.conjBy ((g:G)⁻¹) ≤ V)
    (hproduct : U0 UH V2 = UH ⊔ UH.conjBy ((g:G)⁻¹))
    (ξ : Representation (ZMod 2) H BinaryParabolicExteriorSquare.PlaneSpan.Six)
    (d : BinaryConjugationSection H (Source.VH H V) UH ξ)
    (π₄ : H →* SL(4,ZMod 2))
    (hact : ∀ h x, ξ h x = exteriorMap (π₄ h).val x)
    (hfirst : d.imageSpace (U0 UH V2) = BinaryParabolicExteriorSquare.PlaneSpan.firstSpace)
    (hactors : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j →
      ∃ k : K2 H V2,
        (π₄ (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k)).val =
          Matrix.transvection i j 1)
    (hp : IsPGroup 2 (Source.VH H V)) (hne : Source.VH H V ≠ ⊥)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N → N = M)
    (hHM : ¬ H ≤ M) (hgen : L ⊔ T ≤ H ⊔ zpowers (g:G)) :
    Source.VH H V ⊓ (Source.VH H V).conjBy ((g:G)⁻¹) = U0 UH V2 := by
  obtain ⟨hUV,hKn⟩ := source_tensor_span_and_normalization H UH V2 V3 V π
    hker hK g hg hUH hV3 hseed hproduct
  let B := (Source.VH H V).conjBy ((g:G)⁻¹)
  have hUB : U0 UH V2 ≤ B := by
    have he := mem_normalizer_iff_map_conj_eq.mp (G2_normalizes_U0 UH V2 g⁻¹.property)
    exact he.symm.le.trans (map_mono hUV)
  have hnot : ¬ Source.VH H V ≤ B := source_conjugate_not_contains L T H M
    (Source.VH H V) (le_normalizer_conjugateSpanBy V H) hp hne hu hHM g hgen
  have hs := BinaryParabolicExteriorSquare.PointQuotient.invariant_above_first
    (d.imageSpace B) (hfirst ▸ d.imageSpace_mono hUB) (by
      intro i j hi hj hij x hx
      obtain ⟨k,hk⟩ := hactors i j hi hj hij
      have hh := d.imageSpace_apply_mem B
        (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k) (hKn k.property) x hx
      rwa [hact,hk] at hh)
  have himage : d.imageSpace B = d.imageSpace (U0 UH V2) := by
    rcases hs with hs | hs
    · exact hs.trans hfirst.symm
    · exact (hnot ((d.le_sup_kernel_of_image_top B hs).trans
        (sup_le le_rfl ((UH_le_U0 UH V2).trans hUB)))).elim
  apply le_antisymm ?_ (le_inf hUV hUB)
  intro x hx
  apply (d.coordinates_mem_imageSpace_iff_of_kernel_le (U0 UH V2)
    (UH_le_U0 UH V2) ⟨x,hx.1⟩).mp
  rw [←himage]
  exact (d.mem_imageSpace_iff B _).mpr ⟨⟨x,hx.1⟩,hx.2,rfl⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour

open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G K I U W : Type*} [Group G] [Group K] [Group I]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]

/-- The constructed first tensor and exterior marking give the source intersection,
retaining the same seed embeddings, quotient map and specified conjugator. -/
theorem source_first_tensor_intersection [Finite G]
    (L T H M UH V2 V3 V : Subgroup G) (π : G2 V2 →* K × I)
    (ρ : Representation (ZMod 2) (K × I) W)
    (σ : Representation (ZMod 2) K U) (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
    (d : BinaryConjugationSection (G2 V2) (U0 UH V2) V2 (ρ.comp π))
    (f : σ.IntertwiningMap (ρ.comp (MonoidHom.inl K I)))
    (himage : f.range.toSubmodule = d.imageSpace UH)
    (u₀ : U) (hcyclic : Submodule.span (ZMod 2) (Set.range fun k => σ k u₀) = ⊤)
    (t : μ.IntertwiningMap (ρ.comp (MonoidHom.inr K I)))
    (ht : t first = f u₀) (a : I) (ha : μ a first = second)
    (hf : Function.Injective f) (b : I)
    (hb0 : μ b first = first) (hb1 : μ b second = first + second)
    (hker : π.ker ≤ H.subgroupOf (G2 V2))
    (hK : ∀ k : K2 H V2,
      (π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k)).2 = 1)
    (g : G2 V2) (hg : π g⁻¹ = (1,a)) (hV2U : V2 ≤ UH)
    (hUH : UH = conjugateSpanBy V3 (K2 H V2))
    (hV3 : V3 ≤ V) (hseed : V3.conjBy ((g:G)⁻¹) ≤ V)
    (ξ : Representation (ZMod 2) H BinaryParabolicExteriorSquare.PlaneSpan.Six)
    (dx : BinaryConjugationSection H (Source.VH H V) UH ξ)
    (π₄ : H →* SL(4,ZMod 2))
    (hact : ∀ h x, ξ h x = exteriorMap (π₄ h).val x)
    (hfirst : dx.imageSpace (U0 UH V2) = BinaryParabolicExteriorSquare.PlaneSpan.firstSpace)
    (hactors : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j →
      ∃ k : K2 H V2,
        (π₄ (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k)).val =
          Matrix.transvection i j 1)
    (hp : IsPGroup 2 (Source.VH H V)) (hne : Source.VH H V ≠ ⊥)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N → N = M)
    (hHM : ¬ H ≤ M) (hgen : L ⊔ T ≤ H ⊔ zpowers (g:G)) :
    Source.VH H V ⊓ (Source.VH H V).conjBy ((g:G)⁻¹) = U0 UH V2 := by
  have hsum := (source_tensor_two_conjugates UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 g hg hV2U).1
  have hg1 : (π g).1 = 1 := by
    have hh := congrArg Prod.fst hg
    simpa only [map_inv,Prod.fst_inv,inv_eq_one] using hh
  exact source_tensor_intersection_of_product L T H M UH V2 V3 V π hker hK g hg1
    hUH hV3 hseed hsum ξ dx π₄ hact hfirst hactors hp hne hu hHM hgen

end CFSG.Quasithin.Chapter13.Section08.LinearFour
