module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceTensorIntersection
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.PointObstruction

/-!
# Applying the exact tensor intersection to the critical pair

The first tensor's seed coordinates and the exterior point-parabolic action
construct VH intersect VH^g = U0 through SourceTensorIntersection. The same
markings compute the index eight. These derived conclusions feed the actual
point-normalizer obstruction for the original CriticalPair and original g.
The seed-conjugate placement follows from g in L and L normalizing V.
No intersection equality or separate quotient irreducibility is assumed.

The initial tensor and orthogonal markings, parabolic actor lifts and
three-chief-factor lower bound remain internal obligations of
qt-d-138-linear-four-source. The endpoint placement and nontrivial image
belong to the earlier 13.8.27 setup, owned by qt-d-138-six-g2-source; final
assembly and discharge of earlier inputs belong to qt-d-1381-source.
This conditional application does not complete 13.8.31 or 13.8.28.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, combined
manuscript (1 March 2004), 13.8.29(3) and 13.8.31(1), printed pp.964–965.
-/

public section
open Subgroup Representation
open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open CriticalGeometry NoncentralChiefRefinement BinaryLinear.OuterCyclic
variable {G K I U W : Type*} [Group G] [Group K] [Group I]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The first tensor and the exterior point-parabolic geometry discharge the
exact intersection in the critical-pair obstruction, with the original g.
The earlier endpoint premises and the three-factor lower bound remain explicit. -/
theorem source_critical_line_not_le_of_tensor_geometry [Finite G]
    (L T H M Kc D V V1 V2 V3 : Subgroup G) (c : CriticalPair L T H V)
    [IsElementaryAbelian 2 (Source.VH H V)]
    (ρ₄ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d₄ : BinaryConjugationSection H (Source.UH H V3) V1 ρ₄)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hnatural : ∀ h w, ρ₄ h w = e (QuotientGroup.mk' (pCore 2 H) h) w)
    (hH : H = normalizer (V1 : Set G))
    (hV1 : Nat.card V1 = 2) (hV2 : Nat.card V2 = 4)
    (hcomm : ⁅Source.UH H V3,H.pCoreIn 2⁆ ≤ V1)
    (hseedQ : ⁅V3,H.pCoreIn 2⁆ ≠ ⊥)
    (hKcH : Kc ≤ H) (hKc : IsPPerfect 2 Kc)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ Source.UH H V3)
    (hdisj : V1 ⊓ c.Aone V1 = ⊥)
    (hγH : c.Vgamma ≤ H) (hγQ : ¬ c.Vgamma ≤ H.pCoreIn 2)
    (π : G2 V2 →* K × I)
    (ρ : Representation (ZMod 2) (K × I) W)
    (σ : Representation (ZMod 2) K U) (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
    (d : BinaryConjugationSection (G2 V2) (U0 (Source.UH H V3) V2) V2 (ρ.comp π))
    (f : σ.IntertwiningMap (ρ.comp (MonoidHom.inl K I)))
    (himage : f.range.toSubmodule = d.imageSpace (Source.UH H V3))
    (u₀ : U) (hcyclic : Submodule.span (ZMod 2) (Set.range fun k => σ k u₀) = ⊤)
    (t : μ.IntertwiningMap (ρ.comp (MonoidHom.inr K I)))
    (ht : t first = f u₀) (a : I) (ha : μ a first = second)
    (hf : Function.Injective f) (b : I)
    (hb0 : μ b first = first) (hb1 : μ b second = first + second)
    (hdim : Module.finrank (ZMod 2) U = 3)
    (hker : π.ker ≤ H.subgroupOf (G2 V2))
    (hK2 : ∀ k : K2 H V2,
      (π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k)).2 = 1)
    (g : G2 V2) (hg : π g⁻¹ = (1,a)) (hgH : (g:G) ∉ H)
    (hUH : Source.UH H V3 = conjugateSpanBy V3 (K2 H V2))
    (hV3 : V3 ≤ V) (hLV : L ≤ normalizer (V:Set G)) (hgL : (g:G) ∈ L)
    (ξ : Representation (ZMod 2) H BinaryParabolicExteriorSquare.PlaneSpan.Six)
    (dx : BinaryConjugationSection H (Source.VH H V) (Source.UH H V3) ξ)
    (π₄ : H →* SL(4,ZMod 2))
    (hact : ∀ h x, ξ h x = exteriorMap (π₄ h).val x)
    (hfirst : dx.imageSpace (U0 (Source.UH H V3) V2) =
      BinaryParabolicExteriorSquare.PlaneSpan.firstSpace)
    (hactors : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j →
      ∃ k : K2 H V2,
        (π₄ (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k)).val =
          Matrix.transvection i j 1)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N → N = M)
    (hHM : ¬ H ≤ M) (hgen : L ⊔ T ≤ H ⊔ zpowers (g:G))
    (hDK : D ≤ Kc) (Vn Cn : NormalNode D)
    (hVn : Vn.val = (Source.VH H V).subgroupOf D)
    (hCn : Cn.val = (Source.HC H V3).subgroupOf D)
    (hthree : ∀ s : ChiefSeries D, s.head = Vn → s.last = Cn →
      3 ≤ s.noncentralTwoCount) :
    ¬ c.Aone V1 ≤ Source.UH H V3 := by
  let : Finite W := Finite.of_surjective (fun x => (d.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp d.onto)
  have hne : Source.VH H V ≠ ⊥ := by
    intro he
    have hz : V1 = ⊥ := bot_unique ((d₄.kernel_le.trans dx.kernel_le).trans_eq he)
    rw [hz] at hV1
    simp at hV1
  have hseed : V3.conjBy ((g:G)⁻¹) ≤ V := by
    have he : V.conjBy ((g:G)⁻¹) = V :=
      mem_normalizer_iff_map_conj_eq.mp (hLV (L.inv_mem hgL))
    exact (map_mono hV3).trans_eq he
  have hintersection := source_first_tensor_intersection L T H M (Source.UH H V3)
    V2 V3 V π ρ σ μ d f himage u₀ hcyclic t ht a ha hf b hb0 hb1
    hker hK2 g hg h2U hUH hV3 hseed ξ dx π₄ hact hfirst hactors
    (IsElementaryAbelian.isPGroup 2 (Source.VH H V)) hne hu hHM hgen
  have htensor := source_tensor_dimension (Source.UH H V3) V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 hdim
  exact source_critical_line_not_le_of_marked_sections L T H Kc D V V1 V2 V3 c
    ρ₄ d₄ e hnatural hH hV1 hV2 hcomm hseedQ hKcH hKc h12 h2U hdisj hγH hγQ
    g hgH hintersection (ρ.comp π) d htensor ξ dx (by simp [BinaryParabolicExteriorSquare.PlaneSpan.Six])
    hDK Vn Cn hVn hCn hthree

end CFSG.Quasithin.Chapter13.Section08.LinearFour
