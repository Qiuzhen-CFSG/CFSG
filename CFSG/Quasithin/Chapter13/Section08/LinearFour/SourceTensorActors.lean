module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.Constructions
public import Theory.Representation.BinaryConjugationSection.SubspacePreimages
public import Theory.SpecificGroups.BinaryLinear.PointStabilizerPerfect
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.PerfectLift

public import Theory.GroupTheory.PResidual.PerfectImage
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.TensorIntersection

/-!
# The actual point-normalizer residual in the linear-four branch

The natural action on U_H/V1 identifies N_H(V2)'s image with the full
point stabilizer. That binary four-space stabilizer is perfect, so the
actual K2 = O²(N_H(V2)) has the same image. The original two-group kernel
and two-perfectness then prove K2 is perfect. Its action on the soluble
second factor of the original product quotient is consequently trivial.
Every required point-parabolic transvection lifts to this same K2.

The first-tensor application uses those lifts to prove VH intersect VH^g
is U0. The final application supplies the intersection and the second-factor
identity to the original critical-pair obstruction. Its matrix action is
explicitly the same H/O2(H) marking as the natural section: surjectivity
and the two-group kernel are derived from that marking, not supplied anew.
All conjugations, quotient maps and relative normalizers are retained.

The initial product and tensor markings, exterior marking, and the marked
point V2/V1 remain explicit, as do the three-chief-factor lower bound and
earlier endpoint premises. The remaining 13.8.29–32 construction, including
the extra-trivial-line second-tensor row and critical geometry, belongs to
qt-d-138-linear-four-source. The earlier 13.8.27 setup belongs to
qt-d-138-six-g2-source, and qt-d-1381-source owns its final discharge.
These conditional applications do not complete 13.8.28.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, combined
manuscript of 1 March 2004, 13.8.29(1)–(3) and 13.8.31(1), printed pp.964–965.
-/

public section
open Subgroup Representation
open BinaryLinear BinaryLinear.OuterCyclic Theory.LinearAlgebra
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G : Type*} [Group G]

/-- The local normalizer is exactly the point stabilizer under the literal
natural action, with the full central kernel retained. -/
theorem source_local_normalizer_image
    (H UH V1 V2 : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (φ : H →* LinearGroup 4) (hφ : Function.Surjective φ)
    (hnatural : ∀ h x, ρ h x = φ h x)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ UH)
    (v : Fin 4 → ZMod 2) (hv : v ≠ 0)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {v}) :
    (φ.comp (inclusion (inf_le_left : H ⊓ G2 V2 ≤ H))).range =
      BinaryFivePointStabilizer.stabilizer v := by
  have hn (h : H) : (h:G) ∈ G2 V2 ↔ φ h v = v := by
    have he := d.subspacePreimage_imageSpace V2 h2U h12
    rw [hpoint] at he
    change (h:G) ∈ normalizer (V2:Set G) ↔ _
    rw [←he,d.mem_normalizer_subspacePreimage_iff]
    constructor
    · intro hs
      have hm : φ h v ∈ Submodule.span (ZMod 2) {v} := by
        rw [←hs,←hnatural]
        exact ⟨v,Submodule.mem_span_singleton_self v,rfl⟩
      obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hm
      have ha0 : a ≠ 0 := by
        intro hz
        apply hv
        exact (φ h).map_eq_zero_iff.mp (by simpa only [hz,zero_smul] using ha.symm)
      have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
      simpa only [ha1,one_smul] using ha.symm
    · intro hh
      rw [Submodule.map_span,Set.image_singleton,hnatural,hh]
  ext a
  constructor
  · rintro ⟨h,rfl⟩
    exact (hn ⟨h, h.property.1⟩).mp h.property.2
  · intro ha
    obtain ⟨h,rfl⟩ := hφ a
    exact ⟨⟨h,h.property,(hn h).mpr ha⟩,rfl⟩

/-- The actual two-residual K2 still maps onto the whole point parabolic. -/
theorem source_K2_image [Finite G]
    (H UH V1 V2 : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (φ : H →* LinearGroup 4) (hφ : Function.Surjective φ)
    (hnatural : ∀ h x, ρ h x = φ h x)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ UH)
    (v : Fin 4 → ZMod 2) (hv : v ≠ 0)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {v}) :
    (φ.comp (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left))).range =
      BinaryFivePointStabilizer.stabilizer v := by
  let f := φ.comp (inclusion (inf_le_left : H ⊓ G2 V2 ≤ H))
  have he : f.range = BinaryFivePointStabilizer.stabilizer v :=
    source_local_normalizer_image H UH V1 V2 ρ d φ hφ hnatural h12 h2U v hv hpoint
  let : Group.IsPerfect f.range := he.symm ▸ PointStabilizerPerfect.isPerfect (by simp) hv
  have hm := (map_pResidual_eq_range_of_isPerfect 2 f).trans he
  rw [←hm]
  ext x
  constructor
  · rintro ⟨k,rfl⟩
    obtain ⟨a,ha,hak⟩ := k.property
    refine ⟨a,ha,?_⟩
    change φ _ = φ _
    apply congrArg φ
    exact Subtype.ext hak
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨a,mem_map_of_mem (H ⊓ G2 V2).subtype ha⟩,rfl⟩
/-- The actual K2 is perfect: it is two-perfect by construction, its natural
image is the full perfect point stabilizer, and its kernel is a two-group. -/
theorem source_K2_isPerfect [Finite G]
    (H UH V1 V2 : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (φ : H →* LinearGroup 4) (hφ : Function.Surjective φ)
    (hnatural : ∀ h x, ρ h x = φ h x) (hker : IsPGroup 2 φ.ker)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ UH)
    (v : Fin 4 → ZMod 2) (hv : v ≠ 0)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {v}) :
    Group.IsPerfect (K2 H V2) := by
  let f := φ.comp (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left))
  have he : f.range = BinaryFivePointStabilizer.stabilizer v :=
    source_K2_image H UH V1 V2 ρ d φ hφ hnatural h12 h2U v hv hpoint
  let : Group.IsPerfect f.range := he.symm ▸ PointStabilizerPerfect.isPerfect (by simp) hv
  have hp : IsPPerfect 2 (K2 H V2) := by
    let e := (pResidual 2 (↥(H ⊓ G2 V2))).equivMapOfInjective
      (H ⊓ G2 V2).subtype (H ⊓ G2 V2).subtype_injective
    exact (isPPerfect_pResidual 2).of_surjective e.toMonoidHom e.surjective
  apply hp.isPerfect_of_surjective_pGroup_kernel f.rangeRestrict f.rangeRestrict_surjective
  rw [MonoidHom.ker_rangeRestrict]
  change IsPGroup 2 (φ.comp (inclusion _)).ker
  rw [← MonoidHom.comap_ker]
  exact hker.comap_of_injective _ (inclusion_injective _)

/-- A soluble second factor of the original product quotient kills K2.
In source 13.8.29 this factor is the actual symmetric group on three letters. -/
theorem source_K2_second_factor_eq_one [Finite G]
    (H UH V1 V2 : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (φ : H →* LinearGroup 4) (hφ : Function.Surjective φ)
    (hnatural : ∀ h x, ρ h x = φ h x) (hker : IsPGroup 2 φ.ker)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ UH)
    (v : Fin 4 → ZMod 2) (hv : v ≠ 0)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {v})
    {K I : Type*} [Group K] [Group I] [Group.IsSolvable I]
    (π : G2 V2 →* K × I) (k : K2 H V2) :
    (π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k)).2 = 1 := by
  let : Group.IsPerfect (K2 H V2) :=
    source_K2_isPerfect H UH V1 V2 ρ d φ hφ hnatural hker h12 h2U v hv hpoint
  let f := (MonoidHom.snd K I).comp
    (π.comp (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right)))
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  exact congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict k) 1)

/-- The point-parabolic transvections needed by the exterior quotient lift
into the actual K2, using the same natural matrix marking. -/
theorem source_K2_point_actors [Finite G]
    (H UH V1 V2 : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hπ : Function.Surjective π)
    (hnatural : ∀ h x, ρ h x = (π h).val.mulVec x)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ UH)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {Pi.single 0 1})
    (i j : Fin 4) (hj : j ≠ 0) (hij : i ≠ j) :
    ∃ k : K2 H V2,
      (π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k)).val =
        Matrix.transvection i j 1 := by
  let φ := (slEquivLinear 4).toMonoidHom.comp π
  have hv : (Pi.single 0 1 : Fin 4 → ZMod 2) ≠ 0 := by
    intro he
    have hh := congrFun he 0
    simp at hh
  have he := source_K2_image H UH V1 V2 ρ d φ ((slEquivLinear 4).surjective.comp hπ)
    (fun h x => (hnatural h x).trans (slEquivLinear_apply 4 (π h) x).symm)
    h12 h2U (Pi.single 0 1) hv hpoint
  let a : SL(4,ZMod 2) := Matrix.SpecialLinearGroup.transvection hij 1
  have ha : slEquivLinear 4 a ∈ BinaryFivePointStabilizer.stabilizer (Pi.single 0 1) := by
    change slEquivLinear 4 a (Pi.single 0 1) = Pi.single 0 1
    rw [slEquivLinear_apply]
    simp [a, Matrix.SpecialLinearGroup.transvection_coe, -Matrix.mulVec_single,
      Matrix.add_mulVec, Matrix.single_mulVec_eq, hj]
  rw [←he] at ha
  obtain ⟨k,hk⟩ := ha
  have hk' : π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k) = a :=
    (slEquivLinear 4).injective hk
  exact ⟨k,congrArg Subtype.val hk'⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour

open Atlas.Order20160A8.Bivectors (exteriorMap)
open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G K I U W : Type*} [Group G] [Group K] [Group I] [Group.IsSolvable I]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]

/-- The natural marking constructs the residual actors and removes the
second-factor assumption in the exact first-tensor intersection. -/
theorem source_first_tensor_intersection_of_natural_action [Finite G]
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
    (g : G2 V2) (hg : π g⁻¹ = (1,a)) (hV2U : V2 ≤ UH)
    (hUH : UH = conjugateSpanBy V3 (K2 H V2))
    (hV3 : V3 ≤ V) (hseed : V3.conjBy ((g:G)⁻¹) ≤ V)
    (ξ : Representation (ZMod 2) H BinaryParabolicExteriorSquare.PlaneSpan.Six)
    (dx : BinaryConjugationSection H (Source.VH H V) UH ξ)
    (π₄ : H →* SL(4,ZMod 2)) (hπ₄ : Function.Surjective π₄)
    (V1 : Subgroup G) (h12 : V1 ≤ V2)
    (ρ₄ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d₄ : BinaryConjugationSection H UH V1 ρ₄)
    (hnatural : ∀ h x, ρ₄ h x = (π₄ h).val.mulVec x)
    (hkernel : IsPGroup 2 π₄.ker)
    (hpoint : d₄.imageSpace V2 = Submodule.span (ZMod 2) {Pi.single 0 1})
    (hact : ∀ h x, ξ h x = exteriorMap (π₄ h).val x)
    (hfirst : dx.imageSpace (U0 UH V2) = BinaryParabolicExteriorSquare.PlaneSpan.firstSpace)
    (hp : IsPGroup 2 (Source.VH H V)) (hne : Source.VH H V ≠ ⊥)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N → N = M)
    (hHM : ¬ H ≤ M) (hgen : L ⊔ T ≤ H ⊔ zpowers (g:G)) :
    Source.VH H V ⊓ (Source.VH H V).conjBy ((g:G)⁻¹) = U0 UH V2 := by
  let φ := (slEquivLinear 4).toMonoidHom.comp π₄
  have hφ : Function.Surjective φ := (slEquivLinear 4).surjective.comp hπ₄
  have hnat : ∀ h x, ρ₄ h x = φ h x := fun h x =>
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
  have hK := source_K2_second_factor_eq_one H UH V1 V2 ρ₄ d₄ φ hφ hnat hφker
    h12 hV2U (Pi.single 0 1) hv hpoint π
  have hactors := fun (i j : Fin 4) (_ : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) =>
    source_K2_point_actors H UH V1 V2 ρ₄ d₄ π₄ hπ₄ hnatural h12 hV2U hpoint i j hj hij
  exact source_first_tensor_intersection L T H M UH V2 V3 V π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 hker hK g hg hV2U hUH hV3 hseed
    ξ dx π₄ hact hfirst hactors hp hne hu hHM hgen

end CFSG.Quasithin.Chapter13.Section08.LinearFour

public section
open Subgroup Representation
open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open CriticalGeometry NoncentralChiefRefinement BinaryLinear.OuterCyclic
variable {G K I U W : Type*} [Group G] [Group K] [Group I] [Group.IsSolvable I]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The same natural and exterior marking supplies the actual K2 actors
and kills its soluble second factor before applying the critical-pair obstruction.
The earlier endpoint premises and three-factor bound remain explicit. -/
theorem source_critical_line_not_le_of_natural_tensor_geometry [Finite G]
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
    (g : G2 V2) (hg : π g⁻¹ = (1,a)) (hgH : (g:G) ∉ H)
    (hUH : Source.UH H V3 = conjugateSpanBy V3 (K2 H V2))
    (hV3 : V3 ≤ V) (hLV : L ≤ normalizer (V:Set G)) (hgL : (g:G) ∈ L)
    (ξ : Representation (ZMod 2) H BinaryParabolicExteriorSquare.PlaneSpan.Six)
    (dx : BinaryConjugationSection H (Source.VH H V) (Source.UH H V3) ξ)
    (π₄ : H →* SL(4,ZMod 2))
    (hcompatible : ∀ h, slEquivLinear 4 (π₄ h) = e (QuotientGroup.mk' (pCore 2 H) h))
    (hpoint : d₄.imageSpace V2 = Submodule.span (ZMod 2) {Pi.single 0 1})
    (hact : ∀ h x, ξ h x = exteriorMap (π₄ h).val x)
    (hfirst : dx.imageSpace (U0 (Source.UH H V3) V2) =
      BinaryParabolicExteriorSquare.PlaneSpan.firstSpace)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N → N = M)
    (hHM : ¬ H ≤ M) (hgen : L ⊔ T ≤ H ⊔ zpowers (g:G))
    (hDK : D ≤ Kc) (Vn Cn : NormalNode D)
    (hVn : Vn.val = (Source.VH H V).subgroupOf D)
    (hCn : Cn.val = (Source.HC H V3).subgroupOf D)
    (hthree : ∀ s : ChiefSeries D, s.head = Vn → s.last = Cn →
      3 ≤ s.noncentralTwoCount) :
    ¬ c.Aone V1 ≤ Source.UH H V3 := by
  have hπ₄ : Function.Surjective π₄ := by
    intro a
    obtain ⟨h,hh⟩ := QuotientGroup.mk'_surjective (pCore 2 H)
      (e.symm (slEquivLinear 4 a))
    refine ⟨h,(slEquivLinear 4).injective ?_⟩
    rw [hcompatible,hh,e.apply_symm_apply]
  have hnat : ∀ h x, ρ₄ h x = (π₄ h).val.mulVec x := by
    intro h x
    rw [hnatural,←hcompatible,slEquivLinear_apply]
  have hkernel : IsPGroup 2 π₄.ker := by
    have he : π₄.ker = pCore 2 H := by
      ext h
      change π₄ h = 1 ↔ h ∈ pCore 2 H
      rw [←(slEquivLinear 4).map_eq_one_iff,hcompatible,e.map_eq_one_iff,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [he]
    exact pCore_isPGroup
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
  have hintersection := source_first_tensor_intersection_of_natural_action L T H M (Source.UH H V3)
    V2 V3 V π ρ σ μ d f himage u₀ hcyclic t ht a ha hf b hb0 hb1
    hker g hg h2U hUH hV3 hseed ξ dx π₄ hπ₄ V1 h12 ρ₄ d₄ hnat hkernel hpoint hact hfirst
    (IsElementaryAbelian.isPGroup 2 (Source.VH H V)) hne hu hHM hgen
  have htensor := source_tensor_dimension (Source.UH H V3) V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 hdim
  exact source_critical_line_not_le_of_marked_sections L T H Kc D V V1 V2 V3 c
    ρ₄ d₄ e hnatural hH hV1 hV2 hcomm hseedQ hKcH hKc h12 h2U hdisj hγH hγQ
    g hgH hintersection (ρ.comp π) d htensor ξ dx (by simp [BinaryParabolicExteriorSquare.PlaneSpan.Six])
    hDK Vn Cn hVn hCn hthree

end CFSG.Quasithin.Chapter13.Section08.LinearFour
