module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.OuterSpan.Data
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.Outer
public import Theory.Mathieu.M22.ChapterHLocalClassification.Sylow.Candidates
public import Theory.Representation.BinaryOffender.FixedSpaceSpan

/-!
# Native M22 cocode fixed spans from small certificates

Every elementary sixteen-subgroup of the marked outer Sylow is contained in
the source quintet, or is one of eight explicitly covered sets. In each of
the latter cases nine independent quotient vectors lie in the span of the
fixed spaces of its nonidentity elements. Sylow membership, commutation,
vector fixation and independence are all interpreted in the original native
action. No new group model or altered pair-line quotient is used.

Source: Aschbacher--Smith H.15.5 and 8.1.3, printed pp.400--401,713--714,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender Matrix
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion.SylowCoverage
open MathieuCode.QuadraticActors MathieuCode.CocodeOctad.Involutions
open scoped IsMulCommutative
namespace MathieuCode.NormalizedShadowRows.OuterSpan

/-- The two-vertex certificate covers each actual sixteen-element commuting set. -/
theorem clique_cases (s : Finset (Fin 72)) (hs : s.card = 16)
    (hc : ∀ a ∈ s, ∀ b ∈ s, adjacent a b = true) :
    s ⊆ quintet ∨ ∃ k, s = caseSet k := by
  by_cases hq : s ⊆ quintet
  · exact Or.inl hq
  · obtain ⟨a,has,ha⟩ := Finset.not_subset.mp hq
    have hn : ¬ s ⊆ badSet a := by
      intro hb
      have he := Finset.card_le_card hb
      have hh := bad_card a ha
      omega
    obtain ⟨b,hbs,hb⟩ := Finset.not_subset.mp hn
    refine Or.inr ⟨caseChoice a b,?_⟩
    apply Finset.eq_of_subset_of_card_le
    · intro c hcs
      exact coverage a b ha (hc a has b hbs) hb c (hc a has c hcs) (hc b hbs c hcs)
    · rw [case_card,hs]

private theorem quintet_check : ∀ v : Fin 72, v ∈ quintet →
    ∃ t : Fin 64, ∀ x : Fin 24,
      M22ChapterH.CompatibleSylow.point (M22ChapterH.CompatibleSylow.coreIndex t) x =
        outerPoint v x := by decide +kernel

private theorem identity_check : ∀ v : Fin 72,
    (∀ x : Fin 24, outerPoint v x = x) → v = 0 := by decide +kernel

private theorem native_ne_one (v : Fin 72) (hv : v ≠ 0) : outerNative v ≠ 1 := by
  intro he
  apply hv
  apply identity_check v
  intro x
  rw [←outerNative_apply,he]
  rfl

/-- The large mask belongs to the original, source-marked sextet core. -/
theorem quintet_native (v : Fin 72) (hv : v ∈ quintet) :
    outerNative v ∈ M22ChapterH.Sextet.sourceCore := by
  obtain ⟨t,ht⟩ := quintet_check v hv
  apply (M22ChapterH.CompatibleSylow.mem_sourceCore _).mpr
  refine ⟨t,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro x
  rw [M22ChapterH.CompatibleSylow.row_apply,outerNative_apply]
  exact ht x

/-- Native group commutation has exactly the checked adjacency convention. -/
theorem native_adjacent {a b : m22PairStabilizer} (v w : Fin 72)
    (hv : outerNative v = a.val) (hw : outerNative w = b.val)
    (h : Commute a b) : adjacent v w = true := by
  apply native_compatible
  apply Subtype.ext
  apply (MulAut.conj M22ChapterH.CompatibleSylow.transport).injective
  simp only [Subgroup.coe_mul,map_mul]
  change outerNative v * outerNative w = outerNative w * outerNative v
  rw [hv,hw]
  exact congrArg Subtype.val h.eq

/-- Coordinates on the quotient by the same marked pair line. -/
def quotientCoordinates : M22Cocode →ₗ[ZMod 2] Coordinates :=
  m22PairLine.liftQ
    (coordinates - (LinearMap.proj 0 ∘ₗ coordinates).smulRight pairCoordinate) (by
      intro x hx
      apply LinearMap.mem_ker.mpr
      ext i
      exact pair_line_coordinate x hx i)

private theorem quotientCoordinates_vector (k : Fin 8) (j : Fin 9) :
    quotientCoordinates (m22PairLine.mkQ (sectionMap (vector k j))) = vector k j := by
  have he := LinearMap.congr_fun coordinates_sectionMap (vector k j)
  change coordinates (sectionMap (vector k j)) = vector k j at he
  ext i
  change coordinates (sectionMap (vector k j)) i -
    coordinates (sectionMap (vector k j)) 0 * pairCoordinate i = vector k j i
  rw [he,vector_zero,zero_mul,sub_zero]

private theorem vector_fixed (k : Fin 8) (j : Fin 9)
    (a : m22PairStabilizer) (ha : outerNative (actor k j) = a.val) :
    m22OuterCocodeRepresentation a (m22PairLine.mkQ (sectionMap (vector k j))) =
      m22PairLine.mkQ (sectionMap (vector k j)) := by
  rw [m22OuterCocodeRepresentation_mk,←sub_eq_zero,←map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  let d := cocodeRepresentation a.val (sectionMap (vector k j)) - sectionMap (vector k j)
  have he : outerMatrix (actor k j) *ᵥ vector k j = coordinates d := by
    rw [←displacementMatrix_outerNative,ha]
    exact LinearMap.congr_fun (displacementMatrix_eq a.val) (vector k j)
  have hd : d = coordinates d 0 • m22PairClass := by
    apply coordinateEquiv.injective
    change coordinates d = coordinates (coordinates d 0 • m22PairClass)
    rw [map_smul,pair_coordinates]
    ext i
    exact he ▸ fixed_vector k j i
  change d ∈ m22PairLine
  rw [hd]
  exact m22PairLine.smul_mem _ (Submodule.subset_span (Set.mem_singleton _))

/-- Each listed sixteen-set has fixed-space span of codimension at most one
on the actual cocode quotient. No exhaustiveness or fixed-span input is assumed. -/
theorem case_fixedSpan_codim (A : Subgroup m22PairStabilizer) (k : Fin 8)
    (hA : ∀ v ∈ caseSet k, ∃ a ∈ A, outerNative v = (a : M24)) :
    Module.finrank (ZMod 2) (M22Cocode ⧸ fixedSpaceSpan m22OuterCocodeRepresentation A) ≤ 1 := by
  let S := fixedSpaceSpan m22OuterCocodeRepresentation A
  have hcol : Submodule.span (ZMod 2) (Set.range (columns k).col) ≤
      S.map quotientCoordinates := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    obtain ⟨a,ha,hav⟩ := hA (actor k j) (actor_mem k j).1
    have ha1 : a ≠ 1 := by
      intro he
      apply native_ne_one (actor k j) (actor_mem k j).2
      simpa only [he,Subgroup.coe_one] using hav
    refine ⟨m22PairLine.mkQ (sectionMap (vector k j)),?_,?_⟩
    · exact fixedSpace_le_fixedSpaceSpan _ ha ha1
        ((mem_fixedSpace_zpowers_iff _ _ _).mpr (vector_fixed k j a hav))
    · exact quotientCoordinates_vector k j
  have hl : 9 ≤ (columns k).rank := by
    have hh := Matrix.rank_mul_le_right (leftInverse k) (columns k)
    simpa only [independent_vectors,Matrix.rank_one,Fintype.card_fin] using hh
  have hu := Submodule.finrank_mono hcol
  rw [←Matrix.rank_eq_finrank_span_cols] at hu
  have hm := Submodule.finrank_map_le quotientCoordinates S
  have hd := S.finrank_quotient_add_finrank
  rw [finrank_m22Cocode] at hd
  change Module.finrank (ZMod 2) (M22Cocode ⧸ S) ≤ 1
  exact Nat.le_of_add_le_add_right (show Module.finrank (ZMod 2) (M22Cocode ⧸ S) + 9 ≤ 1 + 9 by
    have hS : 9 ≤ Module.finrank (ZMod 2) S := hl.trans (hu.trans hm)
    omega)

/-- Every native rank-four elementary group is in the quintet, or satisfies
the required cocode span bound directly from the checked eight cases. -/
theorem sylow_rank_four_cases (A : Subgroup m22PairStabilizer)
    [IsElementaryAbelian 2 A] (hc : Nat.card A = 16)
    (hS : A ≤ M22ChapterH.CompatibleSylow.outerGroup) :
    A ≤ M22ChapterH.Sextet.outerTranslations ∨
      Module.finrank (ZMod 2) (M22Cocode ⧸ fixedSpaceSpan m22OuterCocodeRepresentation A) ≤ 1 := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have hex (a : A) : ∃ v : Fin 72, outerNative v = a.val.val :=
    outer_vertex_of_square a.val (hS a.property)
      (elemPow_eq_one_of_isElementaryAbelian a.val a.property)
  choose f hf using hex
  have hi : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Subtype.ext ((hf a).symm.trans ((congrArg outerNative hab).trans (hf b))))
  let s : Finset (Fin 72) := Finset.univ.image f
  have hsc : s.card = 16 := by
    simpa only [s,Finset.card_image_of_injective _ hi,Finset.card_univ,←Nat.card_eq_fintype_card] using hc
  have hcomm : ∀ a ∈ s, ∀ b ∈ s, adjacent a b = true := by
    intro v hv w hw
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hw
    exact native_adjacent (f a) (f b) (hf a) (hf b)
      (congrArg Subtype.val (mul_comm a b))
  rcases clique_cases s hsc hcomm with hq | ⟨k,hk⟩
  · refine Or.inl ?_
    intro a ha
    have hh := quintet_native (f ⟨a,ha⟩) (hq (Finset.mem_image.mpr ⟨⟨a,ha⟩,Finset.mem_univ _,rfl⟩))
    rwa [hf] at hh
  · apply Or.inr
    apply case_fixedSpan_codim A k
    intro v hv
    rw [←hk] at hv
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨a.val,a.property,hf a⟩
end MathieuCode.NormalizedShadowRows.OuterSpan
