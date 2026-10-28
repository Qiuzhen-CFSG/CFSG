module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.MarkedEmbedding
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.CoefficientOpposition
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.CoefficientAlignment
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceGeometry

/-!
# The original E.2.7 marked pair from coefficient-copy recognition

The original minimal-parabolic geometry puts V in the component's Sylow
center and supplies a nonroot central element. Recognizing the SAME literal
opposite pair as a conjugate of Sp4(K) then aligns that copy by a Borel
element. Its original Sylow and maximal intersections are precisely the
coefficient unipotent and Borel groups. The self-normalizer of the copy
makes opposition internal. Trivial Borel core and original centrality give
the exact MarkedModel required by the E.2.13 consumer.

The sole independent recognition input is the displayed coefficient-copy
equality. No root element in V, Sylow/Borel marking, core, center or witness
callback remains. Proper coefficient subfields and K of order two are allowed.

Source: Aschbacher--Smith E.2.7--9 and E.2.13, printed pp.219--225.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate DiagramAutomorphisms
open DiagramAutomorphisms.FieldFixedResidual
open ChapterB EvenBorelTorus
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

omit [Finite G] in
private theorem pair_image {D : Type*} [Group D] (f : D →* G) (W : Subgroup D) (g : D) :
    (W ⊔ W.map (MulAut.conj g).toMonoidHom).map f =
      W.map f ⊔ (W.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_sup,map_map,map_map]
  congr 2
  ext x
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]

/-- Recognizing the SAME opposite pair over a possibly proper coefficient
field constructs every E.2.7 mark for the original module. -/
theorem source_coefficient_copy_markedModel {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hJ : minimalParabolicCore T hP = ⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F ≃* L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom) = unipotent)
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVM : V ≤ (minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G) ≤ normalizer (V : Set G)) (hr : 2 < Nat.card V)
    (K : Subfield F) (c : Sp F)
    (hcopy : oppositePair (V.comap (L.subtype.comp e.toMonoidHom)) =
      (coefficientInclusion K).range.map (MulAut.conj c).toMonoidHom) :
    Nonempty (MarkedModel T (minimalParabolicMax T hP) V) := by
  let f := L.subtype.comp e.toMonoidHom
  let W := V.comap f
  let M := minimalParabolicMax T hP
  have hf : Function.Injective f := L.subtype_injective.comp e.injective
  obtain ⟨_,hmap,hcenter,_,_⟩ := Structure.SymplecticFour.source_geometry
    hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr
  have hB : M.comap f = Theory.SpecificGroups.SymplecticFour.borel :=
    Structure.SymplecticFour.source_borel_intersection hF hn T hP L e hmark hgen
  obtain ⟨t,ht⟩ := Structure.SymplecticFour.exists_moving_sylow_actor
    hF hn T hP L e hmark hgen
  let a : ActorReduction.stabilizer (F := F) :=
    ⟨extensionAction L e t,Structure.SymplecticFour.sylow_actor T L e hmark t⟩
  have hWa : W.map a.val.toMonoidHom = W := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      change f (a.val x) ∈ V
      rw [show f (a.val x) = t.val*f x*t.val⁻¹ from extensionAction_apply L e t x]
      exact (mem_normalizer_iff.mp (hVN t.property) (f x)).mp hx
    · rw [card_map_of_injective a.val.injective]
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  have hne : W ≠ ⊥ := by
    intro he
    have hc : Nat.card W = Nat.card V := by rw [←hmap,card_map_of_injective hf]
    rw [he] at hc
    simp at hc
    omega
  obtain ⟨hl,hs⟩ := not_root_axes_of_moving_actor hq a ht W hWa hne
  obtain ⟨s,t,hs0,ht0,hst⟩ := exists_upper_nonzero_parameters W
    (CentralRootGeometry.parameter_range (F := F) ▸ hcenter) hl hs
  have hz : upper s t ∈ (coefficientInclusion K).range.map (MulAut.conj c).toMonoidHom :=
    hcopy ▸ (show upper s t ∈ oppositePair W from (show W ≤ oppositePair W from le_sup_left) hst)
  obtain ⟨d,hd,hdcopy⟩ := exists_borel_coefficient_alignment K c s t hs0 ht0 hz
  let j := (MulAut.conj d).toMonoidHom.comp (coefficientInclusion K)
  have hj : Function.Injective j := (MulAut.conj d).injective.comp (coefficientInclusion_injective K)
  have hrange : j.range = oppositePair W := by
    rw [MonoidHom.range_comp]
    exact (hcopy.trans hdcopy).symm
  have hUj : unipotent.comap j = unipotent (F := K) :=
    coefficient_conj_comap_unipotent K d hd
  have hBj : Theory.SpecificGroups.SymplecticFour.borel.comap j = Theory.SpecificGroups.SymplecticFour.borel (F := K) := coefficient_conj_comap_borel K d hd
  have hopp : opposition ∈ j.range := hrange.symm ▸ opposition_mem_of_coefficient_copy W K c hcopy
  obtain ⟨g,hg⟩ := hopp
  have hTj : (T : Subgroup G).comap (f.comp j) = unipotent := by
    rw [←comap_comap,hmark,hUj]
  have hMj : M.comap (f.comp j) = Theory.SpecificGroups.SymplecticFour.borel := by rw [←comap_comap,hB,hBj]
  have hpair : V ⊔ V.map (MulAut.conj ((f.comp j) g)).toMonoidHom = (f.comp j).range := by
    rw [MonoidHom.comp_apply,hg,MonoidHom.range_comp,hrange]
    rw [oppositePair,pair_image,hmap]
  apply markedModel_of_embedding T M V hVT (f.comp j) (hf.comp hj) hTj hMj g hpair
  intro v hv x hx
  obtain ⟨w,hw,rfl⟩ := hmap.symm ▸ hv
  obtain ⟨u,hu⟩ := hx.2
  have huU : j u ∈ unipotent (F := F) := by
    rw [←hmark]
    change f (j u) ∈ (T : Subgroup G)
    change f (j u) = x at hu
    rw [hu]
    exact hx.1
  obtain ⟨wU,hwZ,hwU⟩ := hcenter hw
  change (wU : Sp F) = w at hwU
  have hcomm : j u * w = w * j u := by
    have hh := congrArg (fun y : unipotent (F := F) => (y : Sp F))
      (mem_center_iff.mp hwZ ⟨j u,huU⟩)
    simpa only [Subgroup.coe_mul,hwU] using hh
  rw [←hu]
  change f w * f (j u) = f (j u) * f w
  rw [←map_mul,←map_mul,hcomm]

/-- Literal E.2.7 recognized-pair output; its only additional premise is the
independently produced coefficient-copy equality on the original pair. -/
theorem source_hasRecognizedPair_of_coefficient_copy {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hJ : minimalParabolicCore T hP = ⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F ≃* L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom) = unipotent)
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVM : V ≤ (minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G) ≤ normalizer (V : Set G)) (hr : 2 < Nat.card V)
    (K : Subfield F) (c : Sp F)
    (hcopy : oppositePair (V.comap (L.subtype.comp e.toMonoidHom)) =
      (coefficientInclusion K).range.map (MulAut.conj c).toMonoidHom) :
    HasRecognizedPair T (minimalParabolicMax T hP) V := by
  obtain ⟨w⟩ := source_coefficient_copy_markedModel hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr K c hcopy
  exact HasRecognizedPair.of_markedModel w

end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
