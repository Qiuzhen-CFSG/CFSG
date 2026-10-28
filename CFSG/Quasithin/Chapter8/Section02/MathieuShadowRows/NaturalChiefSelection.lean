module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.NaturalChiefCoordinates
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.NaturalChiefMovement

/-!
# The two-versus-three cubic contradiction on the original chief factors

The common chief-image equivalence carries the constructed Cartan component
and each original element to its literal action on a chief factor. The same
sharp actor distinguishes small natural rows from the linear rows. A cubic
moving at least three dimensions on an induced seed section forces a chief
factor of dimension at least five; the single natural row has dimension at
most four and the paired row moves at most two on the original fixed space.

The final theorem eliminates the larger natural alternative from the actual
cubic count and two-factor filtration. Its inputs are constructed in the
Chapter12 application M22CodeSmallNatural; no matching-coordinate premise
remains.
Source: Aschbacher--Smith, proof of 3.1.9(6), printed p.578,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter3 ChapterB QuasisimpleSource SourceInduction

universe u

private theorem chief_fixed_movement_le_two
    {D W : Type u} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    (hD : IsSQTK KnownSimple.IsKnownSimple D)
    (S : Sylow 2 D) (hp : IsMinimalParabolicOver S ⊤)
    (A J : Subgroup D)
    (hA : IsOffender (imageRepresentation ρ) (actionSubgroup ρ A))
    (hsharp : rank (actionSubgroup ρ A) = fixedCodim (imageRepresentation ρ) (actionSubgroup ρ A))
    (hsmall : ¬ ChiefSmallNaturalAlternatives (imageRepresentation ρ))
    (hJ : (S : Subgroup D) ≤ normalizer (J : Set D)) (hAJ : A ≤ J)
    (hdim : 5 ≤ Module.finrank (ZMod 2) W)
    (C : Subgroup (actionImage ρ)) (hC : IsComponent (actionImage ρ) C)
    (F : BinaryField) (hfour : Nat.card F.Carrier = 4) (eC : C ≃* SL(2,F.Carrier))
    (b : D) (hb : actionHom ρ b ∈ C) :
    Module.finrank (ZMod 2) (LinearMap.range
      ((ρ b - LinearMap.id).domRestrict (fixedSpace ρ J))) ≤ 2 := by
  let σ := imageRepresentation ρ
  let q := actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  have hc := irreducible_image_twoCore_eq_bot ρ
  have hff : IsFFModule σ := ⟨_,hA⟩
  have hn : q.ker ≠ ⊤ := by
    intro he
    have hz : actionSubgroup ρ A = ⊥ := by
      apply bot_unique
      rintro x ⟨y,hy,rfl⟩
      exact (show y ∈ q.ker from he ▸ mem_top y)
    exact hA.1.1 hz
  have hp' := (minimalParabolic_reduced_image S hp q hq hc hn).2
  have hJ' : ((S.mapSurjective hq : Sylow 2 (actionImage ρ)) : Subgroup _) ≤
      normalizer (actionSubgroup ρ J : Set (actionImage ρ)) := by
    rintro x ⟨y,hy,rfl⟩
    exact J.le_normalizer_map q (mem_map_of_mem q (hJ hy))
  have hbest := minimalParabolic_sharp_image_isBestOffender ρ hD S hp hA hsharp
  have hu := non_small_natural_fixed_movement_le_two σ (imageRepresentation_injective ρ)
    (imageRepresentation_irreducible ρ inferInstance) (S.mapSurjective hq) hp' hff hc
    (minimalParabolic_chief_natural_alternatives ρ hD S hp hff).1
    hsmall hdim hC F hfour eC (actionSubgroup ρ J) hJ'
    (actionSubgroup ρ A) hbest (Subgroup.map_mono hAJ) (q b) hb
  rw [fixedSpace_actionSubgroup] at hu
  exact hu

section Original
open ChapterD NoncentralChiefRefinement
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {H V M : Subgroup G}
  [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
  {S : Sylow 2 H} {hVH : V ≤ H}

set_option backward.isDefEq.respectTransparency false in
/-- Matching the component and the fixed actor bounds the literal original chief movement. -/
theorem original_chief_cartan_movement_le_two
    (a : EssentialSeedAction H V S hVH) {A : Subgroup H} (ha : EssentialChiefActor a A)
    (hD : IsSQTK KnownSimple.IsKnownSimple H)
    (hsmall : ¬ ChiefSmallNaturalAlternatives a.imageRepresentation)
    (c : SeedCartan (M := M) a.projection a.imageRepresentation a.vector)
    (hfour : Nat.card c.field.Carrier = 4)
    (J : Subgroup H) (hJ : (S : Subgroup H) ≤ normalizer (J : Set H)) (hAJ : A ≤ J)
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H)) (i : Fin s.series.length)
    (hi : ¬ s.Central i) (hdim : 5 ≤ Module.finrank (ZMod 2) (Additive (s.Factor i)))
    (b : c.originalPreimage) :
    Module.finrank (ZMod 2) (LinearMap.range
      ((s.factorRepresentation i (b : H) - LinearMap.id).domRestrict
        (fixedSpace (s.factorRepresentation i) J))) ≤ 2 := by
  let ρ := s.factorRepresentation i
  let := s.factorRepresentation_irreducible i
  obtain ⟨e⟩ := (ha.chief s i hi).2
  let C := c.component.map e.equiv.toMonoidHom
  have hC := c.component_isComponent.map_equiv e.equiv
  let eC : C ≃* SL(2,c.field.Carrier) :=
    (e.equiv.subgroupMap c.component).symm.trans c.component_equiv
  have hb : actionHom ρ (b : H) ∈ C := by
    rw [← e.map_action (b : H)]
    exact mem_map_of_mem _ (c.in_component b.property.2)
  exact chief_fixed_movement_le_two ρ hD S a.original_minimal A J
    (ha.chief s i hi).1 (ha.chief_sharp s i hi)
    (fun hs => hsmall ((ha.small_iff s i hi).mpr hs)) hJ hAJ hdim
    C hC c.field hfour eC b hb

set_option backward.isDefEq.respectTransparency false in
/-- The three-factor cubic count excludes every larger natural source row. -/
theorem essential_small_of_cubic_chiefs [IsElementaryAbelian 2 V]
    (a : EssentialSeedAction H V S hVH) {A : Subgroup H} (ha : EssentialChiefActor a A)
    (hD : IsSQTK KnownSimple.IsKnownSimple H)
    (J : Subgroup H) (hJ : (S : Subgroup H) ≤ normalizer (J : Set H)) (hAJ : A ≤ J)
    (hJC : J.map H.subtype ≤ centralizer (V : Set G))
    (c : SeedCartan (M := M) a.projection a.imageRepresentation a.vector)
    (hfour : Nat.card c.field.Carrier = 4)
    (hcub : CubicOrbitChiefs (V := V) c.originalPreimage a.projection)
    (htwo : ∀ s : SeriesOn ((conjugateSpan H V).subgroupOf H), s.noncentralCount = 2) :
    ChiefSmallNaturalAlternatives a.imageRepresentation := by
  by_contra hs
  obtain ⟨b,_,_,hn,_,hlarge⟩ :=
    cubic_natural_obstruction a ha J hJC c.originalPreimage a.projection hcub htwo hfour
  obtain ⟨s⟩ := SeriesOn.exists_series ((conjugateSpan H V).subgroupOf H)
  obtain ⟨i,hi,hl,hd,_⟩ := hlarge s
  have hu := original_chief_cartan_movement_le_two a ha hD hs c hfour J hJ hAJ s i hi hd b
  have hm := originalSeedFactor_codim_le_fixed_movement H V s i J hJC ⟨(b : H),hn⟩
  have hbad : 3 ≤ 2 := hl.trans (hm.trans hu)
  omega
end Original
end CFSG.Quasithin.Chapter8.MathieuShadowRows
