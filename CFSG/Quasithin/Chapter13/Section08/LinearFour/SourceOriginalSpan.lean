module
public import Theory.Representation.BinaryConjugationSection.ComplementPlaneGeneration
public import Theory.GroupTheory.ConjugateSpanSylow
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceLocalImage
public import CFSG.Quasithin.Chapter13.Section07.Preliminaries
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental

/-!
# The original U_L span in the maximal-chief argument

The actual L₀ image contains the cubic moving the complement of V₃/V₁.
Its natural displacement gives U_H = V₃ [U_H,L₀]. The F.9 setup puts U_H
inside T, which normalizes L; the chosen module puts V₃ inside L. Thus
U_H and its original L-span U_L lie inside L. This uses more than the
previous placement U_L ≤ O₂(LT), which alone does not imply U_L ≤ L.

Natural transitivity puts V inside U_L, and the original orders 16 and 32
make the inclusion strict. Earlier 13.7.3 gives the two-group property.
Transport to the normal-subgroup lattice of L now constructs a selected
maximal quotient above V, its faithful covered-A₆ action of binary degree
six or eighteen, and its contribution to every complete chief series of
the original L₀. The ambient quotient section retains exactly U_L and the
embedded selected kernel, through the canonical covered quotient map.

The original natural/F.9 setups and earlier centralizer bound remain inputs
from their source producers. Compatible second-tensor movement and exclusion
of order 64 on the selected quotient remain with this theorem-family owner;
this module does not assert nine factors or the final 13.8.28 contradiction.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.4(2),(7) and 13.8.30, printed pp.947 and 964.
-/

public noncomputable section
open Subgroup Representation NoncentralChiefRefinement
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open BinaryParabolicExteriorSquare.PlaneSpan BinaryLinear.FlagCoordinates
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The literal seed commutator proves the missing placement in L; original
natural transitivity and orders prove strictness, and 13.7.3 supplies the
p-group property without any abelianness assumption on U_L. -/
theorem source_original_span_placement
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hab : IsMulCommutative (conjugateSpanBy V G₁))
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (hDH : zero L ≤ H)
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hplane : d.imageSpace V₃ = plane) :
    Source.UH H V₃ = V₃ ⊔ ⁅Source.UH H V₃,zero L⁆ ∧
      Source.UL L H V₃ ≤ L ∧ V < Source.UL L H V₃ ∧
      IsPGroup 2 (Source.UL L H V₃) := by
  have hlocal := source_zero_matrix_image_from_original_seed s hab h hH hcentral hDH eL
    ρ d π hker honto hnatural hplane
  have hcubic : complementElement ∈ ((zero L).subgroupOf H).map π := by
    rw [hlocal]
    exact (show zpowers complementElement ≤ BinaryParabolicExteriorSquare.PlaneRadical.complementLocal
      from le_sup_right) (mem_zpowers _)
  have hseed := d.section_eq_plane_sup_commutator_of_complement H (zero L)
    (Source.UH H V₃) V₁ V₃ hDH ρ π hnatural
    (s.line_le_plane.trans s.plane_le_seed) (le_conjugateSpanBy _ _) hplane hcubic
  have hUnL : Source.UH H V₃ ≤ normalizer (L:Set G) :=
    hF.UH_le_QH.trans (hF.QH_le_T.trans s.normalizes_L)
  have hUL : Source.UH H V₃ ≤ L := by
    rw [hseed]
    exact sup_le (s.seed_le.trans s.chosen.le_component)
      ((commutator_mono le_rfl (zero_le L)).trans
        (le_normalizer_iff_commutator_le_right.mp hUnL))
  have hspanL : Source.UL L H V₃ ≤ L := conjugateSpanBy_le_self hUL
  have hVspan : V ≤ Source.UL L H V₃ := by
    have hne : V₃ ≠ ⊥ := by
      intro he
      have hc := s.seed_card
      simp [he] at hc
    obtain ⟨⟨x,hx⟩,hx1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have hx1 : x ≠ 1 := fun he => hx1' (Subtype.ext he)
    intro y hy
    by_cases hy1 : y = 1
    · exact hy1 ▸ (Source.UL L H V₃).one_mem
    obtain ⟨l,hl,rfl⟩ := Section07.natural_nonzero_transitive s (s.seed_le hx) hy hx1 hy1
    exact subset_closure ⟨l,hl,x,le_conjugateSpanBy V₃ H hx,rfl⟩
  have hUc : Nat.card (Source.UH H V₃) = 32 := by
    have hc := d.card_section
    rw [s.line_card] at hc
    simpa using hc
  have hVc : Nat.card V = 16 := by
    calc Nat.card V = Nat.card (BinaryPermutation.natural (Fin 6)) :=
           Nat.card_congr s.coordinate.toEquiv
         _ = 16 := by
           rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
             BinaryPermutation.finrank_natural_even (Fin 6) (by decide),Fintype.card_fin]
           norm_num
  have hstrict : V < Source.UL L H V₃ := by
    refine lt_of_le_of_ne hVspan ?_
    intro he
    have hh : Nat.card (Source.UH H V₃) ≤ Nat.card V :=
      Nat.card_le_card_of_injective
        (inclusion ((le_conjugateSpanBy (Source.UH H V₃) L).trans he.ge))
        (inclusion_injective _)
    omega
  have hUab : IsMulCommutative (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH :=
    (s.toLocalSetup hab).uh_elementary hH |>.toIsMulCommutative
  exact ⟨hseed,hspanL,hstrict,(isPGroup_pCoreIn 2 _).to_le
    (Section07.span_UH_L_le_core s hF hUab)⟩

/-- Select the actual maximal quotient of U_L above V, retaining its
canonical action, exact ambient kernel and original L₀ chief-series count.
The binary degree-six alternative has not yet been excluded. -/
theorem exists_source_original_span_maximal_chief
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hab : IsMulCommutative (conjugateSpanBy V G₁))
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (hDH : zero L ≤ H)
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hplane : d.imageSpace V₃ = plane) :
    ∃ U W : NormalNode L,
      U.val.map L.subtype = Source.UL L H V₃ ∧
      V ≤ W.val.map L.subtype ∧ W ⋖ U ∧
      U.val ≤ W.val ⊔ (zero L).subgroupOf L ∧
      ∃ hbin : IsElementaryAbelian 2 (Section W U),
        let _ := hbin
        ∃ σ : Representation (ZMod 2) Atlas.Codes.HexEvenAutomorphisms
            (Additive (Section W U)),
          IsIrreducible σ ∧ Function.Injective σ ∧
          σ.comp (eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
            binarySectionRepresentation W U ∧
          Nonempty (BinaryConjugationSection L (Source.UL L H V₃)
            (W.val.map L.subtype)
            (σ.comp (eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) ∧
          (Module.finrank (ZMod 2) (Additive (Section W U)) = 6 ∨
            Module.finrank (ZMod 2) (Additive (Section W U)) = 18) ∧
          ∀ t : ChiefSeries (zero L), t.head = ⊥ → t.last = ⊤ →
            Module.finrank (ZMod 2) (Additive (Section W U)) ≤
              2 * t.noncentralTwoCount := by
  obtain ⟨hseed,hUL,hstrict,hp⟩ := source_original_span_placement s hab h hH hF
    hcentral hDH eL ρ d π hker honto hnatural hplane
  let A : NormalNode L := ⟨V.subgroupOf L,
    normal_subgroupOf_of_le_normalizer (le_sup_left.trans s.normalizes_V)⟩
  let U : NormalNode L := ⟨(Source.UL L H V₃).subgroupOf L,
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)⟩
  let S := (Source.UH H V₃).subgroupOf L
  have hSL : Source.UH H V₃ ≤ L := (le_conjugateSpanBy _ _).trans hUL
  have hAm : A.val.map L.subtype = V := map_subgroupOf_eq_of_le s.chosen.le_component
  have hUm : U.val.map L.subtype = Source.UL L H V₃ := map_subgroupOf_eq_of_le hUL
  have hSm : S.map L.subtype = Source.UH H V₃ := map_subgroupOf_eq_of_le hSL
  have hAU : A < U := by
    refine lt_of_le_of_ne (show V.subgroupOf L ≤ (Source.UL L H V₃).subgroupOf L
      from comap_mono hstrict.le) ?_
    intro he
    have hh := congrArg (fun n : NormalNode L => n.val.map L.subtype) he
    rw [hAm,hUm] at hh
    exact hstrict.ne hh
  have hSU : S ≤ U.val := comap_mono (le_conjugateSpanBy _ _)
  have hgen : U.val = conjugateSpanBy S ⊤ := by
    apply map_injective L.subtype_injective
    rw [hUm,map_conjugateSpanBy,hSm,←MonoidHom.range_eq_map,range_subtype]
    rfl
  have hseed' : S ≤ A.val ⊔ ⁅S,(zero L).subgroupOf L⁆ := by
    apply (map_le_map_iff_of_injective L.subtype_injective).mp
    rw [hSm,Subgroup.map_sup,hAm,map_commutator,hSm,
      map_subgroupOf_eq_of_le (zero_le L)]
    exact hseed.le.trans (sup_le_sup_right s.seed_le _)
  let X := (zero L).subgroupOf L
  let : X.Normal := normal_subgroupOf_of_le_normalizer (L_normalizes_zero L)
  obtain ⟨W,hAW,hWU,hcover,hbin,σ,hirr,hfaith,hσ,hdegree⟩ :=
    exists_source_maximal_quotient A U hAU hp.comap_subtype X S hSU hgen hseed' eL
      (source_zero_cover_image L eL)
  let := hbin
  let := hirr
  refine ⟨U,W,hUm,?_,hWU,hcover,hbin,σ,hirr,hfaith,hσ,?_,hdegree,?_⟩
  · rw [←hAm]
    exact map_mono hAW
  · rw [hσ,←hUm]
    exact ⟨ambientBinarySection L W U hWU.le⟩
  · intro t ht0 ht1
    let πL := eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    have hπL : (πL.comp X.subtype).range = center Atlas.Codes.HexEvenAutomorphisms := by
      rw [MonoidHom.range_comp,range_subtype]
      exact source_zero_cover_image L eL
    let c : BinaryConjugationSection X (U.val ⊓ X) (W.val ⊓ X)
        (σ.comp (πL.comp X.subtype)) := by
      have q := source_intersection_coordinates W U X hWU.le hcover
      rw [←hσ] at q
      exact q
    let eX : X ≃* zero L := subgroupOfEquivOfLe (zero_le L)
    have ht := t.mapActor_complete eX.symm ht0 ht1
    have hc := Representation.Hexacode.binary_degree_le_twice_chief_count
      X (U.val ⊓ X) (W.val ⊓ X) σ hfaith (πL.comp X.subtype) hπL c
        (t.mapActor eX.symm) ht.1 ht.2
    simpa only [ChiefSeries.mapActor_noncentralTwoCount] using hc

end CFSG.Quasithin.Chapter13.Section08.LinearFour
