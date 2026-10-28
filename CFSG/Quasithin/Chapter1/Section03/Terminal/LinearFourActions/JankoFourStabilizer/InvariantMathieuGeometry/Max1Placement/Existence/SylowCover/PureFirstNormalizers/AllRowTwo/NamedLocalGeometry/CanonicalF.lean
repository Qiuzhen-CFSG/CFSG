module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.FPlacement
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NativeFNormalizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.CoverAssembly.Elementary

/-!
# The canonical intersection of native F occurrences

Intersect all actual ambient conjugates of F containing X. This intersection
contains X, is normalized by N(X), and lies in any one of those F occurrences.
A second-class element in this intersection therefore supplies whole-normalizer
coverage by the already proved nonfirst F theorem. Maximal TWO-locality gives
one of the literal named-local equalities. The final applications concern the
shared finite rows and an arbitrary radical, with all restriction maps retained.

The mixed-intersection premise remains explicit. The concrete F placements
are discharged here, but the finite occurrence census and a mixed common
member must still be proved before this gives the unconditional source branch.
Source: Kleidman--Wilson (1988), Section 2.1 and Proposition 2.2.3, pp.488--491.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
open ElementaryNormalizerCover LargeCenterRadicals FiniteConfigurations
attribute [local irreducible] modelGroup matrixA matrixB

/-- Actual F occurrences containing the whole subgroup. -/
@[expose] def fOccurrences (X : Subgroup Model) : Set (Subgroup Model) :=
  {Y | ∃ g : Model, Y = nativeF.map (MulAut.conj g).toMonoidHom ∧ X ≤ Y}

/-- Intersect the entire ambient family, without selecting an invariant occurrence. -/
@[expose] def fIntersection (X : Subgroup Model) : Subgroup Model := sInf (fOccurrences X)

private theorem conjugate_comp (X : Subgroup Model) (g h : Model) :
    (X.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      X.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem conjugate_one (X : Subgroup Model) :
    X.map (MulAut.conj (1 : Model)).toMonoidHom = X :=
  mem_normalizer_iff_map_conj_eq.mp (normalizer (X : Set Model)).one_mem

theorem le_fIntersection (X : Subgroup Model) : X ≤ fIntersection X := by
  apply le_sInf
  rintro Y ⟨g,he,hX⟩
  exact hX

theorem fIntersection_le (X : Subgroup Model) (g : Model)
    (hX : X ≤ nativeF.map (MulAut.conj g).toMonoidHom) :
    fIntersection X ≤ nativeF.map (MulAut.conj g).toMonoidHom :=
  sInf_le ⟨g,rfl,hX⟩

/-- Whole normalizers preserve the full family, hence its intersection. -/
theorem normalizer_le_fIntersection_normalizer (X : Subgroup Model) :
    normalizer (X : Set Model) ≤ normalizer (fIntersection X : Set Model) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  have hmap : (fIntersection X).map (MulAut.conj g).toMonoidHom ≤ fIntersection X := by
    apply le_sInf
    rintro Y ⟨k,rfl,hX⟩
    have hX' : X ≤ nativeF.map (MulAut.conj (g⁻¹*k)).toMonoidHom := by
      have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hX
      have hfix : X.map (MulAut.conj g⁻¹).toMonoidHom = X :=
        mem_normalizer_iff_map_conj_eq.mp ((normalizer (X : Set Model)).inv_mem hg)
      rw [hfix,conjugate_comp] at hm
      exact hm
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) (fIntersection_le X _ hX')
    rwa [conjugate_comp,mul_inv_cancel_left] at hm
  exact hmap (mem_map_of_mem _ hx)

/-- Every nonempty occurrence family makes the canonical intersection elementary. -/
theorem fIntersection_elementary (X : Subgroup Model) (g : Model)
    (hX : X ≤ nativeF.map (MulAut.conj g).toMonoidHom) :
    IsElementaryAbelian 2 (fIntersection X) := by
  let := LinearFive.F_elementary
  let : IsElementaryAbelian 2 (nativeF.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  exact IsElementaryAbelian.of_le (fIntersection_le X g hX)

/-- A mixed member of the canonical F intersection closes the original
maximal-two-local placement, without a mixed-to-pure return. -/
theorem nativeLocalPlacement_of_fIntersection (X : Subgroup Model)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model)))
    (g : Model) (hX : X ≤ nativeF.map (MulAut.conj g).toMonoidHom)
    (t : Model) (ht : t ∈ fIntersection X) (ht2 : orderOf t = 2)
    (hnt : ¬ IsConj a t) : NativeLocalPlacement (normalizer (X : Set Model)) := by
  let := fIntersection_elementary X g hX
  have hne : fIntersection X ≠ ⊥ := by
    intro he
    have ht1 : t = 1 := mem_bot.mp (he ▸ ht)
    simp [ht1] at ht2
  have he : normalizer (X : Set Model) = normalizer (fIntersection X : Set Model) :=
    hmax.eq_of_le ⟨fIntersection X,hne,IsElementaryAbelian.isPGroup 2 _,rfl⟩
      (normalizer_le_fIntersection_normalizer X)
  obtain ⟨k,hk | hk⟩ := maximal_twoLocal_of_nativeF_conjugate
    (fIntersection X) (normalizer (X : Set Model)) g (fIntersection_le X g hX)
    t ht ht2 hnt hmax he
  · exact ⟨k,Or.inr (Or.inr (Or.inl (by rwa [LinearFive.M_F_eq_fullNormalizer] at hk)))⟩
  · exact ⟨k,Or.inl hk⟩

/-- A unique actual F occurrence supplies the sixteen-row endpoint directly.
The uniqueness concerns the full ambient family, not the diagnostic core masks. -/
theorem nativeLocalPlacement_of_unique_F (X : Subgroup Model)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) (g : Model)
    (hunique : fOccurrences X = {nativeF.map (MulAut.conj g).toMonoidHom}) :
    NativeLocalPlacement (normalizer (X : Set Model)) := by
  have hf : fIntersection X = nativeF.map (MulAut.conj g).toMonoidHom := by
    simp only [fIntersection,hunique,sInf_singleton]
  have hn := normalizer_le_fIntersection_normalizer X
  rw [hf,← map_equiv_normalizer_eq,nativeF_fullNormalizer_eq] at hn
  have he := hmax.eq_of_le (nativeF_generated_isTwoLocal.map_equiv (MulAut.conj g)) hn
  exact ⟨g,Or.inr (Or.inr (Or.inl (by rwa [LinearFive.M_F_eq_fullNormalizer] at he)))⟩

/-- The actual finite-row application discharges F placement. Only the
independent finite-incidence claim of a common second-class member remains. -/
theorem nonline_row_nativeLocalPlacement (i : Fin 26) (hi : i ≠ 5)
    (hmax : IsMaximalTwoLocal (normalizer (row i : Set Model)))
    (t : Model) (ht : t ∈ fIntersection (row i)) (ht2 : orderOf t = 2)
    (hnt : ¬ IsConj a t) : NativeLocalPlacement (normalizer (row i : Set Model)) := by
  obtain ⟨g,hg⟩ := nonline_row_le_F_conjugate i hi
  exact nativeLocalPlacement_of_fIntersection (row i) hmax g hg t ht ht2 hnt

/-- The arbitrary-radical restriction through this same native intersection.
The named local contains the entire original normalizer, and both normalizer
core maps are literal subgroup inclusions. Maximality is not needed here. -/
theorem radical_local_of_fIntersection (P X : Subgroup Model) (hP : P.IsPRadical 2)
    (hPX : normalizer (P : Set Model) ≤ normalizer (X : Set Model))
    (g : Model) (hX : X ≤ nativeF.map (MulAut.conj g).toMonoidHom)
    (t : Model) (ht : t ∈ fIntersection X) (ht2 : orderOf t = 2)
    (hnt : ¬ IsConj a t) :
    ∃ (k : Model) (H : Subgroup Model), IsTwoLocal H ∧
      (H = LinearFive.M_F.map (MulAut.conj k).toMonoidHom ∨
        H = max1.map (MulAut.conj k).toMonoidHom) ∧
      normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P := by
  exact radical_local_of_nativeF_conjugate P (fIntersection X) hP g (fIntersection_le X g hX)
    t ht ht2 hnt (hPX.trans (normalizer_le_fIntersection_normalizer X))

/-- Literal radical application at any of the shared nonline rows; its F
container is furnished by the checked native words, not by a supplied premise. -/
theorem radical_local_of_nonline_row (P : Subgroup Model) (hP : P.IsPRadical 2)
    (i : Fin 26) (hi : i ≠ 5)
    (hPX : normalizer (P : Set Model) ≤ normalizer (row i : Set Model))
    (t : Model) (ht : t ∈ fIntersection (row i)) (ht2 : orderOf t = 2)
    (hnt : ¬ IsConj a t) :
    ∃ (k : Model) (H : Subgroup Model), IsTwoLocal H ∧
      (H = LinearFive.M_F.map (MulAut.conj k).toMonoidHom ∨
        H = max1.map (MulAut.conj k).toMonoidHom) ∧
      normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P := by
  obtain ⟨g,hg⟩ := nonline_row_le_F_conjugate i hi
  exact radical_local_of_fIntersection P (row i) hP hPX g hg t ht ht2 hnt

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
