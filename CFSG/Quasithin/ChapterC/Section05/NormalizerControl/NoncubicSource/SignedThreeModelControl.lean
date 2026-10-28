module
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.SignedThree
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SmallModelControl
/-!
# The marked signed-three normalizer bound in the source conventions

Actual isomorphisms transport the full Sylow and its normalized SL2(5)
subgroup to the special or projective linear/unitary model at five.
The proved marked automorphism theorem preserves this subgroup under
every Sylow-preserving automorphism. The original ambient conjugation
therefore makes N(S) normalize S intersect C(L), retaining its kernel.
Source: Aschbacher--Smith C.5.12, printed p.163.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open Chapter1.Section02.LocalModels
variable {D : Type*} [Group D] [Finite D]

private theorem invariant_of_equiv {E : Type*} [Group E] [Finite E]
    (e : D ≃* E) (L : Subgroup D)
    (hmodel : ∀ T : Sylow 2 E, (T : Subgroup E) ≤ normalizer (L.map e.toMonoidHom : Set E) →
      ∀ a : MulAut E, (T : Subgroup E).map a.toMonoidHom = T →
        (L.map e.toMonoidHom).map a.toMonoidHom = L.map e.toMonoidHom)
    (T : Sylow 2 D) (hTL : (T : Subgroup D) ≤ normalizer (L : Set D))
    (a : MulAut D) (ha : (T : Subgroup D).map a.toMonoidHom = T) :
    L.map a.toMonoidHom = L := by
  let P := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let b : MulAut E := MulAut.congr e a
  have he (J : Subgroup D) : (J.map e.toMonoidHom).map b.toMonoidHom =
      (J.map a.toMonoidHom).map e.toMonoidHom := by
    rw [Subgroup.map_map,Subgroup.map_map]
    congr 1
    ext x
    change e (a (e.symm (e x))) = e (a x)
    rw [e.symm_apply_apply]
  have hP : (P : Subgroup E) ≤ normalizer (L.map e.toMonoidHom : Set E) := by
    rw [← map_normalizer_eq_of_bijective L e.bijective]
    exact map_mono hTL
  have hb : (P : Subgroup E).map b.toMonoidHom = P := by
    change ((T : Subgroup D).map e.toMonoidHom).map b.toMonoidHom = (T : Subgroup D).map e.toMonoidHom
    rw [he,ha]
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [← he]
  exact hmodel P hP b hb

theorem signed_three_model_preserves_sl2_five
    (hm : ∃ u, IsPSLSign D u 3 5 ∨ IsSLSign D u 3 5)
    (L : Subgroup D) (hL : IsSL L 2 5)
    (T : Sylow 2 D) (hTL : (T : Subgroup D) ≤ normalizer (L : Set D))
    (a : MulAut D) (ha : (T : Subgroup D).map a.toMonoidHom = T) :
    L.map a.toMonoidHom = L := by
  obtain ⟨F0,_,_,hF0,⟨eL⟩⟩ := hL
  rcases hm with ⟨u,hm | hm⟩
  · cases u with
    | false =>
        obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
        apply invariant_of_equiv e L ?_ T hTL a ha
        exact Theory.SpecificGroups.Classical.SylowMarkedSL2.psl3_preserves_sl2_five hF _
          ((L.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eL) hF0
    | true =>
        obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
        let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
          Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
        apply invariant_of_equiv e L ?_ T hTL a ha
        exact Theory.SpecificGroups.Classical.SylowMarkedSL2.psu3_preserves_sl2_five J hF hconj _
          ((L.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eL) hF0
  · cases u with
    | false =>
        obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
        apply invariant_of_equiv e L ?_ T hTL a ha
        exact Theory.SpecificGroups.Classical.SylowMarkedSL2.sl3_preserves_sl2_five hF _
          ((L.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eL) hF0
    | true =>
        obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
        apply invariant_of_equiv e L ?_ T hTL a ha
        exact Theory.SpecificGroups.Classical.SylowMarkedSL2.su3_preserves_sl2_five J hF hconj _
          ((L.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eL) hF0

omit [Finite D] in
theorem signed_three_models_transport {E : Type*} [Group E]
    (e : D ≃* E) (hm : ∃ u, IsPSLSign D u 3 5 ∨ IsSLSign D u 3 5) :
    ∃ u, IsPSLSign E u 3 5 ∨ IsSLSign E u 3 5 := by
  obtain ⟨u,hm | hm⟩ := hm
  · refine ⟨u,Or.inl ?_⟩
    cases u with
    | false => exact hm.of_mulEquiv e.symm
    | true =>
        obtain ⟨F,_,_,J,hF,hc,⟨a⟩⟩ := hm
        exact ⟨F,inferInstance,inferInstance,J,hF,hc,⟨e.symm.trans a⟩⟩
  · refine ⟨u,Or.inr ?_⟩
    cases u with
    | false =>
        obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
        exact ⟨F,inferInstance,inferInstance,hF,⟨e.symm.trans a⟩⟩
    | true =>
        obtain ⟨F,_,_,J,hF,hc,⟨a⟩⟩ := hm
        exact ⟨F,inferInstance,inferInstance,J,hF,hc,⟨e.symm.trans a⟩⟩

theorem signed_three_model_normalizer_centralizer
    {H : Type*} [Group H] [Finite H] (D : Subgroup H) [D.Normal]
    (hm : ∃ u, IsPSLSign D u 3 5 ∨ IsSLSign D u 3 5)
    (S : Sylow 2 H) (L : Subgroup H) (hLD : L ≤ D)
    (hL : IsSL L 2 5) (hSL : (S : Subgroup H) ≤ normalizer (L : Set H)) :
    normalizer (S : Set H) ≤ normalizer ((S : Subgroup H) ⊓ centralizer (L : Set H) : Set H) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hL
  have hLi : IsSL (L.subgroupOf D) 2 5 :=
    ⟨F,inferInstance,inferInstance,hF,⟨(subgroupOfEquivOfLe hLD).trans e⟩⟩
  exact Theory.SpecificGroups.Classical.SylowMarkedSL2.normalizer_le_normalizer_centralizer_of_characteristic_component
    D L hLD S hSL (signed_three_model_preserves_sl2_five hm _ hLi)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
