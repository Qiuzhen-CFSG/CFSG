module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankTwoJanko
public import Theory.SpecificGroups.SU3.QuinticProjectiveSylowFixer
public import Theory.SpecificGroups.SU3.TernarySylowCentralizer

/-!
# Odd unitary exclusions in the original rank-two branch

Transport the original nontrivial Sylow-fixing involution and faithful E₉
through the component's specified Hermitian model. The native PSU₃(3)
centralizer order excludes that model while preserving the original
point, marked module, quotient action and earlier geometry hypotheses.
For PSU₃(5), the original faithful binary section receives the projective
root embedding; the same marked involution then has displacement at least
eight and at most four. This eliminates both odd unitary rows and leaves
the nonlinear binary rank-two models and PSL₅(2), with condition (*) intact.
The rank-one branch, abelian point span and universal natural reduction
remain subsequent source obligations.
Source: Aschbacher–Smith, proof of 12.6.26, printed p.832.
-/

open BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)


include hz hTV hTz hbound hH hn a in
/-- The original rank-two component cannot be PSU3(3). -/
theorem SourceHypothesis.original_rank_two_not_unitaryThreeThree
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    ¬ ClassicalGroup.IsPSU (Nonabelian.Setup.star H c.K) 3 3 := by
  rintro ⟨F,hFfield,hFfinite,J,hF,hconj,⟨e⟩⟩
  let := hFfield
  let := hFfinite
  let : IsSimpleGroup (Nonabelian.Setup.star H c.K) :=
    S.original_selectedComponent_simple D hZ z hz hTV hTz hbound hH hn c a hTI hns
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  obtain ⟨α,hα,⟨P,hP⟩,h9⟩ := S.original_rank_two_model_centralizer D hZ z hz hTV hTz hbound hH hn c a hTI hns hr e
  exact HermitianForm.TernarySylowCentralizer.not_nine_dvd_sylow_fixer_centralizer
    J hF hconj P α hα hP h9
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The same original rank-four section excludes the projective quintic unitary model. -/
theorem SourceHypothesis.original_selectedComponent_not_projectiveUnitaryThreeFive
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    ¬ ClassicalGroup.IsPSU (Nonabelian.Setup.star H c.K) 3 5 := by
  rintro ⟨F,hFfield,hFfinite,J,hF,hconj,⟨e⟩⟩
  let := hFfield
  let := hFfinite
  let B := Nonabelian.Setup.star H c.K
  let : IsSimpleGroup B :=
    S.original_selectedComponent_simple D hZ z hz hTV hTz hbound hH hn c a hTI hns
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  let U := (V.subgroupOf c.localActor).map a.action
  have hU : Nat.card U = 2 := a.module_card
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  have hto : orderOf (t : MulAut B) = 2 :=
    (orderOf_injective U.subtype U.subtype_injective t).trans ht
  obtain ⟨P,hP⟩ := S.original_action_module_fixes_component_sylow D hZ z hz hTV hTz hbound hH hn c a
  let α := MulAut.congr e (t : MulAut B)
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hα : orderOf α = 2 := ((MulAut.congr e).orderOf_eq _).trans hto
  have hQ : ∀ x ∈ Q, α x = x := by
    rintro _ ⟨x,hx,rfl⟩
    change e ((t : MulAut B) (e.symm (e x))) = e x
    rw [e.symm_apply_apply,hP t t.property x hx]
  obtain ⟨v,hv,he⟩ := t.property
  let u := QuotientGroup.mk' (pCore 2 H) (inclusion a.local_le v)
  have hu : u ∈ Nonabelian.Setup.star H V := mem_map_of_mem _ hv
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let := h.point_normal_in_UH
  let := h.point_quotient_elementary
  obtain ⟨σ,f,hσ,_⟩ := h.faithful_point_quotient
  have hr := S.original_binary_displacement_bound D hZ z hz hTV hTz hbound hH hn σ f
  let j := B.subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := B.subtype_injective.comp e.symm.injective
  have heq (x : ProjectiveSpecialUnitaryMatrixGroup J) : j (α x) = u * j x * u⁻¹ := by
    change (e.symm (e ((t : MulAut B) (e.symm x)))).val = _
    rw [e.symm_apply_apply,←he]
    exact a.conjugation v (e.symm x)
  have hl := HermitianForm.QuinticSylowFixer.eight_le_projective_displacement_of_sylow_fixer
    J hF hconj σ hσ j hj u α hα Q hQ heq
  have hupp := hr u hu
  omega

end CFSG.Quasithin.Chapter12.Section06

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)


include hz hTV hTz hbound hH hn a in
/-- After the sporadic and odd-unitary exclusions, the same rank-two component
retains only the binary rows, with its literal centralizer-core obstruction. -/
theorem SourceHypothesis.original_rank_two_even_models
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    let B := Nonabelian.Setup.star H c.K
    let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
    let C := centralizer (U : Set a.action.range)
    2 ≤ primeRank 3 (pCore 3 (C ⧸ pCore 2 C)) ∧
      ((∃ f, ChapterA.Section02.IsTheoremCRankTwoModel B f ∧
          ¬ ClassicalGroup.IsPSL B 3 (2^f)) ∨ ClassicalGroup.IsPSL B 5 2) := by
  obtain ⟨hcore,hmodels⟩ := S.original_rank_two_remaining_models D hZ z hz hTV hTz
    hbound hH hn c a hTI hns hr
  refine ⟨hcore,?_⟩
  rcases hmodels with (h|h)|h|h|h
  · exact (S.original_rank_two_not_unitaryThreeThree D hZ z hz hTV hTz hbound hH hn c a hTI hns hr h).elim
  · exact (S.original_selectedComponent_not_projectiveUnitaryThreeFive D hZ z hz hTV hTz hbound hH hn c a hTI hns h).elim
  · exact Or.inl h
  · exact Or.inr h
  · exact (S.original_rank_two_not_jankoFour D hZ z hz hTV hTz hbound hH hn c a hTI hns hr h).elim
end CFSG.Quasithin.Chapter12.Section06
