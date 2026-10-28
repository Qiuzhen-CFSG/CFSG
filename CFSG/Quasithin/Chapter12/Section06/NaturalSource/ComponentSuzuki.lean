module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentCondition
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Components.Suzuki
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.ThreeFree
public import Theory.Quasithin.PositiveLocalRank

/-!
# Excluding Suzuki and splitting the original selected component by three-rank

The original inverted-odd-order restriction contradicts the Suzuki witness
on K-star. Cyclic odd Sylow transfer lifts any Suzuki marking of
K-star/Z(K-star) to K-star, so the exclusion also applies to the faithful
component K-hat, through its actual central quotient.

Genuine Theorems A and C give the A.3.6 catalogue on the selected component.
Its only three-free row is Suzuki. Thus three divides |K-star|; the ambient
SQTK bound and the literal two-core projection give m₃(K)=m₃(K-star)=1 or 2.
All earlier point, fixed-space, intersection and nonsingular hypotheses
remain explicit. The remaining component exclusions and the abelian
point-span conclusion of 12.6.26 are not assumed or asserted here.

Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The actual star component is not a Suzuki group. -/
theorem SourceHypothesis.original_selectedComponent_star_not_suzuki
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (m : ℕ) (hm : 0 < m) :
    ¬ Nonempty ((Nonabelian.Setup.star H c.K) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rintro ⟨e⟩
  obtain ⟨a⟩ := S.original_selectedComponent_action D hZ z hz hTV hTz hbound hns hH hn c
  obtain ⟨t,ht,x,_,ho,hl,hi⟩ := a.suzuki_inverted_witness m hm e
  have hx : x ≠ 1 := fun he => by simp only [he,orderOf_one] at hl; omega
  rcases S.original_star_inverted_odd_order D hZ z hz hTV hTz hbound hns hH t ht x hx ho hi with h|h <;> omega
/-- The literal simple central quotient of K-star is not a Suzuki group. -/
theorem SourceHypothesis.original_selectedComponent_not_suzuki
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (m : ℕ) (hm : 0 < m) :
    ¬ Nonempty (((Nonabelian.Setup.star H c.K) ⧸ center (Nonabelian.Setup.star H c.K)) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rintro ⟨e⟩
  let := c.component.2
  obtain ⟨e',_⟩ := BenderSuzuki.MatrixGroups.equiv_of_suzuki_central_quotient
    c.star_twoCore_eq_bot m hm e
  exact S.original_selectedComponent_star_not_suzuki D hZ z hz hTV hTz hbound hns hH hn c m hm ⟨e'⟩

/-- The original selected component has order divisible by three after the star map. -/
theorem SourceHypothesis.original_selectedComponent_star_three_dvd
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) :
    3 ∣ Nat.card (Nonabelian.Setup.star H c.K) := by
  by_contra h3
  have hc := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) _
    (S.original_star_sqtk D hZ z hz hH) (pCore_quotient_pCore_eq_bot 2) _ c.component.isCComponent
  obtain ⟨m,hm,he⟩ := hc.suzuki_of_three_free h3
  exact S.original_selectedComponent_star_not_suzuki D hZ z hz hTV hTz hbound hns hH hn c m (by omega) he

/-- The selected star component has three-rank one or two. -/
theorem SourceHypothesis.original_selectedComponent_star_three_rank
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) :
    primeRank 3 (Nonabelian.Setup.star H c.K) = 1 ∨
      primeRank 3 (Nonabelian.Setup.star H c.K) = 2 := by
  have hl := Theory.Quasithin.one_le_primeRank_of_dvd_card
    (S.original_selectedComponent_star_three_dvd D hZ z hz hTV hTz hbound hns hH hn c)
  have hu := (Theory.GroupTheory.primeRank_le_of_injective 3 (Nonabelian.Setup.star H c.K).subtype
    (Nonabelian.Setup.star H c.K).subtype_injective).trans
      (S.original_star_three_rank D hZ z hz hH)
  omega

/-- The same source rank dichotomy holds for the original K before quotienting. -/
theorem SourceHypothesis.original_selectedComponent_three_rank
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) :
    primeRank 3 c.K = 1 ∨ primeRank 3 c.K = 2 := by
  rw [c.three_rank_eq_star]
  exact S.original_selectedComponent_star_three_rank D hZ z hz hTV hTz hbound hns hH hn c

end CFSG.Quasithin.Chapter12.Section06
