module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.QuotientTransport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.CentralizerStructure.Residual
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.LargeFamily
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.FieldReduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.Quasithin.Rank
/-!
# The prime-field PSL₂ input for the centralizer quotient

The full centralizer has SL₂(p) solvable residual. Passing to its residual
Sylow supplement gives equal two- and solvable residuals. The reusable
radical-quotient theorem then identifies the actual simple generalized
Fitting subgroup as PSL₂(p) and proves the radical is a two-group.
Consequently the ambient SQTK hypothesis descends to this literal quotient.

For p > 5, the existing prime-field large-family escape contract now suffices:
the whole-group component case settles small actors and the quotient-family
transport recovers the full original centralizer. The escape calculation is
still an explicit prerequisite. No assertion is made at p = 5 by this route.

Source: Aschbacher--Smith A.3.21(a), p.55; E.1.2, E.1.8, E.1.14(6)--(7),
pp.210--214; Aschbacher (1982), Lemmas 4.10--4.11.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
variable {G : Type*} [Group G] [Finite G]

/-- The literal quotient has a two-group kernel and an actual PSL₂(p) simple socle. -/
theorem centralizer_residual_quotient_structure (L : Subgroup G) [L.Normal]
    {T : Sylow 2 G} (hLT : L ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p)
    (hmodel : ClassicalGroup.IsPSU L 3 p) {z : G} (hzL : z ∈ L) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let K := centralizerResidualOvergroup T z
    let Q := K ⧸ solvableRadical K
    IsPGroup 2 (solvableRadical K) ∧ IsSimpleGroup (generalizedFitting Q) ∧
      ClassicalGroup.IsPSL (generalizedFitting Q) 2 p ∧
      ∀ S : Sylow 2 Q, generalizedFitting Q ⊔ (S : Subgroup Q) = ⊤ := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨ec⟩ := inner_centralizer_residual_equiv L T hLT hp ho hlarge hmodel z hzL hz
  let e := (centralizerResidualOvergroup_residualEquiv hTz).trans ec
  have hF : Nat.card (ZMod p) = p := by simp only [Nat.card_eq_fintype_card, ZMod.card]
  obtain ⟨hR, hs, he, hS⟩ := Theory.SpecificGroups.SL2.ResidualTwoExtension.radical_quotient_structure
    (hF.symm ▸ ho) (hF.symm ▸ hlarge) e (centralizerResidualOvergroup_pResidual_eq hTz)
  exact ⟨hR, hs, ⟨ZMod p, inferInstance, inferInstance, hF, he⟩, hS⟩

/-- The original SQTK hypothesis supplies the precise quotient hypothesis
required by the existing prime-field local-escape producer. -/
theorem centralizer_residual_quotient_sqtk {κ : GroupClass} (hG : IsSQTK κ G)
    (L : Subgroup G) [L.Normal] {T : Sylow 2 G} (hLT : L ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p)
    (hmodel : ClassicalGroup.IsPSU L 3 p) {z : G} (hzL : z ∈ L) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    IsSQTK κ ((centralizerResidualOvergroup T z) ⧸
      solvableRadical (centralizerResidualOvergroup T z)) := by
  have hR := (centralizer_residual_quotient_structure L hLT hp ho hlarge hmodel hzL hz hTz).1
  exact ⟨odd_primeRank_le_two_section_of_isTwoGroup hG.stronglyQuasithin
    (centralizerResidualOvergroup T z) _ hR,
    (hG.isKGroup.subgroup _).quotient _⟩

/-- For p > 5, only the existing prime-field escape calculation remains.
All simple-socle, component and family-transport premises are discharged. -/
theorem centralizer_le_of_prime_quotient_escape (L : Subgroup G) [L.Normal]
    {T : Sylow 2 G} (hLT : L ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 5 < p)
    (hmodel : ClassicalGroup.IsPSU L 3 p) (d : LargeFamilyObstruction T)
    {z : G} (hzL : z ∈ L) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hescape : ∀ S : Sylow 2 ((centralizerResidualOvergroup T z) ⧸
      solvableRadical (centralizerResidualOvergroup T z)),
      PSLTwoGeneration.LargeFamilyEscapeAt S) :
    centralizer ({z} : Set G) ≤ d.overgroup := by
  let K := centralizerResidualOvergroup T z
  let Q := K ⧸ solvableRadical K
  obtain ⟨_, hs, hm, hS⟩ := centralizer_residual_quotient_structure L hLT hp ho (by omega)
    hmodel hzL hz hTz
  let : IsSimpleGroup (generalizedFitting Q) := hs
  have ha := PSLTwoGeneration.nonabelian_of_model (generalizedFitting Q) hlarge hm
  have hgen : IsEGenerated 1 Q :=
    PSLTwoGeneration.isEGenerated_of_component_and_large_escape
      (fun S A _ _ hne => ValuesEvenClassical.RankOneUpper.eCaseComponent_top
        ha S (hS S) (S : Subgroup Q) A hne) hescape
  let S := (T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)).mapSurjective
    (f := QuotientGroup.mk' (solvableRadical K)) (QuotientGroup.mk'_surjective _)
  exact centralizer_le_of_residual_quotient_family_generation d hTz
    (hgen S _ ((ChiefOrbit.restrictedFamily_elementary K d.elementary).map _
      (QuotientGroup.mk'_surjective _)))
end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
