module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Source

/-!
# Surviving Mathieu covers under the original Γ₀ hypotheses

Source: Aschbacher–Smith 2.3.7–2.3.9, printed pp.523–526.
`MathieuSourceSetup` retains Γ₀, its actual local pair, the original H,L,M,S,z,
and the selected ambient Sylow T with Z(T) ≤ S < T and z ∈ Z(T).
It contains no assertion about a covering kernel or its normalizer.
The selection theorem constructs this context from 2.3.9(3).

The earlier universal structural 1.1.5 and Local C(G,T) implications are
passed explicitly to the component setup constructor; their existing
producers are qt-1-01 and qt-c-01. Applying the proved M₁₁ and M₂₃ cover
calculations gives their source intersections. The M₂₂ ambient exclusion
is not asserted. The final restriction shows precisely the forbidden
normalization of its literal two-core by the selected T.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]
variable {C : GroupClass} {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Original source hypotheses, retaining the ambient data absent from
`LocalSetup`. The component and all subgroup inclusions are literal. -/
structure MathieuSourceSetup (H L M : Subgroup G) (S : Sylow 2 H) (z : G) where
  T : Sylow 2 G
  maximal : IsMaximalTwoLocal M
  sylow_le : (T : Subgroup G) ≤ M
  unique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M
  gamma : H ∈ gammaZero (Chapter1.He G) M
  U : Subgroup G
  HU : Subgroup G
  pair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H
  base_le : U ≤ (S : Subgroup H).map H.subtype
  component_le : L ≤ H
  component : IsComponent H (L.subgroupOf H)
  sylow_lt : (S : Subgroup H).map H.subtype < (T : Subgroup G)
  center_le : (center (T : Subgroup G)).map (T : Subgroup G).subtype ≤
    (S : Subgroup H).map H.subtype
  mem_center : z ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype
  involution : orderOf z = 2

/-- The source Sylow selection supplies the full ambient context; uniqueness
is transported from the initial Sylow subgroup to the selected one inside M. -/
theorem exists_mathieuSourceSetup (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T₀ : Subgroup G) ≤ K → K = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    {U HU : Subgroup G} (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (hLH : L ≤ H) (hL : IsComponent H (L.subgroupOf H)) :
    ∃ T : Sylow 2 G,
      ∀ z ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype, orderOf z = 2 →
        ∃ c : MathieuSourceSetup H L M S z, c.T = T := by
  obtain ⟨T, hT, hST, hZS, _⟩ := lemma_2_3_9_3 T₀ hTM hunique
    (Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T₀ M hM hTM)) hH hpair S hUS
  have huniq : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M := by
    intro K hK hTK
    have hKM : K ≤ M := by
      apply core_overgroup_le_of_sylow T₀ hTM hunique
        (Chapter1.mem_H_of_isTwoLocal hK.1) (T.subtype hT)
      simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hT] using hTK
    exact le_antisymm hKM (hK.2 hM.1 hKM)
  refine ⟨T, ?_⟩
  intro z hz hzi
  exact ⟨⟨T, hM, hT, huniq, hH, U, HU, hpair, hUS, hLH, hL,
    hST, hZS, hz, hzi⟩, rfl⟩

/-- Recover the common component input from genuine earlier source
implications, without adding any central-cover conclusion to the context. -/
theorem MathieuSourceSetup.localSetup (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE C G) (source115 : Structural115Input G)
    (sourceC : LocalC129Input C G) : LocalSetup H L M S z := by
  have hzS := c.center_le c.mem_center
  have hcentral : ∀ s ∈ (S : Subgroup H).map H.subtype, s * z = z * s := by
    intro s hs
    obtain ⟨a, ha, he⟩ := c.mem_center
    rw [← he]
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨s, c.sylow_lt.le hs⟩)
  have hMc : ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M).map M.subtype, x * z = z * x := by
    refine ⟨c.T.subtype c.sylow_le, ?_⟩
    intro x hx
    have hxT : x ∈ (c.T : Subgroup G) := by
      simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le c.sylow_le] using hx
    obtain ⟨a, ha, he⟩ := c.mem_center
    rw [← he]
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨x, hxT⟩)
  have hh := componentRefinement_localSetup_of_sources hG source115 sourceC c.T
    c.maximal c.sylow_le c.unique c.gamma c.pair S c.base_le c.involution
    hzS hcentral hMc (L.subgroupOf H) c.component
  simpa only [map_subgroupOf_eq_of_le c.component_le] using hh

/-- Source M₁₁ cover and intersection, conditional only on the displayed
earlier source implications and the actual model/action input of 1.1.5(3)(f). -/
theorem MathieuSourceSetup.mathieuEleven_intersection
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (source115 : Structural115Input G) (sourceC : LocalC129Input C G)
    (d : SporadicQuotientInput L z .m11) :
    pCore 2 L = ⊥ ∧ ∃ eL : L ≃* M11,
      (∀ x : L, eL x = d.quotientIso (QuotientGroup.mk' (pCore 2 L) x)) ∧
      ∃ t : L, orderOf t = 2 ∧ IsConjugationProjection L z t ∧
        L ⊓ M = L ⊓ centralizer ({(t : G)} : Set G) :=
  mathieuEleven_cover_intersection (c.localSetup hG source115 sourceC) d

/-- Source M₂₃ cover and heptad intersection, with the original quotient
map and the actual elementary kernel and alternating quotient. -/
theorem MathieuSourceSetup.mathieuTwentyThree_intersection
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (source115 : Structural115Input G) (sourceC : LocalC129Input C G)
    (d : SporadicQuotientInput L z .m23) :
    pCore 2 L = ⊥ ∧ ∃ eL : L ≃* M23,
      (∀ x : L, eL x = d.quotientIso (QuotientGroup.mk' (pCore 2 L) x)) ∧
      (∃ B ∈ m23Blocks,
        (M.subgroupOf L).map eL.toMonoidHom = MulAction.stabilizer M23 B) ∧
      AlternatingBySixteen (M.subgroupOf L) 7 :=
  mathieuTwentyThree_cover_intersection (c.localSetup hG source115 sourceC) d

/-- A nontrivial component two-kernel cannot be normalized by the actual
selected T. This is an obstruction, not the missing normalization theorem. -/
theorem MathieuSourceSetup.twoCore_not_normalized_by_T
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (source115 : Structural115Input G) (sourceC : LocalC129Input C G)
    (hk : pCore 2 L ≠ ⊥) :
    ¬ (c.T : Subgroup G) ≤ normalizer (twoCore L : Set G) := by
  have hh := (c.localSetup hG source115 sourceC).twoCore_not_normalized_by_sylow
    c.T c.sylow_le c.unique (c.T.subtype c.sylow_le) hk
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le c.sylow_le] using hh

end CFSG.Quasithin.Chapter2.ComponentRefinement
end
