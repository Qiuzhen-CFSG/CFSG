module

public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Faithful
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# The maximal nonquasisimple source choice in 13.1

The finite local family has a maximal overgroup. Normality of the original
odd radical in that overgroup rules out a quasisimple two-core quotient.
A.3.8 gives T-invariance of the original component, and uniqueness of
containing C-components propagates invariance to the overgroup. The two
Sylow normalizers consequently agree, so A.4.10 propagates faithfulness.

The only remaining source inputs are the universal A.3.6, A.3.8 and A.4.10
implications and the normality of the original Ξₚ(L) in its local overgroups.
The latter is exactly the nonnormal-embedding exclusion in 13.1.4, using
1.3.4 and 13.1.2(3); it is not a quasisimple classification assumption.
The ambient quotient SQTK hypotheses are discharged from the original
simple QTKE group with the full known-simple catalogue.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
13.1.4 and the initial counterexample choice for 13.1.7, pp.867--868.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.Adequate

namespace CFSG.Quasithin.Chapter13.Section01
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal family L⁺(G,T), with quotient by each member's own two-core. -/
def nonquasisimpleFaithful (T : Sylow 2 G) : Set (Subgroup G) :=
  {L | L ∈ MainForward.faithfulLocalComponents T ∧
    ¬ IsQuasisimple (XiQuotient L)}

/-- The source ambient hypotheses supply both quotient SQTK conditions in
the normal-radical inference. -/
theorem source_overgroup_not_quasisimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → A36Conclusion C)
    {T : Sylow 2 G} {L₀ K : Subgroup G}
    (hL : L₀ ∈ nonquasisimpleFaithful T) (hK : K ∈ L G T) (hLK : L₀ ≤ K)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)))
    (hN : ((XiP p L₀).subgroupOf K).Normal) :
    ¬ IsQuasisimple (XiQuotient K) := by
  have hl := ((mem_faithfulLocalComponents_iff T L₀).mp hL.1).1
  exact overgroup_not_quasisimple_of_XiP_normal hA36 hl hK
    (uniqueness_local_quotient_sqtk hG hl.2.2)
    (uniqueness_local_quotient_sqtk hG hK.2.2) hL.2 hLK ho hd hN

/-- Choose the actual maximal faithful nonquasisimple overgroup. The source
normality producer is uniform in overgroups of this same L and same radical;
no replacement of the component or its quotient map is made. -/
theorem exists_maximal_nonquasisimple_overgroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    (hA410 : A410EarlierResult G)
    {T : Sylow 2 G} {L₀ : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)))
    (hN : ∀ K ∈ L G T, L₀ ≤ K → ((XiP p L₀).subgroupOf K).Normal) :
    ∃ K ∈ LStar G T, L₀ ≤ K ∧ K ∈ nonquasisimpleFaithful T ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ((XiP p L₀).subgroupOf K).Normal := by
  have hl := ((mem_faithfulLocalComponents_iff T L₀).mp hL.1).1
  obtain ⟨K, hK, hLK⟩ := exists_mem_LStar_ge hl
  have hTK₀ : (T : Subgroup G) ≤ normalizer (L₀ : Set G) :=
    radicalLocal_invariant_of_A38 hA38 hl
      (uniqueness_local_quotient_sqtk hG hl.2.2) hL.2
  have hTK := local_chain_normalizes hl hK.1 hLK hTK₀
  have hnorm : (T : Subgroup G) ⊓ normalizer (L₀ : Set G) =
      (T : Subgroup G) ⊓ normalizer (K : Set G) := by
    rw [inf_eq_left.mpr hTK₀, inf_eq_left.mpr hTK]
  have hf := (faithful_chain_of_A410_of_normalizer_eq T (hG.evenCharacteristic T)
    hA410 hL.1 hK.1 hLK hnorm).2
  exact ⟨K, hK, hLK, ⟨hf, source_overgroup_not_quasisimple hG hA36 hL hK.1 hLK
    ho hd (hN K hK.1 hLK)⟩, hTK, hN K hK.1 hLK⟩

end CFSG.Quasithin.Chapter13.Section01
