module
public import CFSG.Quasithin.ChapterE.Section04.GenerationSetup
public import Theory.Mathieu.M12.ValueBoundParabolics
public import Theory.Mathieu.M12.ValueBoundParabolics.Supplement
public import Theory.Mathieu.M12.ValueBoundParabolics.ComponentReduction
public import Theory.Mathieu.M12.ValueBoundParabolics.CentralCovers
public import Theory.Mathieu.M12.ValueBoundParabolics.Ambient
public import Theory.Mathieu.M12.ValueBoundParabolics.ExtensionPair

/-!
# The M₁₂ generating-family construction for E.4.3(1)

The concrete M₁₂ parabolics generate the group and have intrinsic two-core
quotients S₃. Their two-element family satisfies E.4.2's local condition:
each quotient has generalized Fitting subgroup of order three and two-rank
at most one. The construction retains the prescribed Sylow subgroup and
transports along actual group equivalences.

For a quasisimple L = F*(G) with L/Z(L) ≃ M₁₂ and O₂(G) = 1, the
central-cover theorem removes Z(L). Component theory makes conjugation on L
faithful, and the outer two-group restriction proves G = LT. The conjugation
image is either the marked inner M₁₂ or the full automorphism carrier; the
checked pair in the corresponding model then supplies the ambient family.
`m12_exists_s3_pair` retains both quotient equivalences, distinctness, Sylow
containment and generation before `m12_generatingFamily` forms the finite
family. No representation bound is assumed. The construction uses precisely
the generating-overgroup properties required by E.4.2, without needing a
classification of all maximal overgroups.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.3(1),
printed pp.241–242 (PDF pp.252–253). As in `GenerationSetup`, the local
condition is F*(H/O₂(H)), as used in the source proof.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterE.ValueBound
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics

/-- An actual S₃ two-core quotient satisfies the source local condition. -/
theorem isLocalOvergroup_of_quotient_equiv_s3 {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :
    IsLocalOvergroup H := by
  right
  rw [generalizedFitting_card_of_equiv_s3 e]
  exact Nat.prime_three

/-- Two actual Sylow overgroups generating G, each with intrinsic two-core
quotient S₃, give the required family and a budget at most two. -/
theorem generatingFamily_of_s3_pair {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (H K : Subgroup G)
    (hH : (T : Subgroup G) ≤ H) (hK : (T : Subgroup G) ≤ K)
    (hgen : H ⊔ K = ⊤)
    (eH : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))
    (eK : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) :
    ∃ Δ : Finset (Subgroup G), IsGeneratingFamily T Δ ∧ localRankBudget Δ ≤ 2 := by
  classical
  refine ⟨{H, K}, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro J hJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hJ
    rcases hJ with rfl | rfl
    · exact hH
    · exact hK
  · simpa only [Finset.coe_insert, Finset.coe_singleton, sSup_pair] using hgen
  · intro J hJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hJ
    rcases hJ with rfl | rfl
    · exact isLocalOvergroup_of_quotient_equiv_s3 _ eH
    · exact isLocalOvergroup_of_quotient_equiv_s3 _ eK
  · have h1 := primeRank_two_le_one_of_equiv_s3 eH
    have h2 := primeRank_two_le_one_of_equiv_s3 eK
    by_cases heq : H = K
    · subst K
      simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self H),
        localRankBudget, Finset.sum_singleton] using h1.trans (by decide : 1 ≤ 2)
    · rw [localRankBudget, Finset.sum_insert (by simpa using heq), Finset.sum_singleton]
      omega

/-- The E.4.3(1) generating-family conclusion for a group actually isomorphic
to M₁₂; the full ambient conclusion is `m12_generatingFamily` below. -/
theorem m12_generatingFamily_of_equiv {G : Type*} [Group G] [Finite G]
    (e : G ≃* Sporadic.Mathieu.M12) (T : Sylow 2 G) :
    ∃ Δ : Finset (Subgroup G), IsGeneratingFamily T Δ ∧ localRankBudget Δ ≤ 2 := by
  obtain ⟨H, K, hH, hK, hgen, ⟨eH⟩, ⟨eK⟩⟩ := exists_pair_of_equiv e T
  exact generatingFamily_of_s3_pair T H K hH hK hgen eH eK

/-- Once the actual component is M₁₂, its generalized-Fitting property
discharges the centralizer hypothesis in the Sylow-supplement argument. -/
theorem m12_sup_sylow_of_generalizedFitting_equiv {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [IsQuasisimple L] (hL : generalizedFitting G = L)
    (e : L ≃* Sporadic.Mathieu.M12) (T : Sylow 2 G) :
    L ⊔ (T : Subgroup G) = ⊤ := by
  let _ := Sporadic.Mathieu.m12_isSimpleGroup
  let _ : IsSimpleGroup L := e.isSimpleGroup
  let _ : L.Normal := hL ▸ inferInstance
  exact sup_sylow_eq_top_of_equiv L e
    (centralizer_eq_bot_of_simple_generalizedFitting L hL) T

/-- The centerless reduction, before the central-cover theorem discharges
triviality of Z(L) in `m12_component_equiv_and_sup`. -/
theorem m12_component_equiv_and_sup_of_center_eq_bot
    {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [IsQuasisimple L] (hL : generalizedFitting G = L)
    (e : (L ⧸ center L) ≃* Sporadic.Mathieu.M12) (hZ : center L = ⊥)
    (T : Sylow 2 G) :
    Nonempty (L ≃* Sporadic.Mathieu.M12) ∧ L ⊔ (T : Subgroup G) = ⊤ := by
  let eL : L ≃* Sporadic.Mathieu.M12 :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  exact ⟨⟨eL⟩, m12_sup_sylow_of_generalizedFitting_equiv L hL eL T⟩

/-- The ambient two-core hypothesis removes the center of the quasisimple
component, and the faithful outer action gives the required Sylow supplement. -/
theorem m12_component_equiv_and_sup
    {G : Type*} [Group G] [Finite G] (hcore : pCore 2 G = ⊥)
    (L : Subgroup G) [IsQuasisimple L] (hL : generalizedFitting G = L)
    (e : (L ⧸ center L) ≃* Sporadic.Mathieu.M12) (T : Sylow 2 G) :
    Nonempty (L ≃* Sporadic.Mathieu.M12) ∧ L ⊔ (T : Subgroup G) = ⊤ := by
  let _ : L.Normal := hL ▸ inferInstance
  exact m12_component_equiv_and_sup_of_center_eq_bot L hL e
    (CentralCovers.center_eq_bot (pCore_eq_bot_of_normal 2 hcore L) e) T

/-- The actual two-member source family for every permitted central cover and
outer extension. Both intrinsic S₃ quotient equivalences, the prescribed
Sylow containment and generation are retained for the module-bound consumer. -/
theorem m12_exists_s3_pair
    {G : Type*} [Group G] [Finite G] (hcore : pCore 2 G = ⊥)
    (L : Subgroup G) [IsQuasisimple L] (hL : generalizedFitting G = L)
    (e : (L ⧸ center L) ≃* Sporadic.Mathieu.M12) (T : Sylow 2 G) :
    ∃ H K : Subgroup G, H ≠ K ∧
      (T : Subgroup G) ≤ H ∧ (T : Subgroup G) ≤ K ∧ H ⊔ K = ⊤ ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨⟨eL⟩, _⟩ := m12_component_equiv_and_sup hcore L hL e T
  let _ := Sporadic.Mathieu.m12_isSimpleGroup
  let _ : IsSimpleGroup L := eL.isSimpleGroup
  let _ : L.Normal := hL ▸ inferInstance
  rcases Ambient.ambient_equiv_alternatives L
      (centralizer_eq_bot_of_simple_generalizedFitting L hL) eL with
    ⟨_, ⟨f⟩⟩ | ⟨f, _⟩
  · exact exists_distinct_pair_of_equiv f T
  · exact Extension.exists_pair_of_equiv f T

/-- The E.4.3(1) generating-family conclusion, with all central-cover and
outer-extension premises discharged from the genuine source hypotheses. -/
theorem m12_generatingFamily
    {G : Type*} [Group G] [Finite G] (hcore : pCore 2 G = ⊥)
    (L : Subgroup G) [IsQuasisimple L] (hL : generalizedFitting G = L)
    (e : (L ⧸ center L) ≃* Sporadic.Mathieu.M12) (T : Sylow 2 G) :
    ∃ Δ : Finset (Subgroup G), IsGeneratingFamily T Δ ∧ localRankBudget Δ ≤ 2 := by
  obtain ⟨H, K, _, hH, hK, hgen, ⟨eH⟩, ⟨eK⟩⟩ :=
    m12_exists_s3_pair hcore L hL e T
  exact generatingFamily_of_s3_pair T H K hH hK hgen eH eK


end CFSG.Quasithin.ChapterE.ValueBound
