module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Geometry
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Setup
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# Common action deductions for rank-one components

Once the actual Sylow normalizer equals L ∩ M, its odd complement acts
coprimely on V, while its Sylow subgroup centralizes V. The coprime splitting
therefore decomposes V into [V,L ∩ M] and C_V(L ∩ M), with disjoint factors.
This uses only proved Sylow-normalizer structure and the genuine local action.

The remaining concrete model calculation must identify C_V(L ∩ M) with
C_V(L), compute the displacement order, and identify the actual induced
cyclic image. `ActionCalculation` specifies precisely these remaining facts.
The conditional assembly proves all other Borel-alternative clauses, including
the exact corank and its bound. Neither Borel placement nor the model
calculation is asserted by that conditional theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(1),
printed pp.247–248 (PDF pp.258–259), referring to the coprime splitting
argument in E.6.7 on printed p.246.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G} {n : ℕ}

/-- Output required from the concrete model action proof. This contains no
Borel-placement, direct-decomposition, or corank premise. The assembly owner
must construct both placement and this calculation before claiming E.6.8. -/
structure ActionCalculation (M V L : Subgroup G) (n : ℕ) : Prop where
  fixed : V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G) =
    V ⊓ centralizer (L : Set G)
  displacement_order : Nat.card (⁅V, L ⊓ M⁆ : Subgroup G) = 2 ^ n
  cyclic_image : Nonempty
    (inducedAutomizer V (L ⊓ M) ≃* Multiplicative (ZMod (2 ^ n - 1)))

/-- Coprime splitting for the actual Borel intersection. Identifying the
fixed factor here with C_V(L) is a separate model calculation. -/
theorem intersection_decomposition
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : Model L n) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hB : sylowBorel S = L ⊓ M) :
    DirectDecomposition V ⁅V, L ⊓ M⁆
      (V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G)) := by
  let _ := h.elementary
  have hN := component_intersection_normalizes h hU hL.1
  obtain ⟨D, _, hodd, _, _, hgenD⟩ := (hm.sylowFacts S).abelian_odd_complement
  let A := (S : Subgroup L).map L.subtype
  let X := D.map L.subtype
  have hgen : A ⊔ X = L ⊓ M := by
    change (S : Subgroup L).map L.subtype ⊔ D.map L.subtype = _
    rw [← Subgroup.map_sup, hgenD]
    exact hB
  have hAC : A ≤ centralizer (V : Set G) := by
    change (S : Subgroup L).map L.subtype ≤ _
    rw [hS]
    exact inf_le_right.trans inf_le_right
  have hXB : X ≤ L ⊓ M := hgen ▸ le_sup_right
  have hXN : X ≤ normalizer (V : Set G) := hXB.trans hN
  have hcop : Nat.Coprime (Nat.card X) (Nat.card V) := by
    obtain ⟨d, hd⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hd]
    apply Nat.Coprime.pow_right
    simpa only [X, card_map_of_injective L.subtype_injective] using hodd.symm
  have hcomm : ⁅V, X⁆ = ⁅V, L ⊓ M⁆ :=
    commutator_eq_of_centralizing_sup hgen hAC hXN
  have hfixed : V ⊓ centralizer (X : Set G) =
      V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G) := by
    apply le_antisymm
    · apply le_inf inf_le_left
      apply le_centralizer_iff.mpr
      rw [← hgen]
      exact sup_le (hAC.trans (centralizer_le inf_le_left))
        (le_centralizer_iff.mp inf_le_right)
    · exact inf_le_inf_left V (centralizer_le hXB)
  have hsolv : Group.IsSolvable V := Group.isSolvable_of_comm fun x y => mul_comm x y
  have hjoin := eq_commutator_sup_centralizer_of_solvable_coprime V X hXN hsolv hcop
  have hdis := commutator_disjoint_centralizer_of_coprime V X hXN hcop
  rw [hcomm, hfixed] at hjoin hdis
  refine ⟨hjoin.symm, disjoint_iff.mp hdis, ?_⟩
  apply le_bot_iff.mp
  have hv : ⁅V, L ⊓ M⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hN
  exact (commutator_mono hv inf_le_left).trans
    (commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative V)).le

/-- The already proved proper-overgroup bound supplies one direction;
the independently required Borel placement supplies the other. -/
theorem sylowBorel_eq_intersection_of_le
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : Model L n) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hplace : sylowBorel S ≤ M) : sylowBorel S = L ⊓ M :=
  le_antisymm (le_inf (sylowBorel_le S) hplace)
    (intersection_le_sylowBorel h earlier hU hL hm S hS)

/-- Conditional assembly from Borel placement and the three concrete action
calculations. Coprime splitting gives both decomposition clauses; counting its
disjoint factors gives the exact action corank, and U ≤ C_V(L) gives the bound.
The source-theorem owner must still discharge `hplace` and `ha`. -/
theorem borelAlternative_of_calculation
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : Model L n) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hplace : sylowBorel S ≤ M) (ha : ActionCalculation M V L n) :
    BorelAlternative M V U L n := by
  have hB := sylowBorel_eq_intersection_of_le h earlier hU hL hm S hS hplace
  have hd := intersection_decomposition h hU hL hm S hS hB
  rw [ha.fixed] at hd
  have hn : actionCorank V L = n :=
    corank_of_direct_decomposition (by rw [sup_comm]; exact hd.1.symm)
      ((commutator_eq_bot_iff_le_centralizer.mp hd.2.2).trans
        (Subgroup.centralizer_le_normalizer _))
      (disjoint_iff.mpr (by rw [inf_comm]; exact hd.2.1)) ha.displacement_order
  refine ⟨hm.borelComponentModel, hB ▸ sylowBorel_preimage S, ha.cyclic_image,
    hn.symm, ?_, fun _ => hd, fun _ => ?_⟩
  · rw [← hn]
    exact fixedSpace_corank_le hU.1 hL.1
  · simp only [subgroupCorank, relIndex_bot_left, ha.displacement_order,
      Nat.log_pow (by decide : 1 < 2)]

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
