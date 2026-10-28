module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.FittingActions.HigherHomocyclic
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.LocalNormality

/-!
# The source higher-core prime bound on the original local quotient

Apply complete A.3.6 to the actual component image in LT/O₂(LT).
The inclusion-induced quotient equivalence carries its prime core to
O_p(L/O₂(L)). The higher homocyclic action argument therefore gives
p>5 and the actual higher homocyclic coordinates on this original core.
No model classification or prime lower bound is assumed.

Source: Aschbacher--Smith 3.2.14, p.585.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3.RadicalCentralization
open Chapter1 Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

theorem local_higher_core_structure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (hexp : ¬ ∀ x : pCore p (XiQuotient L), x ^ p = 1) :
    5 < p ∧ ∃ a : ℕ, 2 ≤ a ∧
      Nonempty (pCore p (XiQuotient L) ≃* Multiplicative (Fin 2 → ZMod (p^a))) := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun (A : Type u) _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun (A : Type u) _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have hQ := uniqueness_local_quotient_sqtk hG hL.2.2
  have hc := proposition_1_2_1_four_earlier_conclusion h36 hQ hL.1
  let e := radicalLocalQuotientEquiv hL
  let ep : pCore p (XiQuotient L) ≃* pCore p (radicalLocalImage T L) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso p e))
  have hnC : ¬ IsQuasisimple (radicalLocalImage T L) :=
    fun h => hn (h.of_mulEquiv e.symm)
  have hnp : ¬ ∀ x : pCore p (radicalLocalImage T L), x ^ p = 1 := by
    intro he
    apply hexp
    intro x
    apply ep.injective
    simpa only [map_pow,map_one] using he (ep x)
  let : Group.IsNilpotent (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) := pCore_isNilpotent
  obtain ⟨hp,a,ha,⟨ea⟩⟩ := FittingActions.higher_core_structure
    (hL.1.map_quotient _) hc hnC hnp
  exact ⟨hp,a,ha,⟨ep.trans ea⟩⟩

end CFSG.Quasithin.Chapter3.RadicalCentralization
