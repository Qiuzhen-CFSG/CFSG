module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.Chapter3.Defs
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The original residual in the tensor overgroup argument

For the original H-star member H, the subgroup K is literally the ambient
image of O²(H). The Sylow supplement gives K T = H, so K escapes the
original maximal local subgroup. An A₅ identification of K/O₂(K) makes
this same K a C-component and hence a member of the original local family.
The stabilizer variant retains the precise Sylow and core-containment
premises used in source 9.3.2; it does not replace K by a selected component.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
9.2.7(3) and 9.3.2–9.3.4, printed pp.730–732. The identification of the
residual quotient in 9.2.7(3) is a separate input to these transport results.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The original two-residual and prescribed Sylow subgroup generate H. -/
theorem source_hstar_residual_sup_sylow {M H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
  let S := T.subtype hH.1.1.2
  have he := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top S)
  change (pResidual 2 H ⊔ (S : Subgroup H)).map H.subtype =
    (⊤ : Subgroup H).map H.subtype at he
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at he
  have hS : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hH.1.1.2
  rwa [hS] at he

/-- Escape belongs to the literal residual, independently of its recognition. -/
theorem source_hstar_residual_not_le {M H : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ (pResidual 2 H).map H.subtype ≤ M := by
  intro hK
  exact hH.1.2 ((source_hstar_residual_sup_sylow hH).symm ▸ sup_le hK hTM)

private theorem residual_cComponent_of_a5_quotient (H : Subgroup G)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5)) :
    (((pResidual 2 H).map H.subtype).subgroupOf H).IsCComponent := by
  let f := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let q := f.toMonoidHom.pCoreQuotientEquiv (p := 2) f.surjective
    (by rw [f.toMonoidHom.ker_eq_bot f.injective]; exact IsPGroup.of_bot)
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) :=
    IsQuasisimple.of_mulEquiv (q.trans eK).symm
  have hC : (pResidual 2 H).IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient
      (inferInstance : (pResidual 2 H).Normal).isSubnormal (isPPerfect_pResidual 2)
  simpa only [subgroupOf, comap_map_eq_self_of_injective H.subtype_injective] using hC

/-- Recognition of the actual quotient supplies all local-family clauses at T. -/
theorem source_hstar_residual_mem_local_of_a5 {M H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5)) :
    (pResidual 2 H).map H.subtype ∈ Chapter1.L G (T : Subgroup G) := by
  exact Chapter1.mem_L_of_cComponent hH.1.1.1
    ⟨T.subtype hH.1.1.2, map_subgroupOf_eq_of_le hH.1.1.2⟩
    (map_subtype_le _) (residual_cComponent_of_a5_quotient H eK)

/-- The same residual is local at a smaller Sylow subgroup once 9.3.2 supplies
the Sylow clause and retains the original nontrivial two-core. -/
theorem source_hstar_residual_mem_local_of_a5_at_subgroup {M H R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (hRT : R ≤ (T : Subgroup G))
    (hSyl : Chapter1.IsSylowIn 2 R ((pResidual 2 H).map H.subtype ⊔ R))
    (hcore : H.pCoreIn 2 ≤ (pResidual 2 H).map H.subtype ⊔ R) :
    (pResidual 2 H).map H.subtype ∈ Chapter1.L G R := by
  have hJH : (pResidual 2 H).map H.subtype ⊔ R ≤ H :=
    sup_le (map_subtype_le _) (hRT.trans hH.1.1.2)
  have hc : H.pCoreIn 2 ≤ ((pResidual 2 H).map H.subtype ⊔ R).pCoreIn 2 :=
    (le_inf hcore le_rfl).trans (inf_pCoreIn_le_of_le 2 hJH)
  exact ⟨(residual_cComponent_of_a5_quotient H eK).subgroupOf_of_le
    le_sup_left hJH, hSyl, fun he => hH.1.1.1 (bot_unique (hc.trans_eq he))⟩

/-- Apply the literal-residual transfer at the original component stabilizer. -/
theorem source_a5_hstar_residual_at_stabilizer {L M H : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      ((pResidual 2 H).map H.subtype ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))
    (hcore : H.pCoreIn 2 ≤ (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G))) :
    (pResidual 2 H).map H.subtype ∈ Chapter1.L G (T : Subgroup G) ∧
    (pResidual 2 H).map H.subtype ∈
      Chapter1.L G ((T : Subgroup G) ⊓ normalizer (L : Set G)) ∧
    ¬ (pResidual 2 H).map H.subtype ≤ M := by
  exact ⟨source_hstar_residual_mem_local_of_a5 hH eK,
    source_hstar_residual_mem_local_of_a5_at_subgroup hH eK inf_le_left hSyl hcore,
    source_hstar_residual_not_le hTM hH⟩

end CFSG.Quasithin.Chapter10
