module
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.SubgroupCoverTransport

/-!
# Index of the original parabolic in the linear-three quotient

In a finite group with full two-core quotient PSL₃(2), every maximal
proper subgroup containing the specified Sylow two-subgroup has index
seven. The whole two-core is contained in that Sylow subgroup, so both
maximality and index pass through the literal quotient map. The two
parabolics in the quotient have order 24 in the group of order 168.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource

variable {A : Type*} [Group A] [Finite A]

/-- A maximal overgroup of the original Sylow subgroup has the Fano-plane
index when the full two-core quotient is PSL₃(2). -/
theorem maximal_sylow_overgroup_index_seven
    (e : (A ⧸ pCore 2 A) ≃* Matrix.PSL3Two.PSL)
    (S : Sylow 2 A) (P : Subgroup A)
    (hSP : (S : Subgroup A) ≤ P) (hmax : IsCoatom P) : P.index = 7 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hq : Function.Surjective q :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 A := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkP : q.ker ≤ P :=
    hk ▸ (pCore_isPGroup.le_sylow_of_normal S).trans hSP
  let S' := S.mapSurjective hq
  have hSP' : (S' : Subgroup Matrix.PSL3Two.PSL) ≤ P.map q := map_mono hSP
  have hmax' : IsCoatom (P.map q) :=
    isCoatom_map_of_surjective_of_ker_le q hq P hkP hmax
  obtain ⟨B,C,_,_,_,_,hB,hC,hall⟩ := Matrix.PSL3Two.sylow_parabolics S'
  have hcard : Nat.card (P.map q) = 24 := by
    rcases (hall (P.map q) hmax').mp hSP' with h | h
    · rw [h]
      exact hB
    · rw [h]
      exact hC
  have hcount := (P.map q).card_mul_index
  rw [hcard,Matrix.PSL3Two.card_PSL,P.index_map_eq hq hkP] at hcount
  omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource
