module

public import Theory.Mathieu.M12.ValueBoundParabolics
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Amalgam

/-!
# Two-member generating pairs in M₁₂ and Aut(M₁₂)

The checked simple and outer parabolics each contain a common Sylow subgroup,
generate their ambient model, and have intrinsic two-core quotients S₃.
Their intersection orders prove that the two members are distinct. Sylow
conjugacy and actual group equivalences transport all these facts together
to any prescribed Sylow subgroup.

This is the two-member family used in Aschbacher–Smith E.4.3(1), printed
p.241 (PDF p.252). Only containment, generation and the quotient shapes are
needed for the bound; no maximal-subgroup classification is assumed.
-/

public section
noncomputable section
open Subgroup
namespace Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics

private theorem pair_transport {M G : Type*} [Group M] [Finite M] [Group G]
    (S : Sylow 2 M) (H K : Subgroup M) (hne : H ≠ K)
    (hH : (S : Subgroup M) ≤ H) (hK : (S : Subgroup M) ≤ K)
    (hgen : H ⊔ K = ⊤)
    (eH : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))
    (eK : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3))
    (e : G ≃* M) (T : Sylow 2 G) :
    ∃ A B : Subgroup G, A ≠ B ∧
      (T : Subgroup G) ≤ A ∧ (T : Subgroup G) ≤ B ∧ A ⊔ B = ⊤ ∧
      Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) := by
  let _ : Finite G := Finite.of_equiv M e.symm.toEquiv
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M S T'
  let c := MulAut.conj g
  let f := c.trans e.symm
  have hTc : (T' : Subgroup M) = (S : Subgroup M).map c.toMonoidHom := by
    rw [← hg]
    rfl
  have hcontains (J : Subgroup M) (hJ : (S : Subgroup M) ≤ J) :
      (T : Subgroup G) ≤ J.map f.toMonoidHom := by
    intro x hx
    have hx' : e x ∈ (S : Subgroup M).map c.toMonoidHom :=
      hTc ▸ mem_map_of_mem e.toMonoidHom hx
    obtain ⟨y, hy, he⟩ := hx'
    refine ⟨y, hJ hy, ?_⟩
    change e.symm (c y) = x
    change c y = e x at he
    rw [he, e.symm_apply_apply]
  refine ⟨H.map f.toMonoidHom, K.map f.toMonoidHom,
    fun h => hne (Subgroup.map_injective f.injective h),
    hcontains H hH, hcontains K hK, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, hgen, map_top_of_surjective _ f.surjective]
  · let a := (f.subgroupMap H).symm
    exact ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eH⟩
  · let a := (f.subgroupMap K).symm
    exact ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eK⟩

/-- The two simple-model overgroups are distinct. -/
theorem parabolics_ne : firstParabolic ≠ secondParabolic := by
  intro heq
  have he : sylowCandidate = secondParabolic := by
    change firstParabolic ⊓ secondParabolic = secondParabolic
    rw [heq, inf_idem]
  have h := card_sylowCandidate
  rw [he, card_secondParabolic] at h
  omega

/-- The simple-model pair, retaining that it has two different members. -/
theorem exists_distinct_pair_of_equiv {G : Type*} [Group G]
    (e : G ≃* M12) (T : Sylow 2 G) :
    ∃ H K : Subgroup G, H ≠ K ∧
      (T : Subgroup G) ≤ H ∧ (T : Subgroup G) ≤ K ∧ H ⊔ K = ⊤ ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) :=
  pair_transport commonSylow firstParabolic secondParabolic parabolics_ne
    inf_le_left inf_le_right parabolic_sup_eq_top firstCoreQuotient secondCoreQuotient e T

namespace Extension
open Sporadic.Mathieu.M12ExceptionalExtension

/-- The two outer-model overgroups are distinct. -/
theorem parabolics_ne : M12ExceptionalExtension.firstParabolic ≠
    M12ExceptionalExtension.secondParabolic := by
  intro heq
  have he : overlap = M12ExceptionalExtension.secondParabolic := by
    change M12ExceptionalExtension.firstParabolic ⊓
      M12ExceptionalExtension.secondParabolic = M12ExceptionalExtension.secondParabolic
    rw [heq, inf_idem]
  have h := SecondCoordinates.card_overlap innerModel
  rw [he, SecondCoordinates.card_secondParabolic innerModel] at h
  omega

/-- The actual full automorphism extension has two distinct generating Sylow
 overgroups with their own intrinsic S₃ quotients. -/
theorem exists_pair_of_equiv {G : Type*} [Group G]
    (e : G ≃* Carrier) (T : Sylow 2 G) :
    ∃ H K : Subgroup G, H ≠ K ∧
      (T : Subgroup G) ≤ H ∧ (T : Subgroup G) ≤ K ∧ H ⊔ K = ⊤ ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) :=
  pair_transport VerifiedPair.commonSylow
    M12ExceptionalExtension.firstParabolic M12ExceptionalExtension.secondParabolic
    parabolics_ne inf_le_left inf_le_right
    (SecondCoordinates.parabolic_sup_eq_top innerModel)
    (FirstParabolic.firstParabolicPcoreQuotient innerModel)
    (SecondCoordinates.secondCoreQuotient innerModel) e T

end Extension
end Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics
