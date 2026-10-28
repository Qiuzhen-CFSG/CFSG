module
public import Theory.Mathieu.M12.ValueBoundParabolics.SecondQuotient
public import Theory.Mathieu.M12.ValueBoundParabolics.SmallQuotient
public import Theory.Mathieu.M12.Properties.SylowAutomorphisms

/-!
# A generating pair with S₃ two-core quotients in M₁₂

The two marked parabolics contain the common Sylow subgroup. The existing
Sylow-and-cubics generation theorem proves their join is M₁₂, and their
intrinsic two-core quotients are S₃. Sylow conjugacy gives the pair for every
Sylow subgroup. An actual group equivalence transports the pair, containment,
generation and both quotient identifications together.

These are the simple-model local inputs for Aschbacher–Smith, E.4.3(1),
printed p.241 (PDF p.252). This does not identify a quasisimple central cover
with M₁₂ or construct the overgroups in an outer extension.
-/

public section
noncomputable section
open Subgroup
namespace Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics

/-- The two marked parabolics generate the actual Witt-design group. -/
theorem parabolic_sup_eq_top : firstParabolic ⊔ secondParabolic = ⊤ :=
  SylowAutomorphisms.eq_top_of_contains_sylow_and_cubics _
    (inf_le_left.trans le_sup_left) (mem_sup_left cubicActor_mem)
    (mem_sup_right movingActor_mem)

/-- Each Sylow two-subgroup of M₁₂ lies in a generating pair with intrinsic
two-core quotients S₃. -/
theorem exists_pair (T : Sylow 2 M12) :
    ∃ H K : Subgroup M12,
      (T : Subgroup M12) ≤ H ∧ (T : Subgroup M12) ≤ K ∧ H ⊔ K = ⊤ ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 commonSylow T
  let e := MulAut.conj g
  refine ⟨firstParabolic.map e.toMonoidHom, secondParabolic.map e.toMonoidHom,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hg]
    exact map_mono (show sylowCandidate ≤ firstParabolic from inf_le_left)
  · rw [← hg]
    exact map_mono (show sylowCandidate ≤ secondParabolic from inf_le_right)
  · rw [← Subgroup.map_sup, parabolic_sup_eq_top, map_top_of_surjective _ e.surjective]
  · let f := (e.subgroupMap firstParabolic).symm
    exact ⟨(QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans firstCoreQuotient⟩
  · let f := (e.subgroupMap secondParabolic).symm
    exact ⟨(QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans secondCoreQuotient⟩

/-- Transport through an actual group equivalence, including the specified
Sylow subgroup and the intrinsic cores of both overgroups. -/
theorem exists_pair_of_equiv {G : Type*} [Group G]
    (e : G ≃* M12) (T : Sylow 2 G) :
    ∃ H K : Subgroup G,
      (T : Subgroup G) ≤ H ∧ (T : Subgroup G) ≤ K ∧ H ⊔ K = ⊤ ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) := by
  let _ : Finite G := Finite.of_equiv M12 e.symm.toEquiv
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨H, K, hH, hK, hgen, ⟨eH⟩, ⟨eK⟩⟩ := exists_pair T'
  refine ⟨H.map e.symm.toMonoidHom, K.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨e x, hH (mem_map_of_mem e.toMonoidHom hx), e.symm_apply_apply x⟩
  · intro x hx
    exact ⟨e x, hK (mem_map_of_mem e.toMonoidHom hx), e.symm_apply_apply x⟩
  · rw [← Subgroup.map_sup, hgen, map_top_of_surjective _ e.symm.surjective]
  · let f := (e.symm.subgroupMap H).symm
    exact ⟨(QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans eH⟩
  · let f := (e.symm.subgroupMap K).symm
    exact ⟨(QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans eK⟩

end Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics
