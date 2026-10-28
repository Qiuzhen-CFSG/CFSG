module

public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups
public import Theory.GroupTheory.UniqueMaximalNormalExtension

/-!
# The unique Sylow overgroup in alternating five

The identification A₅ = SL₂(4) transports rank-one Borel uniqueness to
every Sylow four-group. Its normalizer is a point stabilizer of index five,
so this particular subgroup is the unique maximal overgroup. The result
lifts through the full two-core of an arbitrary marked A₅ section.

Source application: Aschbacher–Smith, 10.1.2(6), printed p.742.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.Alternating.FiveSylowMaximal

theorem sylow_unique (S : Sylow 2 (alternatingGroup (Fin 5))) :
    Order.HasUniqueMaximalOver (S : Subgroup (alternatingGroup (Fin 5))) ⊤ := by
  obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
  let f := (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2)).trans e
  apply hasUniqueMaximalOver_of_surjective f.symm.toMonoidHom f.symm.surjective
    (by rw [f.symm.toMonoidHom.ker_eq_bot f.symm.injective]; exact bot_le)
  exact Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver 2
    (S.mapSurjective f.symm.surjective)

private theorem stabilizer_card (i : Fin 5) :
    Nat.card (MulAction.stabilizer (alternatingGroup (Fin 5)) i) = 12 := by
  rw [Nat.card_eq_fintype_card]
  revert i
  decide +kernel

theorem sylow_normalizer_isCoatom (S : Sylow 2 (alternatingGroup (Fin 5))) :
    IsCoatom (normalizer (S : Set (alternatingGroup (Fin 5)))) := by
  obtain ⟨i, hi⟩ := FiveBorelOvergroups.sylow_normalizer_eq_stabilizer S
  rw [hi]
  have hi : (MulAction.stabilizer (alternatingGroup (Fin 5)) i).index = 5 := by
    have hc := (MulAction.stabilizer (alternatingGroup (Fin 5)) i).card_mul_index
    rw [stabilizer_card, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
    omega
  refine ⟨?_, ?_⟩
  · intro he
    simp [he] at hi
  · intro K hK
    have hd := index_dvd_of_le hK.le
    rw [hi] at hd
    rcases (Nat.dvd_prime Nat.prime_five).mp hd with he | he
    · exact index_eq_one.mp he
    · have := index_strictAnti hK
      omega

theorem overgroup_le_sylow_normalizer
    (S : Sylow 2 (alternatingGroup (Fin 5)))
    (H : Subgroup (alternatingGroup (Fin 5)))
    (hS : (S : Subgroup (alternatingGroup (Fin 5))) ≤ H) (hH : H ≠ ⊤) :
    H ≤ normalizer (S : Set (alternatingGroup (Fin 5))) :=
  (sylow_unique S).le_maximal
    ⟨(show (S : Subgroup (alternatingGroup (Fin 5))) ≤
      normalizer (S : Set (alternatingGroup (Fin 5))) from S.toSubgroup.le_normalizer),
      (sylow_normalizer_isCoatom S).covBy_top⟩
    hS (lt_top_iff_ne_top.mpr hH)

variable {A : Type*} [Group A] [Finite A]

/-- The full two-core can be retained in the original A₅ section. -/
theorem core_quotient_sylow_unique (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 A) : Order.HasUniqueMaximalOver (S : Subgroup A) ⊤ := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  apply hasUniqueMaximalOver_of_surjective f hf ?_ (sylow_unique (S.mapSurjective hf))
  have hk : f.ker = pCore 2 A := by
    ext a
    change e (QuotientGroup.mk' (pCore 2 A) a) = 1 ↔ a ∈ pCore 2 A
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff a
  rw [hk]
  exact pCore_isPGroup.le_sylow_of_normal S

end Theory.SpecificGroups.Alternating.FiveSylowMaximal
