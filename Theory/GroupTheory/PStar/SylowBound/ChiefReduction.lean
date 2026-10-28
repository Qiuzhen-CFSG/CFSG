module

public import Theory.GroupTheory.PStar.Radical
public import Theory.GroupTheory.PStar.Chief
public import Theory.GroupTheory.PCoreSurjective

/-!
# Chief selection for the p-star Sylow bound

The quotient by the p-core extension of the p-star core has trivial p-core.
Frattini's argument makes the product of a normal subgroup with the centralizer
of one of its Sylow subgroups normal in the ambient group. Any nontrivial normal
subgroup of the quotient therefore contains an actual ambient chief subgroup,
which is p-perfect and p-star.

These are the chief-factor steps in GLS II, Chapter B, Theorem 5.9. The source
proof bounds the centralizer by O_{p*p}; the transcript's O_{p'p} conclusion
is not used here.
-/

public section

open Subgroup Theory.GroupTheory
namespace Subgroup
variable {p : ℕ} {G : Type*} [Group G] [Finite G] [Fact p.Prime]

/-- Factoring out the p-core extension leaves no normal p-subgroup. -/
theorem pCore_quotient_pStarPCore_eq_bot : pCore p (G ⧸ pStarPCore p G) = ⊥ := by
  let R := pStarCore p G
  let N := pStarPCore p G
  let f : G ⧸ R →* G ⧸ N := QuotientGroup.map R N (MonoidHom.id G)
    pStarCore_le_pStarPCore
  have hf : Function.Surjective f := QuotientGroup.map_surjective_of_surjective R N
    (MonoidHom.id G) (QuotientGroup.mk_surjective.comp Function.surjective_id)
    pStarCore_le_pStarPCore
  have hk : f.ker = pCore p (G ⧸ R) := by
    apply comap_injective (QuotientGroup.mk'_surjective R)
    ext x
    change f (QuotientGroup.mk' R x) = 1 ↔ x ∈ N
    exact QuotientGroup.eq_one_iff x
  have hker : IsPGroup p f.ker := hk ▸ pCore_isPGroup
  have hpre := f.comap_pCore_of_ker_isPGroup hf hker
  apply bot_unique
  intro x hx
  obtain ⟨y, rfl⟩ := hf x
  exact MonoidHom.mem_ker.mp ((hpre.trans hk.symm).le hx)

/-- Frattini normality for the literal mapped Sylow centralizer. -/
theorem normal_sup_centralizer_sylow (N : Subgroup G) [N.Normal] (P : Sylow p N) :
    (N ⊔ centralizer ((P : Subgroup N).map N.subtype : Set G)).Normal := by
  let S := (P : Subgroup N).map N.subtype
  let C := centralizer (S : Set G)
  have hnC : normalizer (S : Set G) ≤ normalizer (C : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (S : Set G))).mp
      (inferInstance : (C.subgroupOf (normalizer (S : Set G))).Normal)
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← P.normalizer_sup_eq_top]
  exact sup_le
    ((le_inf le_normalizer_of_normal hnC).trans
      (normalizer_inf_normalizer_le_normalizer_sup N C))
    (le_sup_left.trans (N ⊔ C).le_normalizer)

/-- Every nontrivial normal subgroup contains an ambient chief subgroup. -/
theorem exists_chief_le_of_ne_bot (H : Subgroup G) [H.Normal] (hH : H ≠ ⊥) :
    ∃ Q : Subgroup G, ChiefFactor.IsChief Q ⊥ ∧ Q ≤ H := by
  obtain ⟨Q, ⟨hQ, hne, hQH⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun Q : Subgroup G => Q.Normal ∧ Q ≠ ⊥ ∧ Q ≤ H)
    ⟨H, inferInstance, hH, le_rfl⟩
  refine ⟨Q, ⟨hQ, inferInstance, bot_lt_iff_ne_bot.mpr hne, ?_⟩, hQH⟩
  intro J hJ _ hJQ
  by_cases he : J = ⊥
  · exact Or.inl he
  · exact Or.inr (le_antisymm hJQ (hmin ⟨hJ, he, hJQ.trans hQH⟩ hJQ))

/-- A chief subgroup is p-star when the ambient p-core is trivial. -/
theorem isPStar_of_isChief_of_pCore_eq_bot (hcore : pCore p G = ⊥)
    (Q : Subgroup G) (hQ : ChiefFactor.IsChief Q ⊥) : IsPStar p Q := by
  let _ := hQ.normal_upper
  have hres : pResidual p Q = ⊤ := by
    rcases ChiefFactor.characteristic_eq_bot_or_top_of_minimal_normal Q
      (fun J hJ hJQ => hQ.minimal J hJ bot_le hJQ)
      (pResidual p Q) inferInstance with hb | ht
    · have hp : IsPGroup p Q :=
        (isPGroup_quotient_pResidual (G := Q) p).of_equiv
          ((QuotientGroup.quotientMulEquivOfEq hb).trans (QuotientGroup.quotientBot))
      have hle : Q ≤ pCore p G := le_sSup ⟨inferInstance, hp⟩
      exact False.elim (hQ.lt.ne' (le_antisymm (hcore ▸ hle) bot_le))
    · exact ht
  exact (isPStar_pResidual_of_isChief Q hQ).of_equiv
    ((MulEquiv.subgroupCongr hres).trans Subgroup.topEquiv)
end Subgroup
