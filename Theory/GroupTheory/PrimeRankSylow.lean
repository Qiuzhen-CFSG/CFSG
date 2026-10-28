module

public import Theory.GroupTheory.QuasithinBasic
public import Mathlib.GroupTheory.Sylow

/-!
# Prime rank is detected on a Sylow subgroup

Every abelian p-subgroup embeds in a Sylow p-subgroup, and Sylow conjugacy
transports that embedding to any chosen Sylow subgroup. The converse follows
from its inclusion in the ambient group. This reduces concrete prime-rank
calculations to the structure of one Sylow subgroup.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.2.19, printed p. 41.
-/

open scoped IsMulCommutative

/-- A finite group's prime rank equals that of each Sylow subgroup. -/
public theorem Sylow.primeRank_eq {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) : primeRank p G = primeRank p P := by
  apply le_antisymm
  · apply csSup_le'
    rintro n ⟨A, hAp, hAc, hfg, hn⟩
    obtain ⟨Q, hAQ⟩ := hAp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
    have he : primeRank p P = primeRank p Q := by
      have e : (P : Subgroup G) ≃* ((g • P : Sylow p G) : Subgroup G) :=
        Subgroup.equivMapOfInjective (P : Subgroup G)
          (MulAut.conj g).toMonoidHom (EquivLike.injective (MulAut.conj g))
      have hh := Theory.GroupTheory.primeRank_equiv p e
      rwa [hg] at hh
    rw [he]
    let := hAc
    let f : A →* Q := Subgroup.inclusion hAQ
    have hle := Theory.GroupTheory.primeRank_le_of_injective p f (Subgroup.inclusion_injective hAQ)
    have hself : Group.rank A ≤ primeRank p A := by
      apply le_csSup (Theory.GroupTheory.primeRank_bdd p)
      refine ⟨⊤, ?_, inferInstance, inferInstance, ?_⟩
      · exact hAp.of_injective (⊤ : Subgroup A).subtype Subtype.val_injective
      · exact le_of_eq (Group.rank_congr Subgroup.topEquiv).symm
    exact hn.trans (hself.trans hle)
  · exact Theory.GroupTheory.primeRank_le_of_injective p (P : Subgroup G).subtype Subtype.val_injective
