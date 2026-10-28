module

public import Theory.SpecificGroups.SL2.DefiningRank
public import CFSG.Quasithin.ChapterA.Section02.OddLie.RootCoverTransfer

/-!
# Odd-characteristic root-group bounds for A.2.17

These are the defining-field bounds in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript (1 March 2004),
Lemma A.2.17, pp. 38–39. The input rank bounds are stated directly on the
ambient group or its involution centralizers, so they can be supplied by the
simultaneous induction in A.2 without assuming any family elimination.

Upper transvections witness rank `e` over a field of cardinality `p^e`.
For SL₂ they centralize the nontrivial central involution; for a subgroup
`C₂ × PSL₂` they centralize the first factor. The latter is the obstruction
used for Ree groups once their concrete involution centralizer is constructed.
`RootCoverTransfer` supplies the prescribed root lift, complementary residual
identity, and quotient rank bounds from the odd, defining-prime-free center
conditions. Full family elimination still requires the complementary centralizer
models, torus ranks, and ambient center analysis.
-/

public section

namespace CFSG.Quasithin.ChapterA.Section02

open Matrix

variable {K G : Type*} [Field K] [Finite K] [Group G] [Finite G]
    {p e : ℕ} [Fact p.Prime] [CharP K p]

/-- The defining field of an embedded fundamental SL₂ has degree at most two
when the relevant involution centralizers have prime rank at most two. -/
theorem sl2_fieldExponent_le_two (hp : p ≠ 2) (hcard : Nat.card K = p ^ e)
    (f : SpecialLinearGroup (Fin 2) K →* G) (hf : Function.Injective f)
    (hlocal : ∀ z : G, z ≠ 1 → z ^ 2 = 1 →
      primeRank p (Subgroup.centralizer ({z} : Set G)) ≤ 2) : e ≤ 2 := by
  let : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩
  obtain ⟨hz, hz2⟩ := SpecialLinearGroup.map_neg_one_isInvolution hp f hf
  exact (SpecialLinearGroup.fieldExponent_le_primeRank_centralizer hcard f hf).trans
    (hlocal (f (-1)) hz hz2)

/-- The PSL₂ branch uses the ordinary rank bound of strong quasithinness. -/
theorem psl2_fieldExponent_le_two (hcard : Nat.card K = p ^ e)
    (f : (SpecialLinearGroup (Fin 2) K ⧸ Subgroup.center (SpecialLinearGroup (Fin 2) K)) →* G)
    (hf : Function.Injective f) (hrank : primeRank p G ≤ 2) : e ≤ 2 :=
  (SpecialLinearGroup.fieldExponent_le_primeRank_of_projective_injective hcard f hf).trans
    hrank

/-- A `C₂ × PSL₂(p^e)` subgroup is incompatible with the local bound when `e > 2`.
For Ree groups the required subgroup and odd degree are separate structural inputs. -/
theorem not_injective_psl2_product_of_large_fieldExponent (hcard : Nat.card K = p ^ e)
    (he : 2 < e)
    (hlocal : ∀ z : G, z ≠ 1 → z ^ 2 = 1 →
      primeRank p (Subgroup.centralizer ({z} : Set G)) ≤ 2)
    (f : Multiplicative (ZMod 2) ×
      (SpecialLinearGroup (Fin 2) K ⧸ Subgroup.center (SpecialLinearGroup (Fin 2) K)) →* G) :
    ¬ Function.Injective f := by
  intro hf
  obtain ⟨z, hz, hz2, hr⟩ :=
    SpecialLinearGroup.exists_involution_primeRank_ge_of_projective_product hcard f hf
  exact (not_le_of_gt he) (hr.trans (hlocal z hz hz2))

end CFSG.Quasithin.ChapterA.Section02
