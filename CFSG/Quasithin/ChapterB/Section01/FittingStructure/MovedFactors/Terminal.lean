module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MovedFactors.Quotient

/-!
# The final minimal-offender contradiction in B.1.10

Assume the B.1.9 conclusion and G = EKA, where E = C_F(G)(J*).
Choose an equal-weight minimal offender B inside the given offender A.
A normalized quasisimple or cubic subgroup is either centralized or fully
moved by B. The latter case contradicts B.1.9(5). In the former, B commutes
with K, with E by definition, and with A because A is elementary abelian.
Hence B is a normal two-subgroup of G, contrary to O₂(G) = 1.

Choosing B inside A sharpens the source's choice inside KA. It makes the
last contradiction direct, while retaining precisely the source hypotheses.
The B.1.9 conclusion and the second generation equality remain explicit;
the main induction owner must construct both before applying this theorem.

Source: Aschbacher–Smith, B.1.10, final paragraph, printed p.72 (PDF p.83).
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure.MovedFactors
variable {G V : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalized_factor_cases (K B : Subgroup G)
    (hK : IsQuasisimple K ∨ Nat.card K = 3) (hn : B ≤ normalizer (K : Set G)) :
    ⁅K,B⁆ = ⊥ ∨ ⁅K,B⁆ = K := by
  have hCK : ⁅K,B⁆ ≤ K := le_normalizer_iff_commutator_le_left.mp hn
  rcases hK with hK | hK
  · let H := K ⊔ B
    let K₀ := K.subgroupOf H
    let B₀ := B.subgroupOf H
    let : K₀.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le K.le_normalizer hn)
    let : IsQuasisimple K := hK
    let : IsQuasisimple K₀ := IsQuasisimple.of_mulEquiv
      (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)).symm
    have hc : IsComponent H K₀ := ⟨(inferInstance : K₀.Normal).isSubnormal, inferInstance⟩
    have hm : (⁅K₀,B₀⁆).map H.subtype = ⁅K,B⁆ := by
      simp only [K₀, B₀, map_commutator,
        map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
        map_subgroupOf_eq_of_le (show B ≤ H from le_sup_right)]
    rcases hc.commutator_dichotomy B₀ with hz | he
    · left
      rw [← hm, hz, Subgroup.map_bot]
    · right
      have hlocal : ⁅K₀,B₀⁆ = K₀ := le_antisymm (commutator_le_left K₀ B₀)
        ((le_iSup_conjugates K₀ B₀).trans he.symm.le)
      rw [← hm, hlocal]
      exact map_subgroupOf_eq_of_le le_sup_left
  · let : Fact (Nat.card K).Prime := ⟨hK ▸ Nat.prime_three⟩
    rcases (⁅K,B⁆.subgroupOf K).eq_bot_or_eq_top_of_prime_card with hz | ht
    · left
      have hh := congrArg (Subgroup.map K.subtype) hz
      simpa only [map_subgroupOf_eq_of_le hCK, Subgroup.map_bot] using hh
    · right
      exact le_antisymm hCK (subgroupOf_eq_top.mp ht)

variable [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem contradiction_of_centralizer_generation (d : Conclusion ρ)
    (hcore : pCore 2 G = ⊥) (K A : Subgroup G)
    (hK : IsQuasisimple K ∨ Nat.card K = 3)
    (hA : IsBestOffender ρ A) (hKA : K = ⁅K,A⁆)
    (hne : ⁅fittingSubgroup G,K⁆ ≠ ⊥)
    (hgen : (fittingSubgroup G ⊓ centralizer (minimalGenerated ρ : Set G)) ⊔
      (K ⊔ A) = ⊤) : False := by
  obtain ⟨B, hB, hBA⟩ := hA.exists_minimal ρ
  have hn : B ≤ normalizer (K : Set G) :=
    hBA.1.trans (hKA ▸ normalizer_commutator_ge_right K A)
  have hKB : K ≤ centralizer (B : Set G) := by
    rcases normalized_factor_cases K B hK hn with hz | he
    · exact commutator_eq_bot_iff_le_centralizer.mp hz
    · have hc := (d.moved_subgroup_centralizes B hB K he.symm).trans inf_le_right
      apply False.elim
      apply hne
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hc
  let : IsElementaryAbelian 2 A := hA.1.2
  have hAB : A ≤ centralizer (B : Set G) := A.le_centralizer.trans (centralizer_le hBA.1)
  have hEB : fittingSubgroup G ⊓ centralizer (minimalGenerated ρ : Set G) ≤
      centralizer (B : Set G) :=
    inf_le_right.trans (centralizer_le (minimal_le ρ hB))
  have hGB : (⊤ : Subgroup G) ≤ centralizer (B : Set G) := by
    rw [← hgen]
    exact sup_le hEB (sup_le hKB hAB)
  let : B.Normal := normalizer_eq_top_iff.mp
    (top_unique (hGB.trans (centralizer_le_normalizer _)))
  let : IsElementaryAbelian 2 B := hB.1.1.2
  have hBQ : B ≤ pCore 2 G := le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 B⟩
  exact hB.1.1.1 (bot_unique (hBQ.trans_eq hcore))

end CFSG.Quasithin.ChapterB.FittingStructure.MovedFactors
