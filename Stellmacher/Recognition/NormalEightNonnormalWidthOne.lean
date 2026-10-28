module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Stellmacher.Recognition.NormalEightNonnormalLargeFactorReduction
public import Stellmacher.Recognition.NormalEightNonnormalLargeCoreExclusion
public import Theory.GroupTheory.PGroup.ExtraspecialSmallOrder

/-!
# Intrinsic width and the large-core obstruction

Every extraspecial factor has order eight or at least thirty-two. Thus a
reduction of all large factors to an extraspecial whole core of order
thirty-two, together with exclusion of that whole core, proves intrinsic
width one. Conversely, such a whole core itself gives a width-two Hall
presentation with trivial tail. Both implications retain the literal
odd-core quotient and impose no bound on arbitrary elementary subgroups.

The final theorem discharges both structural premises using the imported
four-generator reduction and ambient exclusion of both order-32 types.
Source: Janko–Thompson (1970), result 1.1 and §4, printed pp.389–392.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Intrinsic width one excludes an extraspecial whole core of order thirty-two,
using the presentation with the whole core and the trivial Hall tail. -/
public theorem omegaQuotient_pCore_not_extraspecial_thirty_two_of_width_one
    (S : Sylow 2 G)
    (hwidth : ∀ B D : Subgroup (pCore 2 (OmegaQuotient S)),
      B.Normal → D.Normal → IsExtraspecial 2 B → IsBinaryHallFactor D →
      D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))) → B ⊔ D = ⊤ →
      Nat.card B = 8) :
    ¬ (IsExtraspecial 2 (pCore 2 (OmegaQuotient S)) ∧
      Nat.card (pCore 2 (OmegaQuotient S)) = 32) := by
  rintro ⟨hH, hcard⟩
  let H := pCore 2 (OmegaQuotient S)
  have htop : IsExtraspecial 2 (⊤ : Subgroup H) :=
    hH.of_mulEquiv Subgroup.topEquiv.symm
  have hbot : IsBinaryHallFactor (⊥ : Subgroup H) := Or.inl inferInstance
  have hh := hwidth ⊤ ⊥ inferInstance inferInstance htop hbot bot_le (top_sup_eq _)
  rw [Nat.card_congr Subgroup.topEquiv.toEquiv, hcard] at hh
  contradiction

/-- Reducing every large factor to the whole order-thirty-two core and excluding
that core proves width one. The reduction premise covers arbitrarily large
extraspecial factors, not merely factors already known to have order thirty-two. -/
public theorem omegaQuotient_pCore_width_one_of_large_core_reduction
    (S : Sylow 2 G)
    (hreduce : ∀ B D : Subgroup (pCore 2 (OmegaQuotient S)),
      B.Normal → D.Normal → IsExtraspecial 2 B → IsBinaryHallFactor D →
      D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))) → B ⊔ D = ⊤ →
      32 ≤ Nat.card B →
      IsExtraspecial 2 (pCore 2 (OmegaQuotient S)) ∧
        Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hexclude : ¬ (IsExtraspecial 2 (pCore 2 (OmegaQuotient S)) ∧
      Nat.card (pCore 2 (OmegaQuotient S)) = 32)) :
    ∀ B D : Subgroup (pCore 2 (OmegaQuotient S)),
      B.Normal → D.Normal → IsExtraspecial 2 B → IsBinaryHallFactor D →
      D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))) → B ⊔ D = ⊤ →
      Nat.card B = 8 := by
  intro B D hBn hDn hB hD hc hg
  let : IsExtraspecial 2 B := hB
  rcases IsExtraspecial.card_eq_eight_or_thirty_two_le (P := B) with hsmall | hlarge
  · exact hsmall
  · exact (hexclude (hreduce B D hBn hDn hB hD hc hg hlarge)).elim

/-- Every extraspecial factor in a Hall presentation of the quotient two-core
has order eight under the no-normal-elementary-eight hypotheses. The large
factor reduction applies at arbitrary width, and the whole-core exclusion
handles both extraspecial types of order thirty-two. -/
public theorem omegaQuotient_pCore_width_one
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (hN : Stellmacher.IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (Subgroup.center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal) :
    ∀ B D : Subgroup (pCore 2 (OmegaQuotient S)),
      B.Normal → D.Normal → IsExtraspecial 2 B → IsBinaryHallFactor D →
      D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))) → B ⊔ D = ⊤ →
      Nat.card B = 8 := by
  apply omegaQuotient_pCore_width_one_of_large_core_reduction S
  · intro B D hBn hDn hB hD hc hg hlarge
    let : B.Normal := hBn
    let : D.Normal := hDn
    let : IsExtraspecial 2 B := hB
    exact omegaQuotient_pCore_large_factor_reduction hns hN S A hA hnonab hZ hno
      W hW hunique hnormal B D hD hc hg hlarge
  · rintro ⟨hH, hcard⟩
    let : IsExtraspecial 2 (pCore 2 (OmegaQuotient S)) := hH
    exact omegaQuotient_large_core_false hns hN S A hA hnonab hZ hno
      W hW hunique hnormal hcard

end Stellmacher.Recognition.NormalEightNonnormalImage
