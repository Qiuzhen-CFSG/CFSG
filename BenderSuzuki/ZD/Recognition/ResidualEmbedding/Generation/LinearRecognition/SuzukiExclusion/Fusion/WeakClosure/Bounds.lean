module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Basic
public import Theory.SpecificGroups.Suzuki.TwoRank
public import Theory.ElementaryAbelian.Quotient

/-!
# The elementary centralizer factor in the Suzuki fusion argument

The actual embedding of J into the Suzuki group bounds its elementary
Sylow factor U by the field order. Evenness of J makes U nontrivial. The
distinguished closure has field order and is disjoint from U, as follows
from the center and direct-product descriptions of P and T.

These are the cardinal bounds used in GLS4, Chapter 2, Lemma 14.8. They
do not assert that U has order two. Source: `refs/KGroup/GLS4/Chapter2.tex`,
Lemmas 14.2–14.3 and 14.8.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.GroupTheory PFAppendixIII
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

public theorem LocalGeometry.U_le_T (g : LocalGeometry Z M z t m) : g.U ≤ g.T := by
  rw [g.U_eq]
  exact inf_le_left

public theorem LocalGeometry.U_le_S (g : LocalGeometry Z M z t m) : g.U ≤ g.S :=
  g.U_le_T.trans g.T_lt_S.le

public theorem LocalGeometry.U_le_centralizer (g : LocalGeometry Z M z t m) :
    g.U ≤ centralizer (residualGenerated M z t : Set G) := by
  rw [g.U_eq]
  exact inf_le_right

public theorem LocalGeometry.closure_le_P (g : LocalGeometry Z M z t m) :
    closure (Z ∩ (M : Set G)) ≤ borelTwoCore M z t := by
  rw [← g.P_center]
  exact map_subtype_le _

public theorem LocalGeometry.closure_le_S (g : LocalGeometry Z M z t m) :
    closure (Z ∩ (M : Set G)) ≤ g.S := by
  apply g.closure_le_P.trans
  rw [g.P_eq]
  exact inf_le_left.trans g.T_lt_S.le

public theorem LocalGeometry.closure_disjoint_U (g : LocalGeometry Z M z t m) :
    Disjoint (closure (Z ∩ (M : Set G))) g.U :=
  g.P_disjoint_U.mono_left g.closure_le_P

/-- The source distinguished closure has order q and is elementary abelian. -/
public theorem Context.closure_elementary_card (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) :
    IsElementaryAbelian 2 (closure (Z ∩ (M : Set G))) ∧
      Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ (2 * m + 1) := by
  apply residualGenerated_suzuki_distinguishedClosure d.minimal.disconnected d.reduction
    d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper
      ?_ (by have := d.parameter_pos; omega) d.model
  apply g.closure_le_P.trans
  rw [g.P_eq]
  exact inf_le_right

/-- The elementary Sylow factor is bounded using the literal embedding of J. -/
public theorem Context.U_card_le (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) : Nat.card g.U ≤ 2 ^ (2 * m + 1) := by
  let e := d.model.toMonoidHom.comp (f.comp (inclusion g.U_le_centralizer))
  have he : Function.Injective e :=
    d.model.injective.comp (hf.comp (inclusion_injective g.U_le_centralizer))
  let := g.U_elementary
  let : IsElementaryAbelian 2 e.range :=
    IsElementaryAbelian.of_surjective e.rangeRestrict e.rangeRestrict_surjective
  have hbound := (primeRank_le_iff_elementary_card_le
    (MatrixGroups.SuzukiMatrixGroup m)).mp
      (MatrixGroups.suzuki_two_rank m (by have := d.parameter_pos; omega)).le
        e.range inferInstance
  rwa [← Nat.card_congr (MonoidHom.ofInjective he).toEquiv] at hbound

/-- Evenness of J rules out the trivial elementary Sylow factor. -/
public theorem Context.two_le_U_card (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) : 2 ≤ Nat.card g.U := by
  obtain ⟨V, hV⟩ := g.U_sylow_centralizer
  have hn := V.ne_bot_of_dvd_card d.centralizer_even.two_dvd
  have hc : 1 < Nat.card (V : Subgroup (centralizer
      (residualGenerated M z t : Set G))) := (one_lt_card_iff_ne_bot _).mpr hn
  rw [← hV, card_map_of_injective Subtype.val_injective]
  exact hc

end BenderSuzuki.ZD.SuzukiExclusion
