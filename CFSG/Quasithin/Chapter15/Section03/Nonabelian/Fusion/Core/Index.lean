module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Reduction
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The index-two deduction from the actual actor quotient

Simplicity and order 168 show that SL₃(2) is two-perfect. Its inner
automorphism subgroup is therefore the two-residual of Aut(SL₃(2)), since
the checked outer quotient has order two. A multiplicative equivalence from
the literal actor quotient H/O₂(H) transports this calculation.

After U = O₂(H) and U ≤ K, the quotient map preserves the residual index.
Sylow restriction then proves the precise index [T:T∩K] used by transfer.
Only the group-equivalence clause of 15.3.58 is needed for this deduction;
the natural/dual action is still needed for the residual-generation inputs
of the other clauses.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.58(1) and 15.3.59(3), printed pp.1148–1150.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core
open Subgroup
open Matrix.PSL3Two

private theorem linear_three_two_perfect : IsPPerfect 2 SL := by
  let : IsSimpleGroup PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup SL := equiv.isSimpleGroup
  intro N hN hp
  rcases hN.eq_bot_or_eq_top with hn | hn
  · obtain ⟨n, hc⟩ := hp.exists_card_eq
    have he : 168 = 2 ^ n := by
      change N.index = 2 ^ n at hc
      simpa only [hn, index_bot, card_SL] using hc
    have hd : 3 ∣ 2 ^ n := he ▸ (by decide : 3 ∣ 168)
    have hf := (by decide : Nat.Prime 3).dvd_of_dvd_pow hd
    norm_num at hf
  · exact hn

private theorem aut_linear_three_residual :
    pResidual 2 (MulAut SL) = MulAut.innerSubgroup SL := by
  apply pResidual_eq_of_isPPerfect _ _ Automorphisms.outer_sl_isTwoGroup
  exact linear_three_two_perfect.of_surjective (MulAut.conj : SL →* MulAut SL).rangeRestrict
    (MulAut.conj : SL →* MulAut SL).rangeRestrict_surjective

private theorem aut_linear_three_residual_index : (pResidual 2 (MulAut SL)).index = 2 := by
  rw [aut_linear_three_residual]
  exact Automorphisms.card_outer_sl


open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core
variable {G : Type*} [Group G] [Finite G]

/-- The actual group equivalence in 15.3.58(1) determines the residual index in H*. -/
theorem actorResidual_index_two (Z : Subgroup G)
    (e : ActorQuotient Z ≃* MulAut SL) :
    (pResidual 2 (ActorQuotient Z)).index = 2 := by
  have hi : ((pResidual 2 (ActorQuotient Z)).map e.toMonoidHom).index = 2 := by
    rw [map_pResidual_of_surjective 2 e.toMonoidHom e.surjective]
    exact aut_linear_three_residual_index
  exact ((pResidual 2 (ActorQuotient Z)).index_map_equiv e).symm.trans hi

/-- Once the two-core is U ≤ K, the actual actor equivalence yields |T:T_K| = 2.
The subgroup S is genuinely Sylow in H and has the prescribed ambient image T. -/
theorem residualSylow_index_two_of_actor_equiv (T Z ZS : Subgroup G)
    (S : Sylow 2 (centralizerH Z))
    (hS : (S : Subgroup (centralizerH Z)).map (centralizerH Z).subtype = T)
    (e : ActorQuotient Z ≃* MulAut SL)
    (hcore : closureU Z ZS = coreQ Z) (hUK : closureU Z ZS ≤ residualK Z) :
    ((residualSylow T Z).subgroupOf T).index = 2 := by
  have hQR : pCore 2 (centralizerH Z) ≤ pResidual 2 (centralizerH Z) := by
    apply (map_le_map_iff_of_injective (centralizerH Z).subtype_injective).mp
    change coreQ Z ≤ (pResidual 2 (centralizerH Z)).map (centralizerH Z).subtype
    rw [← twoResidualAmbient_eq_pResidual]
    exact hcore.symm.le.trans hUK
  let q := QuotientGroup.mk' (pCore 2 (centralizerH Z))
  have hkernel : q.ker ≤ pResidual 2 (centralizerH Z) := by
    simpa only [q, QuotientGroup.ker_mk'] using hQR
  have hi := (pResidual 2 (centralizerH Z)).index_map_eq
    (QuotientGroup.mk'_surjective (pCore 2 (centralizerH Z))) hkernel
  rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)] at hi
  rw [residualSylow_index T Z S hS, ← hi]
  exact actorResidual_index_two Z e

/-- The first three conclusions of 15.3.59, assembled from the precise remaining
residual calculations and the earlier local data. The recognition input is an
equivalence of the actual actor quotient, not an abstract group-family tag. -/
theorem core_sylow_and_index_of_local_calculations (T Z ZS V Y : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal] [IsExtraspecial 2 (closureU Z ZS)]
    (d : LocalCoreData T Z ZS V Y)
    (S : Sylow 2 (centralizerH Z))
    (hS : (S : Subgroup (centralizerH Z)).map (centralizerH Z).subtype = T)
    (e : ActorQuotient Z ≃* MulAut SL)
    (hUK : closureU Z ZS ≤ residualK Z)
    (hgen : ⁅residualK Z, V⁆ = residualK Z)
    (hcontain : residualSylow T Z ≤ Y ⊔ closureU Z ZS)
    (hlower : 2 ^ 10 ≤ Nat.card (residualSylow T Z)) :
    closureU Z ZS = coreQ Z ∧
      (∃ P : Sylow 2 (Y ⊔ closureU Z ZS : Subgroup G),
        (P : Subgroup (Y ⊔ closureU Z ZS : Subgroup G)).map (Y ⊔ closureU Z ZS).subtype =
          residualSylow T Z) ∧
      ((residualSylow T Z).subgroupOf T).index = 2 := by
  obtain ⟨hcore, hSylow⟩ :=
    core_and_sylow_of_local_calculations T Z ZS V Y d hgen hcontain hlower
  exact ⟨hcore, hSylow, residualSylow_index_two_of_actor_equiv T Z ZS S hS e hcore hUK⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core
