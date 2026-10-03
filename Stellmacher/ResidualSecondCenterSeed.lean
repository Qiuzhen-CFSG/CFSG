module

public import Stellmacher.ResidualCommutatorIdempotence
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Theory.GroupTheory.SmallTwoCentralQuotientCommutator

/-!
# A residual-generated seed in the second central layer

Let `Q` be a normal two-subgroup of a finite group and `Z` a normal subgroup
of order two. The local two-residual is assumed to centralize the center of
`Q`. Let `M` be the elements of `Q` that centralize `Q` modulo `Z`.
If an extracted residual contained in the local residual normalizes `V`
and has a commutator with `M ∩ V` outside `Z`, then `U = [M,O²(P)]` is normal,
lies in `Q`, satisfies `[U,Q] = Z` and `[U,O²(P)] = U`, and meets `V` in a
subgroup of order at least eight that is not contained in `Z`. Only `Z ≤ V` is required; `V ≤ Q` is not
needed for this construction.

Normality of the quotient centralizer makes `M` and `U` normal. Residual
commutator idempotence gives the full residual equation. If `U` centralized
`Q`, the fixed-center hypothesis would force `U` trivial, contradicting the
extracted commutator. Thus `[U,Q]`, already contained in `Z`, equals `Z`.
For the size bound, a two-subgroup of order less than eight modulo a contained
normal subgroup of order two admits no nontrivial normalizer action.
Applying this to `U ∩ V` contradicts residual idempotence of the extracted
commutator.

This is the group-theoretic seed construction before relation (9) in
Stellmacher's N-group paper (1997), (9.1), pp. 46–47; source file
`refs/latex/stellmacher-n-group.tex`. Graph-specific nontriviality and
noncontainment arguments belong to the caller.
-/

open Subgroup
open scoped commutatorElement
namespace Stellmacher
open SectionThree BenderSuzuki.External

private theorem residual_commutator_idem_normalized
    {G : Type*} [Group G] [Finite G] (M L : Subgroup G)
    (hM : IsPGroup 2 M) (hn : twoResidualAmbient L ≤ normalizer M) :
    ⁅⁅M,twoResidualAmbient L⁆,twoResidualAmbient L⁆ = ⁅M,twoResidualAmbient L⁆ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hid : twoResidualAmbient (twoResidualAmbient L) = twoResidualAmbient L := by
    rw [twoResidualAmbient, twoResidualSubgroup_eq_hktPResidual',
      twoResidualAmbient_has_top_twoResidual, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  simpa only [hid] using commutator_twoResidualAmbient_idempotent M (twoResidualAmbient L) hM hn

/-- A nontrivial extracted residual action in a second central layer supplies
a normal seed with full residual commutator and an intersection of order at
least eight. -/
public theorem exists_residual_second_center_seed
    {P : Type*} [Group P] [Finite P]
    (Q Z V L : Subgroup P) [Q.Normal] [Z.Normal]
    (hQ : IsPGroup 2 Q) (hZcard : Nat.card Z = 2)
    (hZV : Z ≤ V)
    (hfix : ⁅centerIn Q, twoResidualAmbient (⊤ : Subgroup P)⁆ = ⊥)
    (hRE : twoResidualAmbient L ≤ twoResidualAmbient (⊤ : Subgroup P))
    (hRV : twoResidualAmbient L ≤ normalizer V)
    (hnon : ¬ ⁅(Q ⊓ (centralizer
        ((Q.map (QuotientGroup.mk' Z) : Subgroup (P ⧸ Z)) : Set (P ⧸ Z))).comap
          (QuotientGroup.mk' Z)) ⊓ V, twoResidualAmbient L⁆ ≤ Z) :
    ∃ U : Subgroup P, U ≤ Q ∧ ⁅U,Q⁆ = Z ∧
      ⁅U,twoResidualAmbient (⊤ : Subgroup P)⁆ = U ∧ U.Normal ∧
      8 ≤ Nat.card ↥(U ⊓ V) ∧ ¬ U ⊓ V ≤ Z := by
  classical
  let E := twoResidualAmbient (⊤ : Subgroup P)
  let R := twoResidualAmbient L
  let q := QuotientGroup.mk' Z
  let Qbar := Q.map q
  have hQbar : Qbar.Normal := (inferInstance : Q.Normal).map q (QuotientGroup.mk'_surjective Z)
  let _ : Qbar.Normal := hQbar
  let M := Q ⊓ (centralizer (Qbar : Set (P ⧸ Z))).comap q
  let U := ⁅M,E⁆
  let W := ⁅M ⊓ V,R⁆
  have hE : E.Normal := by
    dsimp [E]
    rw [twoResidualAmbient_top_eq_hktPResidual]
    exact hktPResidual_normal
  let _ : E.Normal := hE
  have hM : M.Normal := inferInstance
  let _ : M.Normal := hM
  have hU : U.Normal := inferInstance
  let _ : U.Normal := hU
  have hMQ : M ≤ Q := inf_le_left
  have hUM : U ≤ M := commutator_le_left _ _
  have hUQ : U ≤ Q := hUM.trans hMQ
  have hfull : ⁅U,E⁆ = U :=
    commutator_twoResidualAmbient_idempotent M ⊤ (hQ.to_le hMQ) le_normalizer_of_normal
  have hWn : R ≤ normalizer (M ⊓ V) :=
    (le_inf le_normalizer_of_normal hRV).trans inf_normalizer_le_normalizer_inf
  have hWfull : ⁅W,R⁆ = W := residual_commutator_idem_normalized (M ⊓ V) L
    (hQ.to_le (inf_le_left.trans hMQ)) hWn
  have hWMV : W ≤ M ⊓ V := le_normalizer_iff_commutator_le_left.mp hWn
  have hWU : W ≤ U := commutator_mono inf_le_left hRE
  have hWUV : W ≤ U ⊓ V := le_inf hWU (hWMV.trans inf_le_right)
  have hMQZ : ⁅M,Q⁆ ≤ Z := by
    rw [commutator_le]
    intro m hm a ha
    apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅m,a⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_centralizer_iff.mp hm.2 (q a) (mem_map_of_mem q ha)).symm
  have hUQZ : ⁅U,Q⁆ ≤ Z := (commutator_mono hUM le_rfl).trans hMQZ
  have hne : ⁅U,Q⁆ ≠ ⊥ := by
    intro hbot
    have hUC : U ≤ centerIn Q := le_inf hUQ (commutator_eq_bot_iff_le_centralizer.mp hbot)
    have hfullbot : ⁅U,E⁆ = ⊥ :=
      le_antisymm ((commutator_mono hUC le_rfl).trans hfix.le) bot_le
    have hUbot : U = ⊥ := hfull.symm.trans hfullbot
    exact hnon (hWU.trans (by rw [hUbot]; exact bot_le))
  have hcomm : ⁅U,Q⁆ = Z := by
    apply eq_of_le_of_card_ge hUQZ
    have hc := (Subgroup.one_lt_card_iff_ne_bot (H := ⁅U,Q⁆)).mpr hne
    omega
  have hZU : Z ≤ U := hcomm ▸ commutator_le_left U Q
  refine ⟨U,hUQ,hcomm,hfull,hU,?_, fun h => hnon (hWUV.trans h)⟩
  by_contra hc
  have hKR : R ≤ normalizer (U ⊓ V) :=
    (le_inf le_normalizer_of_normal hRV).trans inf_normalizer_le_normalizer_inf
  have hKZ := commutator_le_of_card_lt_eight_of_normal_order_two (U ⊓ V) Z R
    (hQ.to_le (inf_le_left.trans hUQ)) (le_inf hZU hZV) hZcard hKR (by omega)
  apply hnon
  change W ≤ Z
  rw [← hWfull]
  exact (commutator_mono hWUV le_rfl).trans hKZ
end Stellmacher
