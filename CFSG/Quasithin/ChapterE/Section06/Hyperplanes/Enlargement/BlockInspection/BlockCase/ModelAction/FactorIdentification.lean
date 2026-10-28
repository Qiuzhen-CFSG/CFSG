module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.ModelAction.FactorWitness
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.ModelAction.SylowAction
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Identifying the actual block among the E.6.7 factors

Put J = ⟨X,Q⟩. The quotient of J by the normal closure of X is a
2-group, so every short block lies in that normal closure. C.1.9 shows
that a block not conjugate to X would centralize the normal closure and
hence itself, contrary to shortness. The same commutation theorem makes
the normal closure normalize X, so the conjugating element can be taken
in Q. This uses two-perfection, including the nonperfect A₃ case.

Since Q centralizes V, every E.6.7 factor has the same fixed space A as X.
Its corank two makes the factor a natural L₂(4) block. If it were distinct
from X, its torus would centralize X, and its displacement on V would lie
in A. The direct decomposition in E.6.7(3) would then force V = A.
Thus every factor is X, and escape from M ensures that a factor exists.

All subnormality is relative to J or C_G(A). Q is allowed to move X;
neither normality under Q nor membership in the C-component family is
assumed. The exact E.6.7, C.1.9 and E.6.21 inputs remain explicit. The
stronger result does not require Hypothesis E.6.15 or a prior type for X.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–9,
printed p.123, E.6.7, printed p.246 (PDF p.257), and the proper-block step
in E.6.23, printed p.254 (PDF p.265).
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
open InvariantSubspaces.BlockSelection

private theorem short_not_self_centralizing {G : Type*} [Group G]
    {L : Subgroup G} (hL : ChapterC.IsShort L) :
    ¬ L ≤ centralizer (L : Set G) := by
  intro hc
  have hz : ChapterC.blockU L ≤ center L := by
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (hc x.property) y y.property)
  exact hL.irreducible.1.ne (inf_eq_left.mpr hz)

private theorem block_conjugate {G : Type*} [Group G] (X Q Y : Subgroup G)
    (hX : ChapterC.IsBlock X) (hY : ChapterC.IsBlock Y)
    (hcomm : ∀ B D : Subgroup G, ChapterC.IsBlock B → ChapterC.IsBlock D →
      B ≠ D → ⁅B, D⁆ = ⊥)
    (hQ : IsPGroup 2 Q) (hgen : X ⊔ Q = ⊤) :
    ∃ q ∈ Q, X.map (MulAut.conj q).toMonoidHom = Y := by
  classical
  let N := normalClosure (X : Set G)
  have hNQ : N ⊔ Q = ⊤ := top_unique (hgen ▸ sup_le_sup_right le_normalClosure Q)
  have hYN : Y ≤ N := (le_pResidual_of_isPPerfect Y hY.short.twoPerfect).trans
    (sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top N Q hQ hNQ⟩)
  have hNN : N ≤ normalizer (X : Set G) := by
    apply (closure_le _).mpr
    intro x hx
    obtain ⟨a, ha, hx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    have hg : g * a * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom := ⟨a, ha, rfl⟩
    by_cases he : X.map (MulAut.conj g).toMonoidHom = X
    · exact X.le_normalizer (he ▸ hg)
    · exact Subgroup.centralizer_le_normalizer _ ((commutator_eq_bot_iff_le_centralizer.mp
        (hcomm _ _ (hX.map_equiv (MulAut.conj g)) hX he)) hg)
  have hex : ∃ g : G, X.map (MulAut.conj g).toMonoidHom = Y := by
    by_contra! hn
    have hNC : N ≤ centralizer (Y : Set G) := by
      apply (closure_le _).mpr
      intro x hx
      obtain ⟨a, ha, hx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨g, rfl⟩ := isConj_iff.mp hx
      exact (commutator_eq_bot_iff_le_centralizer.mp
        (hcomm _ _ (hX.map_equiv (MulAut.conj g)) hY (hn g))) ⟨a, ha, rfl⟩
    exact short_not_self_centralizing hY.short (hYN.trans hNC)
  obtain ⟨g, hg⟩ := hex
  have hgprod : g ∈ (Q : Set G) * (N : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right Q N (by rw [normalizer_eq_top]; exact le_top),
      sup_comm, hNQ]
    trivial
  obtain ⟨q, hq, n, hn, rfl⟩ := hgprod
  refine ⟨q, hq, ?_⟩
  have hnX := mem_normalizer_iff_map_conj_eq.mp (hNN hn)
  change X.map (MulAut.conj n).toMonoidHom = X at hnX
  rw [map_mul] at hg
  change X.map ((MulAut.conj q).toMonoidHom.comp (MulAut.conj n).toMonoidHom) = Y at hg
  rw [← map_map, hnX] at hg
  exact hg

private theorem fixedSpace_conjugate {G : Type*} [Group G] {V X : Subgroup G} (q : G)
    (hq : q ∈ centralizer (V : Set G)) :
    V ⊓ centralizer (X.map (MulAut.conj q).toMonoidHom : Set G) =
      V ⊓ centralizer (X : Set G) := by
  have hV : V.map (MulAut.conj q).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _ hq)
  have hF : (V ⊓ centralizer (X : Set G)).map (MulAut.conj q).toMonoidHom =
      V ⊓ centralizer (X : Set G) :=
    mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _ (centralizer_le inf_le_left hq))
  rw [← hF, map_inf _ _ _ (MulAut.conj q).injective,
    Theory.Quasithin.map_centralizer, hV]

private theorem commutator_centralizes {G : Type*} [Group G] {V X D : Subgroup G}
    (hn : V ≤ normalizer (X : Set G)) (hc : D ≤ centralizer (X : Set G)) :
    ⁅V, D⁆ ≤ centralizer (X : Set G) := by
  have hnC : normalizer (X : Set G) ≤ normalizer (centralizer (X : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (X : Set G))).mp
      (inferInstance : ((centralizer (X : Set G)).subgroupOf (normalizer (X : Set G))).Normal)
  exact (commutator_mono le_rfl hc).trans
    (le_normalizer_iff_commutator_le_right.mp (hn.trans hnC))

/-- Every E.6.7 factor in the block–Sylow join is the given block when
its fixed space is the indicated corank-two subspace. -/
theorem block_join_factor_eq {G : Type*} [Group G] [Finite G]
    {𝒦 : GroupClass} {T : Sylow 2 G} {M V A X : Subgroup G}
    (h : HypothesisE61 𝒦 T M V) (h19 : BlockCommutationInput G)
    (hA : A ∈ obstructionFamily M V) (hX : CentralizerBlock A X)
    (hJ : HasCharacteristicTwo (X ⊔ sylowCentralizer (T : Subgroup G) V : Subgroup G))
    (d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V A
      (X ⊔ sylowCentralizer (T : Subgroup G) V))
    (hc : subgroupCorank V A = 2) (hfixed : V ⊓ centralizer (X : Set G) = A)
    (i : Fin d.count) : d.block i = X := by
  let Q := sylowCentralizer (T : Subgroup G) V
  let J := X ⊔ Q
  have hXJ : X ≤ J := le_sup_left
  have hQJ : Q ≤ J := le_sup_right
  have hJA : J ≤ centralizer (A : Set G) :=
    sup_le hX.1 (inf_le_right.trans (centralizer_le hA.1))
  have hBX : ChapterC.IsBlock (X.subgroupOf J) :=
    ⟨inferInstance,
      (hX.2.short.of_mulEquiv (subgroupOfEquivOfLe hX.1)).of_mulEquiv
        (subgroupOfEquivOfLe hXJ).symm,
      hX.2.subnormal.comap (inclusion hJA)⟩
  have hBY : ChapterC.IsBlock ((d.block i).subgroupOf J) :=
    ⟨inferInstance, ((d.type i).chi.short).of_mulEquiv (subgroupOfEquivOfLe (d.le i)).symm,
      d.subnormal i⟩
  have hgen : X.subgroupOf J ⊔ Q.subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hXJ, map_subgroupOf_eq_of_le hQJ,
      ← MonoidHom.range_eq_map, range_subtype]
  have hcomm := h19 J (fun _ => c19Condition_of_oddCore_eq_bot
    (pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hJ))
  have hQ : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  obtain ⟨q, hq, he⟩ := block_conjugate (X.subgroupOf J) (Q.subgroupOf J)
    ((d.block i).subgroupOf J) hBX hBY hcomm hQ.comap_subtype hgen
  have heG : X.map (MulAut.conj (q : G)).toMonoidHom = d.block i := by
    have hh := congrArg (Subgroup.map J.subtype) he
    rw [map_subgroupOf_eq_of_le (d.le i), map_map] at hh
    have hf : J.subtype.comp (MulAut.conj q).toMonoidHom =
        (MulAut.conj (q : G)).toMonoidHom.comp J.subtype := by ext; rfl
    rw [hf, ← map_map, map_subgroupOf_eq_of_le hXJ] at hh
    exact hh
  have hfi : V ⊓ centralizer (d.block i : Set G) = A := by
    rw [← heG, fixedSpace_conjugate (q : G) (show (q : G) ∈ centralizer (V : Set G) from hq.2)]
    exact hfixed
  have hnatural := factor_naturalFour_of_corank_two d hc i (by rw [hfi]; exact hc)
  obtain ⟨D, hD, _, _, hVD, _, _, _, _, _⟩ := d.rankOne i 2 hnatural
  by_contra hne
  have hne' : X.subgroupOf J ≠ (d.block i).subgroupOf J := by
    intro heq
    have hh := congrArg (Subgroup.map J.subtype) heq
    rw [map_subgroupOf_eq_of_le hXJ, map_subgroupOf_eq_of_le (d.le i)] at hh
    exact hne hh.symm
  have hDC : D ≤ centralizer (X : Set G) := by
    have hh := congrArg (Subgroup.map J.subtype) (hcomm _ _ hBX hBY hne')
    rw [map_commutator, map_subgroupOf_eq_of_le hXJ,
      map_subgroupOf_eq_of_le (d.le i), Subgroup.map_bot] at hh
    exact (hD.trans inf_le_left).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh))
  obtain ⟨S, _, hact⟩ := block_action_of_characteristicTwo_intermediate
    h hA hX hQJ hXJ hJA hJ
  have hVN : V ≤ normalizer (X : Set G) := by
    apply le_normalizer_iff.mpr
    intro v hv x hx
    obtain ⟨z, _, hz⟩ := hact v hv
    rw [← hz ⟨x, hx⟩]
    exact X.mul_mem (X.mul_mem z.property hx) (X.inv_mem z.property)
  have hWA : ⁅V, D⁆ ≤ A := by
    rw [← hfixed]
    exact le_inf ((le_sup_right : ⁅V, D⁆ ≤
      (V ⊓ centralizer (d.block i : Set G)) ⊔ ⁅V, D⁆).trans hVD.symm.le)
      (commutator_centralizes hVN hDC)
  have hVA : V ≤ A := by
    rw [hVD, hfi]
    exact sup_le le_rfl hWA
  have hAV : A = V := le_antisymm hA.1 hVA
  rw [hAV, subgroupCorank, relIndex_self] at hc
  norm_num at hc

/-- E.6.7 supplies a decomposition containing the actual proper block.
The fixed-space proof uses precisely C.1.9 and E.6.21; the join's
characteristic-two hypothesis is the input of ProperBlockFactors. -/
theorem properBlockFactors_of_e67 {G : Type*} [Group G] [Finite G]
    {𝒦 : GroupClass} {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 𝒦 T M V) (h67 : E67Input T M V)
    (h19 : BlockCommutationInput G) (h21 : OddCoreFree V) :
    ProperBlockFactors T M V := by
  let _ := h.elementary
  intro U hU hUh L hL he A hA hAU hc X hLX hX _ hJ
  let Q := sylowCentralizer (T : Subgroup G) V
  have hJA : X ⊔ Q ≤ centralizer (A : Set G) :=
    sup_le hX.1 (inf_le_right.trans (centralizer_le hA.1))
  obtain ⟨d⟩ := h67 A hA (X ⊔ Q) le_sup_right hJA hJ
  have hpos : 0 < d.count := by
    by_contra! hzero
    have hb : (⨆ i, d.block i : Subgroup G) = ⊥ := by
      apply iSup_eq_bot.mpr
      intro i
      have := i.isLt
      omega
    have hJM : X ⊔ Q ≤ M := by
      rw [d.generated, hb, sup_bot_eq]
      exact inf_le_right
    exact he (hLX.le.trans (le_sup_left.trans hJM))
  let i : Fin d.count := ⟨0, hpos⟩
  refine ⟨d, i, ?_⟩
  exact block_join_factor_eq h h19 hA hX hJ d hc
    (proper_block_fixedSpace h h19 h21 hU hUh hAU hc hL he hLX hX) i

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
