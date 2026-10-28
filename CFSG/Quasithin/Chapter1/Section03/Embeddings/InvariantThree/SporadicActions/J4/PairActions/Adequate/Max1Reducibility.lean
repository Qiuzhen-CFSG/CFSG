module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.MathieuTransport
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.LocalOvergroups.TrioPlacement
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.LocalOvergroups.TrioQuotient

/-!
# Reducibility for a J₄ pair in a max1-type overgroup

The supplied local equivalence followed by the actual max1 projection gives a
surjection to M₂₄ with a two-group kernel. The odd complement injects through
this map, retaining both its elementary-nine and extraspecial order-27 cases.
Odd-prime rank bounds descend through the kernel, and the complement forces
three-rank two. The proved simplicity and composite order of M₂₄ supply the
remaining quasisimplicity and commutator clauses of the quotient `PairInput`.

The corrected Mathieu alternative either gives reducibility or places the
quotient pair in a trio stabilizer. In the latter case the proved trio quotient
and Sylow-normalizer control give reducibility. Every supplied actor descends
through the characteristic max1 kernel, and the invariant subgroup pulls back
through the actual complement and Frattini equivalences.

Only `ReducibleOrTrioPlacement` remains an explicit premise. Its proof is owned
by the separate Mathieu placement task and must be supplied by the J₄ assembly.
No universal max1-preimage placement or invariant-subgroup premise is used.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511/PDF p.528
of `refs/quasithin.pdf`; see `docs/quasithin-proof-basis.md` for the corrected
actor-wise sieve and its distinction from universal placement.
-/

open Subgroup Theory.GroupTheory
open scoped Pointwise
set_option backward.isDefEq.respectTransparency true

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate
open MathieuAbsorption Sporadic.Mathieu
attribute [local irreducible] Janko4.modelGroup Janko4.Cardinality.max1Subgroup

private theorem mathieu_center : center M24 = ⊥ := by
  let := m24_isSimpleGroup
  rcases (inferInstance : (center M24).Normal).eq_bot_or_eq_top with h | h
  · exact h
  let := Group.commGroupOfCenterEqTop h
  have hp := IsSimpleGroup.prime_card (α := M24)
  rw [m24_order] at hp
  norm_num at hp

private theorem mathieu_quasisimple : IsQuasisimple M24 := by
  let := m24_isSimpleGroup
  have hperfect : Group.IsPerfect M24 := by
    constructor
    rcases (inferInstance : (_root_.commutator M24).Normal).eq_bot_or_eq_top with hb | ht
    · have hc := (commutator_eq_bot_iff_center_eq_top M24).mp hb
      rw [mathieu_center] at hc
      exact (bot_ne_top hc).elim
    · exact ht
  let := hperfect
  refine { simple := ?_ }
  let e : (M24 ⧸ center M24) ≃* M24 :=
    (QuotientGroup.quotientMulEquivOfEq mathieu_center).trans QuotientGroup.quotientBot
  exact (MulEquiv.isSimpleGroup_congr e).mpr m24_isSimpleGroup

private theorem mathieu_commutator (U : Subgroup M24) (hu : XiOddQuotient 3 U) :
    ⁅(⊤ : Subgroup M24), U⁆ = ⊤ := by
  let := m24_isSimpleGroup
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : (⁅(⊤ : Subgroup M24), U⁆).Normal :=
    normalizer_eq_top_iff.mp (top_le_iff.mp (normalizer_commutator_ge_left ⊤ U))
  rcases (inferInstance : (⁅(⊤ : Subgroup M24), U⁆).Normal).eq_bot_or_eq_top with hb | ht
  · have hub : U = ⊥ := le_bot_iff.mp (mathieu_center ▸
      (commutator_top_left_eq_bot_iff_le_center.mp hb))
    have hc : IsCyclic U := by rw [hub]; infer_instance
    exact (hu.not_isCyclic hc).elim
  · exact ht

private theorem quotient_pair_input [Finite Janko4.Model]
    {S : Sylow 2 Janko4.Model} {R : Subgroup Janko4.Model} (h : PairInput S R)
    (M : Subgroup Janko4.Model) (hSM : S.toSubgroup ≤ M) (hRM : R ≤ M)
    (f : M →* M24) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (eR : R ≃* (R.subgroupOf M).map f) :
    PairInput ((S.subtype hSM).mapSurjective hf) ((R.subgroupOf M).map f) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hthin : IsStronglyQuasithin M24 := by
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    rw [← primeRank_congr p (QuotientGroup.quotientKerEquivOfSurjective f hf)]
    exact (primeRank_quotient_le_of_isTwoGroup p ho f.ker hk).trans
      ((primeRank_subgroup_le p M).trans (h.stronglyQuasithin p hp ho))
  have hodd := h.oddComplement.of_mulEquiv eR
  refine ⟨mathieu_quasisimple, m24_twoCore, hthin, ?_, hodd,
    mathieu_commutator _ hodd, ?_⟩
  · have hu := hthin 3 Nat.prime_three (by decide)
    have hl := primeRank_subgroup_le 3 ((R.subgroupOf M).map f)
    rw [← primeRank_congr 3 eR, EvenRankTwo.complement_rank h] at hl
    exact Nat.le_antisymm hu hl
  · have hp : (R.subgroupOf M : Set M) * (S.toSubgroup.subgroupOf M : Set M) =
        (S.toSubgroup.subgroupOf M : Set M) * (R.subgroupOf M : Set M) := by
      apply M.subtype_injective.image_injective
      simpa only [Set.image_mul, ← coe_map, map_subgroupOf_eq_of_le hRM,
        map_subgroupOf_eq_of_le hSM, Sylow.coe_coe] using h.permutes
    change ((R.subgroupOf M).map f : Set M24) *
        ((S.toSubgroup.subgroupOf M).map f : Set M24) =
      ((S.toSubgroup.subgroupOf M).map f : Set M24) * ((R.subgroupOf M).map f : Set M24)
    simpa only [coe_map, Set.image_mul] using congrArg (Set.image f) hp

private theorem mathieu_pair_reducible (htrio : M24PairAction.ReducibleOrTrioPlacement)
    (S : Sylow 2 M24) (R : Subgroup M24) (h : PairInput S R) :
    PairReducible S.toSubgroup R := by
  rcases htrio S R h with hred | ⟨g, hg⟩
  · exact hred
  · obtain ⟨f, _, hk⟩ := M24PairAction.quotient_of_standard_trio
      M24PairAction.standardTrioQuotient g
    exact M24PairAction.pairReducible_of_local_quotient S.toSubgroup R h.oddComplement
      _ (le_sup_left.trans hg)
      ((M24PairAction.sylowNormalizerControl S).trans (le_sup_right.trans hg)) f hk

/-- Each supplied two-group actor on a pair in an actual max1-type overgroup
is reducible, conditional only on the corrected Mathieu pair alternative. -/
public theorem max1_localModelPairReducibility_of_mathieuAlternative
    (htrio : M24PairAction.ReducibleOrTrioPlacement) :
    LocalModelPairReducibility
      (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four) := by
  intro _ _ _ S R h M _ hSM hRM e D _ htwo hactions
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : M →* M24 := projection.comp e.toMonoidHom
  have hf : Function.Surjective f := projection_surjective.comp e.surjective
  have hk : IsPGroup 2 f.ker :=
    projection_ker_isPGroup.comap_of_injective e.toMonoidHom e.injective
  have hi : Function.Injective (f.comp (R.subgroupOf M).subtype) := by
    apply injective_comp_subtype_of_coprime_ker f _ _ h.oddComplement.isPGroup.comap_subtype
    obtain ⟨n, hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  let U := (R.subgroupOf M).map f
  let eR : R ≃* U := (subgroupOfEquivOfLe hRM).symm.trans
    (MulEquiv.ofBijective (f.subgroupMap (R.subgroupOf M))
      ⟨fun _ _ he => hi (congrArg Subtype.val he), f.subgroupMap_surjective _⟩)
  have heR (r : R) : (eR r : M24) = f (inclusion hRM r) := rfl
  let T := (S.subtype hSM).mapSurjective hf
  have hp : PairInput T U := quotient_pair_input h M hSM hRM f hf hk eR
  have hred := mathieu_pair_reducible htrio T U hp
  let a := MulAut.congr eR
  let D' := D.map a.toMonoidHom
  have hD' : D' ≤ pairAutomizer T.toSubgroup U := by
    rintro b ⟨b, hb, rfl⟩
    obtain ⟨c, hcS, hcR⟩ := hactions b hb
    obtain ⟨d, hd⟩ := exists_quotientActor (MulAut.congr e c)
    have hfd (x : M) : f (c x) = d (f x) := by
      change projection (e (c x)) = d (projection (e x))
      have hh := hd (e x)
      simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using hh
    refine ⟨d, ?_, ?_⟩
    · intro y
      constructor
      · rintro ⟨x, hx, he⟩
        refine ⟨c.symm x, ?_, ?_⟩
        · exact (hcS (c.symm x)).mp (by rwa [c.apply_symm_apply])
        · apply d.injective
          rw [← hfd, c.apply_symm_apply, he]
      · rintro ⟨x, hx, rfl⟩
        exact ⟨c x, (hcS x).mpr hx, hfd x⟩
    · intro y
      obtain ⟨r, rfl⟩ := eR.surjective y
      change (MulAut.congr eR b (eR r) : M24) = d (eR r)
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [heR, heR, hcR, hfd]
  obtain ⟨A, hAb, hAt, hA⟩ := hred D' hD' (htwo.map a.toMonoidHom)
  let q := frattiniEquiv eR
  refine ⟨A.comap q.toMonoidHom, ?_, ?_, ?_⟩
  · intro hb
    apply hAb
    have hh := congrArg (Subgroup.map q.toMonoidHom) hb
    rwa [map_comap_eq_self_of_surjective (f := q.toMonoidHom) q.surjective A,
      Subgroup.map_bot] at hh
  · intro ht
    apply hAt
    have hh := congrArg (Subgroup.map q.toMonoidHom) ht
    rwa [map_comap_eq_self_of_surjective (f := q.toMonoidHom) q.surjective A,
      map_top_of_surjective q.toMonoidHom q.surjective] at hh
  · intro b hb x hx
    change q (quotientAut (frattini R) b x) ∈ A
    rw [frattiniEquiv_equivariant]
    exact hA (a b) ⟨b, hb, rfl⟩ (q x) hx

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate
