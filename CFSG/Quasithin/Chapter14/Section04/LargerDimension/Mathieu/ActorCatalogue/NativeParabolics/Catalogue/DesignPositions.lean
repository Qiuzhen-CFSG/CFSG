module
public import Theory.GroupTheory.IndexTwoIntersection
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue.DesignContract
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PairQuotients
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation

/-!
# Exhaustion of the two Mathieu design positions

Every Sylow 2-subgroup of the full design automorphism group is conjugate to
one lying in the common pair--partition flag.  An index-three overgroup has
order 768; its even intersection with the normal M₂₂ subgroup has order 384.
The native M₂₂ solvable-Sylow classification places that intersection in the
unique invariant hexad, and the two maximal overgroups of the induced Sylow
subgroup in the actual A₆ restriction quotient are the pair--hexad and
three-pair parabolics.  An odd element of the ambient Sylow then recovers the
full outer subgroup from its even intersection.  The quotient witnesses use
the literal six-point action and the intrinsic two-core, with the pair case
factored through the duad model.

Source: Aschbacher--Smith, 14.4.12, printed pp.1011--1012; H.12.1(4),
printed pp.393--394; the A₆ parabolics are the calculation of I.5,
printed pp.419--422.  This module supplies the design classification input
for the native catalogue and does not use the binary representation.
-/

@[expose] public section
open Subgroup MulAction
open Sporadic.Mathieu
open M22ValueBound.Concrete M22ValueBound.Concrete.PartitionStructure
open M22SolvableSylow M22SolvableSylow.LocalClassification
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue

private lemma sylow_card (U : Sylow 2 m22DesignAut) : Nat.card U = 256 := by
  rw [U.card_eq_multiplicity, m22DesignAut_order]
  decide +kernel

private lemma sylow_not_le_inner (U : Sylow 2 m22DesignAut) :
    ¬ (U : Subgroup m22DesignAut) ≤ M22ValueBound.Concrete.inner := by
  intro h
  have hd := card_dvd_of_le h
  have hc : Nat.card M22ValueBound.Concrete.inner = 443520 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe M22_le_m22DesignAut).toEquiv, m22_order]
  rw [sylow_card U, hc] at hd
  norm_num at hd

private lemma card_double (U : Sylow 2 m22DesignAut) (Q : Subgroup m22DesignAut)
    (hUQ : (U : Subgroup m22DesignAut) ≤ Q) :
    Nat.card Q = Nat.card (Q.comap inclusion) * 2 := by
  have hi := M22ValueBound.Concrete.inner.subgroupOf_index_eq_two Q PartitionStructure.inner_index
    (fun h => sylow_not_le_inner U (hUQ.trans h))
  have hc := (M22ValueBound.Concrete.inner.subgroupOf Q).card_mul_index
  have hm1 : Nat.card (M22ValueBound.Concrete.inner.subgroupOf Q) =
      Nat.card (M22ValueBound.Concrete.inner ⊓ Q : Subgroup m22DesignAut) := by
    calc
      Nat.card (M22ValueBound.Concrete.inner.subgroupOf Q) =
          Nat.card ((M22ValueBound.Concrete.inner ⊓ Q).subgroupOf Q) := by
            rw [Subgroup.inf_subgroupOf_right]
      _ = Nat.card (M22ValueBound.Concrete.inner ⊓ Q : Subgroup m22DesignAut) :=
        Nat.card_congr (subgroupOfEquivOfLe (H := M22ValueBound.Concrete.inner ⊓ Q)
          (K := Q) inf_le_right).toEquiv
  have hm2 : Nat.card (Q.comap inclusion) =
      Nat.card (M22ValueBound.Concrete.inner ⊓ Q : Subgroup m22DesignAut) := by
    calc
      Nat.card (Q.comap inclusion) = Nat.card ((Q.comap inclusion).map inclusion) :=
        (card_map_of_injective M22ValueBound.Concrete.inclusion_injective).symm
      _ = Nat.card (M22ValueBound.Concrete.inner ⊓ Q : Subgroup m22DesignAut) := by
        rw [Subgroup.map_comap_eq, M22ValueBound.Concrete.inclusion_range]
  have hm : Nat.card (M22ValueBound.Concrete.inner.subgroupOf Q) =
      Nat.card (Q.comap inclusion) := hm1.trans hm2.symm
  rw [hm, hi] at hc
  exact hc.symm

private noncomputable def evenSylow (U : Sylow 2 m22DesignAut) : Sylow 2 M22 :=
  Sylow.ofCard ((U : Subgroup m22DesignAut).comap inclusion) (by
    have h := card_double U U le_rfl
    rw [sylow_card U] at h
    rw [m22_order]
    have he : 2 ^ (443520 : ℕ).factorization 2 = 128 := by decide +kernel
    rw [he]
    omega)

private lemma rank_one_card (U : Sylow 2 m22DesignAut) {Q : Subgroup m22DesignAut}
    (hQ : Q ∈ rankOneOvergroups U) : Nat.card Q = 768 := by
  have h := ((U : Subgroup m22DesignAut).subgroupOf Q).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hQ.1).toEquiv, sylow_card U] at h
  change 256 * (U : Subgroup m22DesignAut).relIndex Q = Nat.card Q at h
  rw [hQ.2] at h
  omega

private lemma pair_comap : outerPairHexad.comap inclusion = M22SolvableSylow.pairHexad := rfl

private lemma pair_card : Nat.card outerPairHexad = 768 := by
  have ho : oddElement ∈ outerPairHexad := by
    refine ⟨?_, oddElement_mem.1⟩
    change m22OddPairSwap • m22Hexad123 = m22Hexad123
    decide +kernel
  rw [outer_card_double _ ho, pair_comap, M22SolvableSylow.pairHexad_card]

private lemma rank_one_of_card (U : Sylow 2 m22DesignAut) {Q : Subgroup m22DesignAut}
    (hle : (U : Subgroup m22DesignAut) ≤ Q) (hc : Nat.card Q = 768) :
    Q ∈ rankOneOvergroups U := by
  refine ⟨hle, ?_⟩
  have h := ((U : Subgroup m22DesignAut).subgroupOf Q).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, sylow_card U, hc] at h
  change 256 * (U : Subgroup m22DesignAut).relIndex Q = 768 at h
  omega

private lemma eq_of_comap (U : Sylow 2 m22DesignAut) {P Q : Subgroup m22DesignAut}
    (hUP : (U : Subgroup m22DesignAut) ≤ P) (hUQ : (U : Subgroup m22DesignAut) ≤ Q)
    (he : P.comap inclusion = Q.comap inclusion) : P = Q := by
  classical
  obtain ⟨u, hu, hnu⟩ : ∃ u ∈ (U : Subgroup m22DesignAut), u ∉ M22ValueBound.Concrete.inner := by
    simpa only [SetLike.le_def, not_forall, exists_prop] using sylow_not_le_inner U
  have hi : M22ValueBound.Concrete.inner ⊓ P = M22ValueBound.Concrete.inner ⊓ Q := by
    simpa only [map_comap_eq, M22ValueBound.Concrete.inclusion_range] using congrArg (Subgroup.map inclusion) he
  have transfer (A B : Subgroup m22DesignAut) (huA : u ∈ A) (huB : u ∈ B)
      (he : M22ValueBound.Concrete.inner ⊓ A = M22ValueBound.Concrete.inner ⊓ B) : A ≤ B := by
    intro x hx
    by_cases hxi : x ∈ M22ValueBound.Concrete.inner
    · exact (show x ∈ M22ValueBound.Concrete.inner ⊓ B from he ▸ ⟨hxi, hx⟩).2
    · have hm : x * u ∈ M22ValueBound.Concrete.inner :=
        (M22ValueBound.Concrete.inner.mul_mem_iff_of_index_two PartitionStructure.inner_index).mpr
          (iff_of_false hxi hnu)
      have hB : x * u ∈ B := (show x * u ∈ M22ValueBound.Concrete.inner ⊓ B from
        he ▸ ⟨hm, A.mul_mem hx huA⟩).2
      simpa only [mul_inv_cancel_right] using B.mul_mem hB (B.inv_mem huB)
  exact le_antisymm (transfer P Q (hUP hu) (hUQ hu) hi)
    (transfer Q P (hUQ hu) (hUP hu) hi.symm)

private lemma rank_one_hexad (U : Sylow 2 m22DesignAut) {Q : Subgroup m22DesignAut}
    (hQ : Q ∈ rankOneOvergroups U) :
    ∃ B ∈ m22Blocks, Q ≤ stabilizer m22DesignAut B := by
  let X := Q.comap inclusion
  have hVX : (evenSylow U : Subgroup M22) ≤ X := comap_mono hQ.1
  have hc : Nat.card X = 384 := by
    have h := card_double U Q hQ.1
    rw [rank_one_card U hQ] at h
    change 768 = Nat.card X * 2 at h
    omega
  have hn : (X.subgroupOf X).Normal := by rw [subgroupOf_self]; infer_instance
  obtain ⟨B, hB, _, _, _, _, hnorm⟩ := hexad_of_solvable_normal_three X X le_rfl hn
    (solvable_of_card_384 X hc ⟨evenSylow U, hVX⟩) (hc ▸ (by decide : 3 ∣ 384))
    ⟨evenSylow U, hVX⟩
  refine ⟨B, hB, le_trans ?_ hnorm⟩
  have hm : X.map inclusion = M22ValueBound.Concrete.inner ⊓ Q := by rw [map_comap_eq, M22ValueBound.Concrete.inclusion_range]
  rw [hm]
  apply (normal_subgroupOf_iff_le_normalizer inf_le_right).mp
  have he : (M22ValueBound.Concrete.inner ⊓ Q).subgroupOf Q = M22ValueBound.Concrete.inner.subgroupOf Q := by
    rw [inf_subgroupOf_right]
  rw [he]
  infer_instance

private lemma coatom_image {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (X : Subgroup G) (hk : f.ker ≤ X) (hX : IsCoatom X) :
    IsCoatom (X.map f) := by
  refine ⟨?_, ?_⟩
  · intro he
    have he' := congrArg (Subgroup.comap f) he
    rw [comap_map_eq_self hk, comap_top] at he'
    exact hX.1 he'
  · intro Y hY
    have hl : X < Y.comap f := by
      rw [← comap_map_eq_self hk]
      exact (comap_lt_comap_of_surjective hf).mpr hY
    apply comap_injective hf
    rw [comap_top]
    exact hX.2 _ hl

private lemma inner_two_parabolics (V : Sylow 2 M22)
    (hVP : (V : Subgroup M22) ≤ M22SolvableSylow.pairHexad) (hVS : (V : Subgroup M22) ≤ second)
    (X : Subgroup M22) (hVX : (V : Subgroup M22) ≤ X)
    (hX : X ≤ stabilizer M22 m22Hexad123) (hc : Nat.card X = 384) :
    X = M22SolvableSylow.pairHexad ∨ X = second := by
  let H := stabilizer M22 m22Hexad123
  let f := hexadRestriction m22Hexad123_mem
  have hf := hexadRestriction_surjective m22Hexad123_mem
  let T : Sylow 2 H := V.subtype (hVP.trans inf_le_left)
  have hk : f.ker ≤ (T : Subgroup H) :=
    hexadRestriction_ker_le m22Hexad123_mem V (hVP.trans inf_le_left) ⟨V, le_rfl⟩
  let P := M22SolvableSylow.pairHexad.subgroupOf H
  let S := second.subgroupOf H
  let Y := X.subgroupOf H
  have hTP : (T : Subgroup H) ≤ P := fun _ hv => hVP hv
  have hTS : (T : Subgroup H) ≤ S := fun _ hv => hVS hv
  have hTY : (T : Subgroup H) ≤ Y := fun _ hv => hVX hv
  have hY : IsCoatom Y := isCoatom_of_card_384 m22Hexad123_mem X hX
    ((kernel_le_of_sylow m22Hexad123_mem V (hVP.trans inf_le_left)).trans hVX) hc
  obtain ⟨_, _, hclass⟩ := Theory.SpecificGroups.SymmetricSix.a6_coatoms_over_sylow
    (T.mapSurjective hf)
  have hp := (hclass (P.map f)).mp
    ⟨coatom_image f hf P (hk.trans hTP) M22SolvableSylow.pairHexad_isCoatom, map_mono hTP⟩
  have hs := (hclass (S.map f)).mp
    ⟨coatom_image f hf S (hk.trans hTS) second_isCoatom, map_mono hTS⟩
  have hy := (hclass (Y.map f)).mp
    ⟨coatom_image f hf Y (hk.trans hTY) hY, map_mono hTY⟩
  have hne : P.map f ≠ S.map f := by
    intro he
    have hi := map_injective_of_ker_le f (hk.trans hTP) (hk.trans hTS) he
    have heq := congrArg (Subgroup.map H.subtype) hi
    change (M22SolvableSylow.pairHexad.subgroupOf H).map H.subtype = (second.subgroupOf H).map H.subtype at heq
    rw [map_subgroupOf_eq_of_le (show M22SolvableSylow.pairHexad ≤ H from inf_le_left),
      map_subgroupOf_eq_of_le second_le_hexad] at heq
    exact second_not_le_pair m22Pair12 (by decide +kernel) (heq ▸ inf_le_right)
  have he : Y.map f = P.map f ∨ Y.map f = S.map f := by
    rcases hp with hp | hp <;> rcases hs with hs | hs <;>
      rcases hy with hy | hy <;> simp_all
  have lift (Z : Subgroup M22) (hZ : Z ≤ H) (hTZ : (T : Subgroup H) ≤ Z.subgroupOf H)
      (he : Y.map f = (Z.subgroupOf H).map f) : X = Z := by
    have hi := map_injective_of_ker_le f (hk.trans hTY) (hk.trans hTZ) he
    have hi' := congrArg (Subgroup.map H.subtype) hi
    change (X.subgroupOf H).map H.subtype = (Z.subgroupOf H).map H.subtype at hi'
    rw [map_subgroupOf_eq_of_le hX, map_subgroupOf_eq_of_le hZ] at hi'
    exact hi'
  exact he.imp (lift M22SolvableSylow.pairHexad inf_le_left hTP) (lift second second_le_hexad hTS)

private lemma standard_overgroups (U : Sylow 2 m22DesignAut)
    (hU : (U : Subgroup m22DesignAut) ≤ outerFirst ⊓ outerSecond) :
    rankOneOvergroups U = {outerSecond, outerPairHexad} := by
  have hUS := hU.trans inf_le_right
  have hHexad : outerSecond ≤ stabilizer m22DesignAut m22Hexad123 := by
    intro g hg
    change g • M22ValueBound.Concrete.hexadPartition = M22ValueBound.Concrete.hexadPartition at hg
    change g • m22Hexad123 = m22Hexad123
    rw [← M22ValueBound.Concrete.hexadPartition_union]
    have h : g • M22ValueBound.Concrete.hexadPartition.biUnion id =
        (g • M22ValueBound.Concrete.hexadPartition).biUnion id := by
      simp only [Finset.smul_finset_def, Finset.image_biUnion, Finset.biUnion_image]
      rfl
    rw [h, MulAction.mem_stabilizer_iff.mp hg]
  have hUP : (U : Subgroup m22DesignAut) ≤ outerPairHexad :=
    le_inf (hUS.trans hHexad) (hU.trans inf_le_left)
  have hVS : (evenSylow U : Subgroup M22) ≤ second := comap_mono hUS
  have hVP : (evenSylow U : Subgroup M22) ≤ M22SolvableSylow.pairHexad := comap_mono hUP
  ext Q
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hQ
    obtain ⟨B, hB, hQB⟩ := rank_one_hexad U hQ
    have hBstd : B = m22Hexad123 := invariant_six_eq_hexad m22Hexad123_mem B
      (m22Block_card B hB) ((kernel_le_of_sylow m22Hexad123_mem (evenSylow U)
        (hVS.trans second_le_hexad)).trans ((comap_mono hQ.1).trans (comap_mono hQB)))
    rw [hBstd] at hQB
    have hc : Nat.card (Q.comap inclusion) = 384 := by
      have h := card_double U Q hQ.1
      rw [rank_one_card U hQ] at h
      omega
    rcases inner_two_parabolics (evenSylow U) hVP hVS (Q.comap inclusion)
      (comap_mono hQ.1) (comap_mono hQB) hc with hp | hs
    · exact Or.inr (eq_of_comap U hQ.1 hUP hp)
    · exact Or.inl (eq_of_comap U hQ.1 hUS hs)
  · rintro (rfl | rfl)
    · exact rank_one_of_card U hUS outerSecond_card
    · exact rank_one_of_card U hUP pair_card

lemma exists_overgroups (U : Sylow 2 m22DesignAut) :
    ∃ g, rankOneOvergroups U = {partitionAt g, pairAt g} := by
  obtain ⟨V, hV⟩ := exists_sylow_le_outerFirst_inf_outerSecond
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq m22DesignAut V U
  let e := (MulAut.conj g).mapSubgroup
  have he : e (V : Subgroup m22DesignAut) = (U : Subgroup m22DesignAut) := by
    change ((g • V : Sylow 2 m22DesignAut) : Subgroup m22DesignAut) = _
    rw [hg]
  have hc := standard_overgroups V hV
  refine ⟨g, ?_⟩
  ext Q
  have hmem : Q ∈ rankOneOvergroups U ↔ e.symm Q ∈ rankOneOvergroups V := by
    constructor
    · rintro ⟨hle, hi⟩
      refine ⟨?_, ?_⟩
      · have h := e.symm.monotone hle
        rwa [← he, e.symm_apply_apply] at h
      · have h := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
          (V : Subgroup m22DesignAut) (e.symm Q)
            (fun x y hxy => (MulAut.conj g).injective hxy)
        change (e (V : Subgroup m22DesignAut)).relIndex (e (e.symm Q)) = _ at h
        rw [he, e.apply_symm_apply, hi] at h
        exact h.symm
    · rintro ⟨hle, hi⟩
      refine ⟨?_, ?_⟩
      · have h := e.monotone hle
        rwa [he, e.apply_symm_apply] at h
      · have h := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
          (V : Subgroup m22DesignAut) (e.symm Q)
            (fun x y hxy => (MulAut.conj g).injective hxy)
        change (e (V : Subgroup m22DesignAut)).relIndex (e (e.symm Q)) = _ at h
        rw [he, e.apply_symm_apply, hi] at h
        exact h
  rw [hmem, hc]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  change e.symm Q = outerSecond ∨ e.symm Q = outerPairHexad ↔
    Q = e outerSecond ∨ Q = e outerPairHexad
  constructor
  · exact Or.imp (fun h => (e.apply_symm_apply Q).symm.trans (congrArg e h))
      (fun h => (e.apply_symm_apply Q).symm.trans (congrArg e h))
  · exact Or.imp (fun h => by rw [h, e.symm_apply_apply])
      (fun h => by rw [h, e.symm_apply_apply])

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue

@[expose] public section
open Subgroup MulAction
open Sporadic.Mathieu
open M22ValueBound.Concrete
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue

def pointFourHom : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 5) :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin 1 ⊕ Fin 4 ≃ Fin 5)).toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom _ _).comp
      ((1 : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 1)).prod (MonoidHom.id _)))

def pointFourMap : Equiv.Perm (Fin 4) →*
    stabilizer (Equiv.Perm (Fin 5)) (0 : Fin 5) :=
  pointFourHom.codRestrict _ (by decide +kernel)

noncomputable def pointFourEquiv : Equiv.Perm (Fin 4) ≃*
    stabilizer (Equiv.Perm (Fin 5)) (0 : Fin 5) :=
  MulEquiv.ofBijective pointFourMap (by
    apply (Nat.bijective_iff_injective_and_card _).mpr
    constructor
    · intro x y h
      have hh : pointFourHom x = pointFourHom y := congrArg Subtype.val h
      exact (by decide +kernel : Function.Injective pointFourHom) hh
    · have hi : (stabilizer (Equiv.Perm (Fin 5)) (0 : Fin 5)).index = 5 := by
        simpa using (MulAction.index_stabilizer_of_transitive
          (Equiv.Perm (Fin 5)) (0 : Fin 5))
      have hc := (stabilizer (Equiv.Perm (Fin 5)) (0 : Fin 5)).card_mul_index
      have hgroup : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
        decide
      rw [hgroup, hi] at hc
      have hsub : Nat.card (stabilizer (Equiv.Perm (Fin 5)) (0 : Fin 5)) = 24 := by
        have hc' : Fintype.card (stabilizer (Equiv.Perm (Fin 5)) (0 : Fin 5)) * 5 = 120 := by
          simpa only [Nat.card_eq_fintype_card] using hc
        rw [Nat.card_eq_fintype_card]
        omega
      have hsub' : Fintype.card (stabilizer (Equiv.Perm (Fin 5)) (0 : Fin 5)) = 24 := by
        simpa only [Nat.card_eq_fintype_card] using hsub
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
        Nat.factorial]
      exact hsub'.symm)

private lemma standard_hexad_label : M22ValueBound.Concrete.pairHexad 0 = m22Hexad123 := by
  decide +kernel

noncomputable def pairRestriction : M22SolvableSylow.pairHexad →*
    stabilizer (Equiv.Perm (Fin 5)) (0 : Fin 5) :=
  (pairAction.comp (Subgroup.inclusion (show M22SolvableSylow.pairHexad ≤ first from inf_le_right))).codRestrict _ (by
    intro x
    apply M22ValueBound.Concrete.pairHexad_injective
    change M22ValueBound.Concrete.pairHexad (pairAction
      (Subgroup.inclusion (show M22SolvableSylow.pairHexad ≤ first from inf_le_right) x) 0) =
      M22ValueBound.Concrete.pairHexad 0
    rw [pairAction_spec, standard_hexad_label]
    exact x.property.1)

private lemma pairRestriction_surjective : Function.Surjective pairRestriction := by
  intro y
  obtain ⟨x, hx⟩ := pairAction_surjective y.val
  have hspec := pairAction_spec x 0
  rw [standard_hexad_label] at hspec
  have hleft : M22ValueBound.Concrete.pairHexad (pairAction x 0) =
      M22ValueBound.Concrete.pairHexad 0 := by
    rw [hx]
    exact congrArg M22ValueBound.Concrete.pairHexad y.property
  have hfix : x.val • m22Hexad123 = m22Hexad123 := by
    exact hspec.symm.trans hleft
  exact ⟨⟨x.val, hfix, x.property⟩, Subtype.ext hx⟩

noncomputable def pairThree : M22SolvableSylow.pairHexad →* Equiv.Perm (Fin 3) :=
  quotientHom.comp (pointFourEquiv.symm.toMonoidHom.comp pairRestriction)

lemma pairThree_surjective : Function.Surjective pairThree :=
  quotientHom_surjective.comp (pointFourEquiv.symm.surjective.comp pairRestriction_surjective)

noncomputable def pairQuotientEquiv :
    (M22SolvableSylow.pairHexad ⧸ pCore 2 M22SolvableSylow.pairHexad) ≃*
      Equiv.Perm (Fin 3) := by
  have hk : Nat.card pairThree.ker = 64 := by
    have h := pairThree.ker.card_mul_index
    rw [index_ker, pairThree.range_eq_top_of_surjective pairThree_surjective,
      card_top, M22SolvableSylow.pairHexad_card] at h
    have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [hc] at h
    omega
  have he := ker_eq_twoCore_of_surjective_perm_three pairThree pairThree_surjective
    (IsPGroup.of_card (n := 6) hk)
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective pairThree pairThree_surjective)

noncomputable def conjugateInnerEquiv (P : Subgroup m22DesignAut) (g : m22DesignAut) :
    (P.map (MulAut.conj g).toMonoidHom ⊓ M22ValueBound.Concrete.inner : Subgroup m22DesignAut) ≃*
      (P ⊓ M22ValueBound.Concrete.inner : Subgroup m22DesignAut) := by
  have he : (P ⊓ M22ValueBound.Concrete.inner).map (MulAut.conj g).toMonoidHom =
      P.map (MulAut.conj g).toMonoidHom ⊓ M22ValueBound.Concrete.inner := by
    have hn : M22ValueBound.Concrete.inner.map (MulAut.conj g).toMonoidHom =
        M22ValueBound.Concrete.inner :=
      Subgroup.Normal.map_conj_eq M22ValueBound.Concrete.inner g
    rw [map_inf _ _ _ (MulAut.conj g).injective, hn]
  exact (MulEquiv.subgroupCongr he.symm).trans
    ((P ⊓ M22ValueBound.Concrete.inner).equivMapOfInjective _ (MulAut.conj g).injective).symm

noncomputable def pairInnerEquiv :
    (outerPairHexad ⊓ M22ValueBound.Concrete.inner : Subgroup m22DesignAut) ≃*
      M22SolvableSylow.pairHexad := by
  have he : M22SolvableSylow.pairHexad.map inclusion =
      outerPairHexad ⊓ M22ValueBound.Concrete.inner := by
    change (outerPairHexad.comap inclusion).map inclusion = _
    rw [map_comap_eq, M22ValueBound.Concrete.inclusion_range, inf_comm]
  exact (MulEquiv.subgroupCongr he.symm).trans
    (M22SolvableSylow.pairHexad.equivMapOfInjective inclusion
      M22ValueBound.Concrete.inclusion_injective).symm

noncomputable def partitionAtQuotientEquiv (g : m22DesignAut) :
    ((partitionAt g ⊓ M22ValueBound.Concrete.inner : Subgroup m22DesignAut) ⧸
      pCore 2 (partitionAt g ⊓ M22ValueBound.Concrete.inner : Subgroup m22DesignAut)) ≃*
        Equiv.Perm (Fin 3) := by
  let e := (conjugateInnerEquiv outerSecond g).trans secondInnerEquiv
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans secondQuotientEquiv

noncomputable def pairAtQuotientEquiv (g : m22DesignAut) :
    ((pairAt g ⊓ M22ValueBound.Concrete.inner : Subgroup m22DesignAut) ⧸
      pCore 2 (pairAt g ⊓ M22ValueBound.Concrete.inner : Subgroup m22DesignAut)) ≃*
        Equiv.Perm (Fin 3) := by
  let e := (conjugateInnerEquiv outerPairHexad g).trans pairInnerEquiv
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans pairQuotientEquiv

/-- Every Sylow 2-subgroup of the full design automorphism group has the
 two native index-three overgroups in common hexad coordinates. The two
 quotient maps are the literal intrinsic two-core quotients of their even
 intersections. -/
lemma exists_design_catalogue (U : Sylow 2 m22DesignAut) :
    ∃ g : m22DesignAut, DesignCatalogueAt U g := by
  obtain ⟨g, hg⟩ := exists_overgroups U
  refine ⟨g, ⟨hg, ⟨partitionAtQuotientEquiv g⟩, ⟨pairAtQuotientEquiv g⟩⟩⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue
