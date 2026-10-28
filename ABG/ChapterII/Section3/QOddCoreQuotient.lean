module

public import ABG.ChapterII.Section2.QDefinitionEquivalence
public import FeitThompson.PCore.PPrimeCore

/-!
# Enlarged Q-groups modulo normal odd subgroups

The quotient of a finite Q-group by a normal subgroup of odd order is again
a Q-group. In particular this applies to the odd core, without assuming that
the Sylow subgroup itself is semidihedral or wreathed.

Use the quaternion-overgroup form of the enlarged definition and keep its
actual overgroup and largest quaternion subgroup. The quotient map restricts
to an isomorphism on the chosen Sylow subgroup. The odd kernel lies in the
normal two-power-index witness, so its image retains that index, the absence
of normal index-two subgroups, and exactly the same quaternion intersection
under the transported embedding. The center of the Sylow image lifts through
this isomorphism; the weak-closure quotient theorem handles every subgroup
of that center.

This proves the quotient reduction in Alperin--Brauer--Gorenstein, II.3
Proposition 1 (article p21), also used in Lemma 1 (article p23). The source's
sentence introducing K before taking its image is read as K in the original
group, as required by its defining Q-witness and the subsequent barred K.
-/

namespace ABG
universe u

public theorem IsQGroup.quotient_of_coprime
    {G : Type u} [Group G] [Finite G] (hG : IsQGroup G)
    (N : Subgroup G) [N.Normal] (hN : Nat.Coprime 2 (Nat.card N)) :
    IsQGroup (G ⧸ N) := by
  obtain ⟨S, iS, hS, R, f, Y, K, hf, hY, hKN, ⟨m, hKi⟩, hKno, hRweak, hlink⟩ :=
    isQGroup_iff_quaternionOvergroup.mp hG
  let : Group S := iS
  let : K.Normal := hKN
  let q := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hNK : N ≤ K := by
    apply Subgroup.relIndex_eq_one.mp
    apply Nat.eq_one_of_dvd_coprimes (hN.pow_left m)
    · rw [← hKi]
      exact Subgroup.relIndex_dvd_index_of_normal (H := K) (K := N)
    · exact Subgroup.relIndex_dvd_card _ _
  have hqker : q.ker ≤ K := by
    rw [show q.ker = N from QuotientGroup.ker_mk' N]
    exact hNK
  let Rbar : Sylow 2 (G ⧸ N) := R.mapSurjective (f := q) hq
  have hRbar : (Rbar : Subgroup (G ⧸ N)) = (R : Subgroup G).map q :=
    Sylow.coe_mapSurjective _ _
  let r : R →* Rbar := {
    toFun := fun x => ⟨q x, by rw [hRbar]; exact Subgroup.mem_map_of_mem q x.property⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' := fun x y => Subtype.ext (map_mul q (x : G) (y : G)) }
  have hrinj : Function.Injective r := by
    have hdis : Disjoint (R : Subgroup G) N := by
      apply Subgroup.disjoint_of_coprime_natCard
      obtain ⟨n, hn⟩ := R.isPGroup'.exists_card_eq
      rw [hn]
      exact hN.pow_left n
    apply (MonoidHom.ker_eq_bot_iff r).mp
    apply bot_unique
    intro x hx
    have hxq : q (x : G) = 1 := congrArg Subtype.val hx
    have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).mp hxq
    exact Subtype.ext (Subgroup.disjoint_def.mp hdis x.property hxN)
  have hrsurj : Function.Surjective r := by
    rintro ⟨x, hx⟩
    rw [hRbar] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨⟨a, ha⟩, rfl⟩
  let e : R ≃* Rbar := MulEquiv.ofBijective r ⟨hrinj, hrsurj⟩
  have he (x : R) : (e x : G ⧸ N) = q x := rfl
  let Kbar := K.map q
  have hKbarN : Kbar.Normal := hKN.map q hq
  have hKbarI : Kbar.index = 2 ^ m := (K.index_map_eq hq hqker).trans hKi
  let qK : K →* Kbar := {
    toFun := fun x => ⟨q x, Subgroup.mem_map_of_mem q x.property⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' := fun x y => Subtype.ext (map_mul q (x : G) (y : G)) }
  have hqK : Function.Surjective qK := by
    rintro ⟨x, k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  have hKbarNo : HasNoNormalIndexTwoSubgroup Kbar := by
    intro A hAN hAi
    let : A.Normal := hAN
    exact hKno (A.comap qK) inferInstance
      ((A.index_comap_of_surjective hqK).trans hAi)
  have hRbarWeak : HasWeaklyClosedCenterSubgroups (Rbar : Subgroup (G ⧸ N)) := by
    intro Z hZ
    have hcenter : subgroupCenter (Rbar : Subgroup (G ⧸ N)) ≤
        (subgroupCenter (R : Subgroup G)).map q := by
      rintro x ⟨x, hx, rfl⟩
      refine ⟨e.symm x, ?_, ?_⟩
      · exact ⟨e.symm x, (Subgroup.centerCongr e.symm ⟨x, hx⟩).property, rfl⟩
      · exact (he (e.symm x)).symm.trans (congrArg Subtype.val (e.apply_symm_apply x))
    have h := hRweak.weaklyClosedIn_of_le_map q hq Z (hZ.trans hcenter)
    rwa [← hRbar] at h
  have hinter : (Kbar.comap (Rbar : Subgroup (G ⧸ N)).subtype).map e.symm.toMonoidHom =
      K.comap (R : Subgroup G).subtype := by
    rw [Subgroup.map_equiv_eq_comap_symm' e.symm]
    ext x
    change (e x : G ⧸ N) ∈ Kbar ↔ (x : G) ∈ K
    rw [he]
    exact SetLike.ext_iff.mp (Subgroup.comap_map_eq_self hqker) (x : G)
  apply isQGroup_iff_quaternionOvergroup.mpr
  refine ⟨S, iS, hS, Rbar, f.comp e.symm.toMonoidHom, Y, Kbar,
    hf.comp e.symm.injective, hY, hKbarN, ⟨m, hKbarI⟩, hKbarNo, hRbarWeak, ?_⟩
  rw [← Subgroup.map_map, hinter, hlink]

public theorem IsQGroup.oddCore_quotient
    {G : Type u} [Group G] [Finite G] (hG : IsQGroup G) :
    IsQGroup (G ⧸ pPrimeCore 2 G) :=
  hG.quotient_of_coprime (pPrimeCore 2 G) pPrimeCore_coprime_card

end ABG
