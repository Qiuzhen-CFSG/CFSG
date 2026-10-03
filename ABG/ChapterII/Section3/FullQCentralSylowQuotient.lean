module
public import ABG.ChapterII.Section3.CentralSylowDihedralQuotient
public import ABG.ChapterII.Section3.CoreFreeCentralQuotient
public import ABG.ChapterII.Section2.QDefinitionEquivalence
public import ABG.ChapterII.Section1.NormalQuaternionCenter

/-!
# Central Sylow quotients from full Q fusion patterns

Let G be a finite group with a full Q fusion pattern and trivial odd core.
If the center of one Sylow two-subgroup is central in G, the center of every
Sylow two-subgroup is central, by Sylow conjugacy. For the Sylow witness S
in the full fusion pattern, quotienting by its ambient center image N gives
a group with dihedral Sylow two-subgroups, trivial odd core, and a normal
index-two subgroup having no normal subgroup of index two.

Retain the normal subgroup K in the actual fusion pattern. Its index equals
the order of Z(S). Its Sylow intersection with S is generalized quaternion
and normal in S, so that intersection meets Z(S) in order two. The subgroup
index formulas now give index two for the image of K in G/N. Pullback of
normal subgroups along the restricted quotient map preserves the absence
of index two. The previously proved dihedral Sylow quotient and central
odd-core quotient theorems give the remaining clauses.

The construction is also exposed for any chosen normal quaternion witness,
so the enlarged-Q extraction can use the same quotient argument.
This is a restricted prerequisite for ABG Chapter II Section 3 Proposition 2,
article p22 of the Alperin--Brauer--Gorenstein paper, using the full fusion
pattern supplied by the involution-centralizer construction. The general
enlarged-Q version remains a separate theorem. In particular, normality of
S intersect K is used in S; the printed assertion of normality in K is
unnecessary and is not assumed.
-/

namespace ABG
variable {G : Type*} [Group G] [Finite G]

private theorem quotient_index (K N : Subgroup G) [K.Normal] [N.Normal]
    (hindex : K.index = Nat.card N) (hcap : Nat.card (K ⊓ N : Subgroup G) = 2) :
    (K.map (QuotientGroup.mk' N)).index = 2 := by
  have hcap' : Nat.card (K.subgroupOf N) = 2 := by
    let e : K.subgroupOf N ≃* (K ⊓ N : Subgroup G) := {
      toFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
    exact (Nat.card_congr e.toEquiv).trans hcap
  have hc := (K.subgroupOf N).card_mul_index
  change Nat.card (K.subgroupOf N) * K.relIndex N = Nat.card N at hc
  rw [hcap'] at hc
  have ht : 0 < K.relIndex N := by
    have hp := Nat.card_pos (α := N)
    omega
  have hi := K.relIndex_mul_index (show K ≤ K ⊔ N from le_sup_left)
  rw [Subgroup.relIndex_sup_left, hindex, ← hc] at hi
  have hj : (K ⊔ N).index = 2 :=
    Nat.eq_of_mul_eq_mul_left ht (by simpa [Nat.mul_comm] using hi)
  rw [Subgroup.index_map, QuotientGroup.ker_mk',
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N),
    Subgroup.index_top, mul_one, hj]

omit [Finite G] in
private theorem center_intersection (S : Sylow 2 G) (K N : Subgroup G)
    [K.Normal] (hN : N = subgroupCenter (S : Subgroup G))
    (hQ : IsGeneralizedQuaternionGroup (K.comap (S : Subgroup G).subtype)) :
    Nat.card (K ⊓ N : Subgroup G) = 2 := by
  let Q : Subgroup S := K.comap (S : Subgroup G).subtype
  have hcard := normal_quaternion_inf_center_card Q hQ
  have hNle : N ≤ (S : Subgroup G) := by
    rw [hN]
    exact Subgroup.map_subtype_le _
  have heq : (Q ⊓ Subgroup.center S).map (S : Subgroup G).subtype = K ⊓ N := by
    rw [Subgroup.map_inf _ _ _ (S : Subgroup G).subtype_injective]
    change (K.comap (S : Subgroup G).subtype).map (S : Subgroup G).subtype ⊓
      subgroupCenter (S : Subgroup G) = K ⊓ N
    rw [Subgroup.map_comap_eq, (S : Subgroup G).range_subtype, ← hN,
      inf_assoc]
    exact inf_eq_right.mpr (inf_le_right.trans hNle)
  rw [← heq, Subgroup.card_map_of_injective (S : Subgroup G).subtype_injective]
  exact hcard

omit [Finite G] in
private theorem no_index_two_image {H : Type*} [Group H]
    (f : G →* H) (K : Subgroup G) (hK : HasNoNormalIndexTwoSubgroup K) :
    HasNoNormalIndexTwoSubgroup (K.map f) := by
  intro L hL hindex
  let : L.Normal := hL
  let g := f.subgroupMap K
  have hi := L.index_comap_of_surjective (f.subgroupMap_surjective K)
  exact hK (L.comap g) inferInstance (hi.trans hindex)

omit [Finite G] in
private theorem center_cyclic_nontrivial (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S) :
    IsCyclic (Subgroup.center S) ∧ Nat.card (Subgroup.center S) ≠ 1 := by
  rcases hS with hs | ⟨n, hn⟩
  · have hc := QuasiDihedral.card_center hs
    exact ⟨isCyclic_of_prime_card hc, by omega⟩
  · obtain ⟨P⟩ := Wreathed.nonempty_presentation hn
    exact ⟨P.center_cyclic, by
      rw [P.card_center]
      have := P.height
      have hp : 2 ≤ 2 ^ n := by
        simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
      omega⟩

/-- A normal quaternion witness of the required index gives all central
Sylow quotient data used in ABG II.3 Proposition 2. -/
public theorem central_sylow_quotient_data_of_normal_quaternion
    (S : Sylow 2 G) (K N : Subgroup G) [K.Normal] [N.Normal]
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S)
    (hK : HasGeneralizedQuaternionSylowTwo K) (hno : HasNoNormalIndexTwoSubgroup K)
    (hi : K.index = Nat.card (Subgroup.center S))
    (hN : N = subgroupCenter (S : Subgroup G))
    (hcentral : N ≤ Subgroup.center G) (hcore : pPrimeCore 2 G = ⊥) :
    IsCyclic N ∧ N ≠ ⊥ ∧ GorensteinWalter.HasDihedralSylowTwo (G ⧸ N) ∧
      pPrimeCore 2 (G ⧸ N) = ⊥ ∧
      ∃ J : Subgroup (G ⧸ N), J.Normal ∧ J.index = 2 ∧ HasNoNormalIndexTwoSubgroup J := by
  let eZ : Subgroup.center S ≃* N :=
    (Subgroup.equivMapOfInjective _ (S : Subgroup G).subtype
      (S : Subgroup G).subtype_injective).trans (MulEquiv.subgroupCongr hN.symm)
  obtain ⟨hcyclic, hne⟩ := center_cyclic_nontrivial S hS
  have hcardN : Nat.card N = Nat.card (Subgroup.center S) :=
    (Nat.card_congr eZ.toEquiv).symm
  have hNtwo : IsPGroup 2 N :=
    IsPGroup.of_equiv (S.isPGroup'.to_subgroup (Subgroup.center S)) eZ
  refine ⟨eZ.isCyclic.mp hcyclic, ?_,
    hasDihedralSylowTwo_quotient_sylow_center S N hN hS,
    oddCore_quotient_eq_bot_of_central_two_subgroup N hcentral hNtwo hcore, ?_⟩
  · intro hbot
    have hc : Nat.card N = 1 := by simp [hbot]
    exact hne (hcardN.symm.trans hc)
  · let q := QuotientGroup.mk' N
    refine ⟨K.map q, Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective N),
      quotient_index K N (hi.trans hcardN.symm) ?_, no_index_two_image q K hno⟩
    exact center_intersection S K N hN
      (normal_sylow_intersection_isGeneralizedQuaternion S K hK)

/-- The central Sylow quotient of a core-free full Q-group has the index-two
subgroup needed for the dihedral classification step. -/
public theorem fullQGroup_central_sylow_quotient_data
    (hQ : IsFullSylowQGroup G) (R : Sylow 2 G)
    (hcentral : subgroupCenter (R : Subgroup G) ≤ Subgroup.center G)
    (hcore : pPrimeCore 2 G = ⊥) :
    ∃ (S : Sylow 2 G) (N : Subgroup G) (hNnormal : N.Normal),
      letI := hNnormal
      N = subgroupCenter (S : Subgroup G) ∧ IsCyclic N ∧ N ≠ ⊥ ∧
        GorensteinWalter.HasDihedralSylowTwo (G ⧸ N) ∧
        pPrimeCore 2 (G ⧸ N) = ⊥ ∧
        ∃ J : Subgroup (G ⧸ N), J.Normal ∧ J.index = 2 ∧ HasNoNormalIndexTwoSubgroup J := by
  have hchosen : ∃ (S : Sylow 2 G) (K : Subgroup G),
      K.Normal ∧ (Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S) ∧
      HasGeneralizedQuaternionSylowTwo K ∧ HasNoNormalIndexTwoSubgroup K ∧
      K.index = Nat.card (Subgroup.center S) := by
    rcases hQ with ⟨S, T, Q, hframe, hpattern⟩ | ⟨S, n, U, V, hframe, hpattern⟩
    · obtain ⟨K, hn, hi, hK, hno⟩ := hpattern.1
      exact ⟨S, K, hn, Or.inl hframe.1, hK, hno,
        hi.trans (QuasiDihedral.card_center hframe.1).symm⟩
    · obtain ⟨K, hn, hi, hK, hno⟩ := hpattern.1
      obtain ⟨P⟩ := Wreathed.nonempty_presentation hframe.1
      exact ⟨S, K, hn, Or.inr ⟨n, hframe.1⟩, hK, hno, hi.trans P.card_center.symm⟩
  obtain ⟨S, K, hKnormal, hS, hK, hno, hi⟩ := hchosen
  let : K.Normal := hKnormal
  let N := subgroupCenter (S : Subgroup G)
  have hNZ : N ≤ Subgroup.center G := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R S
    have hmap : (R : Subgroup G).map (MulAut.conj g).toMonoidHom = (S : Subgroup G) :=
      congrArg (fun T : Sylow 2 G => (T : Subgroup G)) hg
    change subgroupCenter (S : Subgroup G) ≤ Subgroup.center G
    rw [← hmap, subgroupCenter_map]
    exact (Subgroup.map_mono hcentral).trans
      (Subgroup.Normal.map_conj_eq (Subgroup.center G) g).le
  have hNnormal : N.Normal := by
    constructor
    intro x hx g
    have hxg := Subgroup.mem_center_iff.mp (hNZ hx) g
    simpa [hxg, mul_assoc] using hx
  let : N.Normal := hNnormal
  exact ⟨S, N, hNnormal, rfl,
    central_sylow_quotient_data_of_normal_quaternion S K N hS hK hno hi rfl hNZ hcore⟩
end ABG
