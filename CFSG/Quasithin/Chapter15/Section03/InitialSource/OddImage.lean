module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.LocalAction
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.PResidual.PrimeToAction
public import Theory.GroupAction.QuotientConjugation
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The original odd quotient-action reduction of 14.1.8

Let a maximal two-local M contain the original Sylow T, and suppose Mc is
its specified unique maximal two-local over C_G(Ω₁(Z(T))). If X has odd
image in M/C_M(U), that image is normalized by the image of T, and X is
not contained in Mc, then U=[U,X] for every reduced module U of M.

Normalization is retained only in the quotient. The preimage of the image
of X is X C_M(U), which has the same fixed points on U as X. A nonzero
fixed subgroup would therefore contain a nonidentity central involution of
T. Its full centralizer is two-local and contained in Mc, a contradiction.
The actual conjugation image has odd order, so coprime splitting gives the
commutator equality even when X itself has even order.

The final consumer constructs elementary abelianness of the original
localModule from characteristic two, then applies the result to the literal
localActionMap and localActionImage of Section 15.3. Its quotient comparison
is induced by equality of the actual centralizer kernels. Neither solvability
of M nor a natural-module marking is assumed.

Source: Aschbacher–Smith, Lemma 14.1.8, printed p.977, and the Chapter 15
convention V(M)=⟨Ω₁(Z(T))ᴹ⟩, printed pp.1083 and 1120–1121.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
variable {G : Type*} [Group G] [Finite G]

/-- A nonidentity central involution has its full centralizer inside Mc. -/
theorem central_involution_centralizer_le_partner (T : Sylow 2 G) {Mc : Subgroup G}
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {z : G} (hz : z ∈ centralInvolutions T) (hne : z ≠ 1) :
    centralizer ({z} : Set G) ≤ Mc := by
  have hz2 := ((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.1
  have hlocal := isTwoLocal_involution_centralizer (orderOf_eq_prime hz2 hne)
  obtain ⟨N, hCN, hN⟩ := Finite.exists_le_maximal hlocal
  have hZN : centralizer (centralInvolutions T : Set G) ≤ N :=
    (centralizer_le (Set.singleton_subset_iff.mpr hz)).trans hCN
  have hNM : N = Mc := Set.mem_singleton_iff.mp (hunique ▸ ⟨hN, hZN⟩)
  exact hNM ▸ hCN

omit [Finite G] in
private theorem normalizes_fixed_of_image (U X S : Subgroup G) [U.Normal]
    (hn : S.map (QuotientGroup.mk' (centralizer (U : Set G))) ≤
      normalizer (X.map (QuotientGroup.mk' (centralizer (U : Set G))) : Set _)) :
    S ≤ normalizer (U ⊓ centralizer (X : Set G) : Subgroup G) := by
  let N := centralizer (U : Set G)
  let q := QuotientGroup.mk' N
  have hSY : S ≤ normalizer ((X.map q).comap q : Subgroup G) :=
    ((map_le_iff_le_comap).mp hn).trans (le_normalizer_comap q)
  have hY : (X.map q).comap q = X ⊔ N := by
    rw [comap_map_eq, QuotientGroup.ker_mk']
  have hC : U ⊓ centralizer (X ⊔ N : Subgroup G) = U ⊓ centralizer (X : Set G) := by
    apply le_antisymm (inf_le_inf_left _ (centralizer_le (show X ≤ X ⊔ N from le_sup_left)))
    apply le_inf inf_le_left
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp (inf_le_left.trans (le_centralizer_iff.mp le_rfl)))
  rw [hY] at hSY
  rw [← hC]
  exact (le_inf (le_normalizer_of_normal : S ≤ normalizer (U : Set G))
    (hSY.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf

/-- Quotient normalization suffices for the original fixed-point obstruction. -/
theorem fixed_eq_bot_of_image_normalized (T : Sylow 2 G) {M Mc : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (U X : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (hn : ((T.subtype hTM : Sylow 2 M) : Subgroup M).map
      (QuotientGroup.mk' (centralizer (U : Set M))) ≤
      normalizer (X.map (QuotientGroup.mk' (centralizer (U : Set M))) : Set _))
    (hescape : ¬ X.map M.subtype ≤ Mc) : U ⊓ centralizer (X : Set M) = ⊥ := by
  classical
  let S := T.subtype hTM
  let C := U ⊓ centralizer (X : Set M)
  change C = ⊥
  by_contra hC
  have hCS : C ≤ (S : Subgroup M) :=
    inf_le_left.trans ((IsElementaryAbelian.isPGroup 2 U).le_sylow_of_normal S)
  have hSn : (S : Subgroup M) ≤ normalizer C := normalizes_fixed_of_image U X S hn
  let : (C.subgroupOf (S : Subgroup M)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCS).mpr hSn
  let : Nontrivial C := (nontrivial_iff_ne_bot C).mpr hC
  let : Nontrivial (C.subgroupOf (S : Subgroup M)) :=
    (subgroupOfEquivOfLe hCS).toEquiv.nontrivial
  let : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  obtain ⟨z, hzne, hzcenter⟩ :=
    exists_nontrivial_center_mem_normal (C.subgroupOf (S : Subgroup M)) (p := 2)
  have hzU : ((z : S) : M) ∈ U := z.property.1
  have hzX : ((z : S) : M) ∈ centralizer (X : Set M) := z.property.2
  have hzZ : (((z : S) : M) : G) ∈ centralInvolutions T := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨(z : S).property, ?_, ?_⟩
    · exact congrArg M.subtype (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hzU)
    · intro t ht
      exact congrArg M.subtype (congrArg Subtype.val
        ((mem_center_iff.mp hzcenter) (⟨⟨t,hTM ht⟩, ht⟩ : S)))
  have hzGne : (((z : S) : M) : G) ≠ 1 :=
    fun he => hzne (Subtype.ext (Subtype.ext (Subtype.ext he)))
  apply hescape
  apply le_trans _ (central_involution_centralizer_le_partner T hunique hzZ hzGne)
  rintro x ⟨y, hy, rfl⟩
  exact mem_centralizer_singleton_iff.mpr (congrArg M.subtype (hzX y hy))


private theorem coprime_image_of_odd_centralizer_quotient
    (U X : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hodd : Odd (Nat.card (X.map (QuotientGroup.mk' (centralizer (U : Set G)))))) :
    Nat.Coprime (Nat.card (U.normalizerMonoidHom.comp
      (inclusion (le_normalizer_of_normal : X ≤ normalizer (U : Set G)))).range)
      (Nat.card U) := by
  let N := centralizer (U : Set G)
  let q := QuotientGroup.mk' N
  let a := MulAut.quotientConjNormal U N le_rfl
  let f := U.normalizerMonoidHom.comp
    (inclusion (le_normalizer_of_normal : X ≤ normalizer (U : Set G)))
  have he : f = a.comp (q.comp X.subtype) := by
    ext x v
    rfl
  have hr : f.range = (X.map q).map a := by
    rw [he, MonoidHom.range_comp, MonoidHom.range_comp, range_subtype]
  have hfo : Odd (Nat.card f.range) := by
    rw [hr]
    exact hodd.of_dvd_nat (card_map_dvd _ a)
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
  rw [hn]
  exact hfo.coprime_two_right.pow_right n

/-- The odd image acts fully on the original normal elementary module. -/
theorem eq_commutator_of_odd_image (T : Sylow 2 G) {M Mc : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (U X : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (hn : ((T.subtype hTM : Sylow 2 M) : Subgroup M).map
      (QuotientGroup.mk' (centralizer (U : Set M))) ≤
      normalizer (X.map (QuotientGroup.mk' (centralizer (U : Set M))) : Set _))
    (hodd : Odd (Nat.card (X.map (QuotientGroup.mk' (centralizer (U : Set M))))))
    (hescape : ¬ X.map M.subtype ≤ Mc) : U = ⁅U,X⁆ := by
  have hfixed := fixed_eq_bot_of_image_normalized T hTM hunique U X hn hescape
  have hd := (commutator_centralizer_decomposition_of_coprime_image U X
    le_normalizer_of_normal (coprime_image_of_odd_centralizer_quotient U X hodd)).1
  rw [hfixed, sup_bot_eq] at hd
  exact hd.symm

/-- Source 14.1.8 for an arbitrary actual reduced module, embedded back into G. -/
theorem source_lemma_14_1_8 (T : Sylow 2 G) {M Mc : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (U X : Subgroup M) (hU : IsPReduced 2 U) :
    letI := hU.normal
    let q := QuotientGroup.mk' (centralizer (U : Set M))
    ((T.subtype hM.2 : Sylow 2 M) : Subgroup M).map q ≤ normalizer (X.map q : Set _) →
    Odd (Nat.card (X.map q)) →
    ¬ X.map M.subtype ≤ Mc →
    U.map M.subtype = ⁅U.map M.subtype, X.map M.subtype⁆ := by
  let := hU.normal
  let := hU.elementary
  dsimp only
  intro hn hodd hescape
  rw [← map_commutator]
  exact congrArg (map M.subtype) (eq_commutator_of_odd_image T hM.2 hunique U X hn hodd hescape)


/-- Characteristic two makes the original conjugate-span module elementary. -/
theorem localModule_elementary_from_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : M ∈ Chapter1.HOver G (T : Set G)) :
    IsElementaryAbelian 2 (localModule T M) := by
  let W := omegaOneCenterAmbient (pCore 2 M)
  let : (omega₁ (center (pCore 2 M)) (p := 2)).Characteristic := omega₁_characteristic _
  let : ((omega₁ (center (pCore 2 M)) (p := 2)).map
    (center (pCore 2 M)).subtype).Characteristic := inferInstance
  let : W.Normal := ConjAct.normal_of_characteristic_of_normal
  have hn : M ≤ normalizer (W.map M.subtype : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      W.le_normalizer_map M.subtype
  have hVW : localModule T M ≤ W.map M.subtype :=
    conjugateSpanBy_le (centralInvolutions_le_omegaCore hG T hM) hn
  let : IsElementaryAbelian 2 W := omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 (W.map M.subtype) := IsElementaryAbelian.map M.subtype
  exact IsElementaryAbelian.of_le hVW


/-- The Section 15.3 consumer with its literal ambient subgroup and quotient map. -/
theorem localModule_eq_commutator_of_odd_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc X : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hXM : X ≤ M)
    (hn : localActionImage (centralInvolutions T) M (T : Subgroup G) ≤
      normalizer (localActionImage (centralInvolutions T) M X : Set _))
    (hodd : Odd (Nat.card (localActionImage (centralInvolutions T) M X)))
    (hescape : ¬ X ≤ Mc) : localModule T M = ⁅localModule T M, X⁆ := by
  have hVM : localModule T M ≤ M := conjugateSpanBy_le_self
    (fun z hz => hM.2 ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1)
  let U := (localModule T M).subgroupOf M
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy (centralInvolutions T) M)
  let : IsElementaryAbelian 2 (localModule T M) :=
    localModule_elementary_from_source hG T ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1, hM.2⟩
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVM
  have hK : centralizer (U : Set M) = localActionKernel (centralInvolutions T) M := by
    ext m
    constructor
    · intro hm v hv
      exact congrArg M.subtype (hm ⟨v,hVM hv⟩ hv)
    · intro hm v hv
      exact Subtype.ext (hm v hv)
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let e := QuotientGroup.quotientMulEquivOfEq hK
  have hcomp : e.toMonoidHom.comp q = localActionMap (centralInvolutions T) M := by
    ext x
    exact QuotientGroup.quotientMulEquivOfEq_mk hK x
  have hn' : ((T.subtype hM.2 : Sylow 2 M) : Subgroup M).map q ≤
      normalizer ((X.subgroupOf M).map q : Set _) := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [map_normalizer_eq_of_bijective _ e.bijective, map_map, map_map, hcomp]
    exact hn
  have hodd' : Odd (Nat.card ((X.subgroupOf M).map q)) := by
    rw [← card_map_of_injective (f := e.toMonoidHom) e.injective (K := (X.subgroupOf M).map q), map_map, hcomp]
    exact hodd
  have hesc' : ¬ (X.subgroupOf M).map M.subtype ≤ Mc := by
    rwa [map_subgroupOf_eq_of_le hXM]
  have he := congrArg (map M.subtype)
    (eq_commutator_of_odd_image T hM.2 hunique U (X.subgroupOf M) hn' hodd' hesc')
  simpa only [U, map_commutator, map_subgroupOf_eq_of_le hVM,
    map_subgroupOf_eq_of_le hXM] using he

end CFSG.Quasithin.Chapter15.Section03.InitialSource
