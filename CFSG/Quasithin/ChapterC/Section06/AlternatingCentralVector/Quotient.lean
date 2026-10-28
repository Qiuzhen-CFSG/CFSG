module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.ModelSplit
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.ElementaryAbelian.Injective

/-!
# The literal transposition quotient in C.6.4

The specified map H → S₇ identifies R/Q with the marked transposition
subgroup. Its kernel is precisely the restriction of the ambient core.
The residual image is A₇, so the odd transposition also proves H = K R.
These are the quotient and generation inputs for C.6.3.

Source: Aschbacher–Smith C.6.4(I), proof on printed p.168.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
variable {G : Type*} [Group G] [Finite G] {K R S Λ : Subgroup G}

omit [Finite G] in
theorem Input.quotientMap_surjective (d : Input K R S Λ) :
    Function.Surjective d.quotientMap :=
  d.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem Input.quotientMap_ker (d : Input K R S Λ) :
    d.quotientMap.ker = pCore 2 (K ⊔ S : Subgroup G) := by
  rw [Input.quotientMap, MonoidHom.ker_comp_of_injective _ _ d.quotientIso.injective,
    QuotientGroup.ker_mk']

/-- The first isomorphism theorem retains the supplied transposition marking. -/
def Input.quotientEquivTransposition (d : Input K R S Λ) :
    letI := d.core_normal_in_R
    (R ⧸ ((K ⊔ S).pCoreIn 2).subgroupOf R) ≃*
      zpowers (Equiv.swap (0 : Fin 7) 1) := by
  letI := d.core_normal_in_R
  let i := inclusion (d.R_le_S.trans (show S ≤ K ⊔ S from le_sup_right))
  let f := d.quotientMap.comp i
  have hk : f.ker = ((K ⊔ S).pCoreIn 2).subgroupOf R := by
    ext r
    change i r ∈ d.quotientMap.ker ↔ (r : G) ∈ (K ⊔ S).pCoreIn 2
    rw [d.quotientMap_ker]
    constructor
    · exact fun hr => mem_map_of_mem (K ⊔ S).subtype hr
    · rintro ⟨v,hv,he⟩
      exact (Subtype.ext he : v = i r) ▸ hv
  have hf : f.range = zpowers (Equiv.swap (0 : Fin 7) 1) := by
    rw [← d.transposition]
    ext p
    constructor
    · rintro ⟨r,rfl⟩
      exact ⟨i r,r.property,rfl⟩
    · rintro ⟨r,hr,rfl⟩
      exact ⟨⟨r,hr⟩,rfl⟩
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hf))

/-- The quotient in C.6.3(3)(b) is elementary abelian and has rank one. -/
theorem Input.quotient_elementary_rank_one (d : Input K R S Λ) :
    letI := d.core_normal_in_R
    IsElementaryAbelian 2 (R ⧸ ((K ⊔ S).pCoreIn 2).subgroupOf R) ∧
      Group.rank (R ⧸ ((K ⊔ S).pCoreIn 2).subgroupOf R) = 1 := by
  let := d.core_normal_in_R
  let E := R ⧸ ((K ⊔ S).pCoreIn 2).subgroupOf R
  let e := d.quotientEquivTransposition
  have ht : Equiv.swap (0 : Fin 7) 1 ^ 2 = 1 := by decide
  let : IsElementaryAbelian 2 (zpowers (Equiv.swap (0 : Fin 7) 1)) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one ht
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  have hc : Nat.card E = 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_zpowers]
    exact orderOf_eq_prime ht (by decide)
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  refine ⟨inferInstance, le_antisymm ?_ (Nat.succ_le_iff.mpr (Group.rank_pos E))⟩
  exact IsElementaryAbelian.rank_le_of_card_le (p := 2) E (by simp [hc])

omit [Finite G] in
/-- The original residual, restricted to H, is exactly O²(H). -/
theorem Input.block_subgroupOf_eq_residual (d : Input K R S Λ) :
    K.subgroupOf (K ⊔ S) = pResidual 2 (K ⊔ S : Subgroup G) := by
  apply map_injective (K ⊔ S).subtype_injective
  rw [map_subgroupOf_eq_of_le le_sup_left, d.residual]

/-- The original residual maps to the actual alternating subgroup. -/
theorem Input.quotientMap_block (d : Input K R S Λ) :
    (K.subgroupOf (K ⊔ S)).map d.quotientMap = alternatingGroup (Fin 7) := by
  rw [d.block_subgroupOf_eq_residual,
    map_pResidual_of_surjective 2 d.quotientMap d.quotientMap_surjective,
    Equiv.Perm.twoResidual_eq_alternating]

private theorem alternating_sup_transposition :
    alternatingGroup (Fin 7) ⊔ zpowers (Equiv.swap (0 : Fin 7) 1) = ⊤ := by
  apply top_unique
  intro p _
  by_cases hp : p ∈ alternatingGroup (Fin 7)
  · exact (show alternatingGroup (Fin 7) ≤ _ from le_sup_left) hp
  · have ht : Equiv.swap (0 : Fin 7) 1 ∉ alternatingGroup (Fin 7) := by
      simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide : (0 : Fin 7) ≠ 1)]
    have hpt : p * Equiv.swap (0 : Fin 7) 1 ∈ alternatingGroup (Fin 7) :=
      (mul_mem_iff_of_index_two alternatingGroup.index_eq_two).mpr (by simp [hp, ht])
    have h := mul_mem_sup hpt (inv_mem (mem_zpowers (Equiv.swap (0 : Fin 7) 1)))
    simpa only [mul_inv_cancel_right] using h

/-- H=KR, so the two-core in C.6.3 is the two-core in the input. -/
theorem Input.block_sup_R (d : Input K R S Λ) : K ⊔ R = K ⊔ S := by
  let H := K ⊔ S
  let A := (K ⊔ R).subgroupOf H
  have hAH : K ⊔ R ≤ H := sup_le le_sup_left (d.R_le_S.trans le_sup_right)
  have hm : A.map d.quotientMap = ⊤ := by
    rw [show A = K.subgroupOf H ⊔ R.subgroupOf H from
      subgroupOf_sup le_sup_left (d.R_le_S.trans le_sup_right), Subgroup.map_sup,
      d.quotientMap_block, show (R.subgroupOf H).map d.quotientMap = _ from d.transposition]
    exact alternating_sup_transposition
  have hk : d.quotientMap.ker ≤ A := by
    rw [d.quotientMap_ker]
    intro q hq
    exact (show R ≤ K ⊔ R from le_sup_right)
      (d.core_le (mem_map_of_mem H.subtype hq))
  have htop : A = ⊤ := by
    have hh := congrArg (comap d.quotientMap) hm
    simpa only [comap_map_eq, sup_eq_left.mpr hk, comap_top] using hh
  exact le_antisymm hAH (subgroupOf_eq_top.mp htop)

end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
