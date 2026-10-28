module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.OddImage

/-!
# Reducedness of the original Chapter 15 module

The intrinsic form of V(M)=⟨Ω₁(Z(T))ᴹ⟩ is elementary by characteristic two.
To show that M/C_M(V(M)) has trivial two-core, lift that core to M.
Its elements agree modulo the centralizer with elements of the original
Sylow subgroup, hence centralize Ω₁(Z(T)). Normality then forces the
whole lifted core to centralize its M-conjugate span V(M).

The final theorem uses the existing Section 15.3 localActionKernel and
localActionMap, with equality of the actual centralizer denominators.
No reducedness or quotient-core assumption is added to the source input.
Source: Aschbacher–Smith B.2.13–14 and the standing Chapter 14/15 module
convention, printed pp.78–79, 974 and 1083.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual conjugate-span module belongs to the source family R₂(M). -/
theorem localModule_reduced_from_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : M ∈ Chapter1.HOver G (T : Set G)) :
    IsPReduced 2 ((localModule T M).subgroupOf M) := by
  have hTM : (T : Subgroup G) ≤ M := hM.2
  have hVM : localModule T M ≤ M := conjugateSpanBy_le_self
    (fun z hz => hTM ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1)
  let U := (localModule T M).subgroupOf M
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy (centralInvolutions T) M)
  let : IsElementaryAbelian 2 (localModule T M) := localModule_elementary_from_source hG T hM
  refine ⟨inferInstance, IsElementaryAbelian.subgroupOf hVM, ?_⟩
  let C := centralizer (U : Set M)
  let q := QuotientGroup.mk' C
  let Q := (pCore 2 (M ⧸ C)).comap q
  let S := T.subtype hTM
  have hQS : pCore 2 (M ⧸ C) ≤ (S : Subgroup M).map q :=
    pCore_isPGroup.le_sylow_of_normal (S.mapSurjective (QuotientGroup.mk'_surjective C))
  have hQZ : Q.map M.subtype ≤ centralizer (centralInvolutions T : Set G) := by
    rintro x ⟨a, ha, rfl⟩ z hz
    obtain ⟨s, hs, hsa⟩ := hQS ha
    have hasC : a / s ∈ C := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (a / s) = 1
      rw [map_div, hsa, div_self']
    have hzM : z ∈ M := hTM ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1
    have hzc : (⟨z,hzM⟩ : M) ∈ U := le_conjugateSpanBy _ _ hz
    have hsZ : (s : G) * z = z * s := ((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 s hs
    have he : (a / s : M) * s = a := div_mul_cancel _ _
    have hd : (a / s : M) ∈ centralizer ({(⟨z,hzM⟩ : M)} : Set M) :=
      mem_centralizer_singleton_iff.mpr (hasC ⟨z,hzM⟩ hzc).symm
    have hsC : s ∈ centralizer ({(⟨z,hzM⟩ : M)} : Set M) :=
      mem_centralizer_singleton_iff.mpr (Subtype.ext hsZ)
    have hh := (centralizer ({(⟨z,hzM⟩ : M)} : Set M)).mul_mem hd hsC
    rw [he] at hh
    exact congrArg M.subtype (mem_centralizer_singleton_iff.mp hh).symm
  have hMQ : M ≤ normalizer (Q.map M.subtype : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      Q.le_normalizer_map M.subtype
  have hQV := le_centralizer_conjugateSpanBy_of_normalizes _ _ _ hMQ hQZ
  apply bot_unique
  intro x hx
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective C x
  apply (QuotientGroup.eq_one_iff a).mpr
  intro v hv
  exact Subtype.ext (hQV (mem_map_of_mem M.subtype hx) v hv)

omit [Finite G] in
/-- Identify the original action kernel with the intrinsic module centralizer. -/
theorem localActionKernel_eq_centralizer (T : Sylow 2 G) {M : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) :
    localActionKernel (centralInvolutions T) M =
      centralizer ((localModule T M).subgroupOf M : Set M) := by
  have hVM : localModule T M ≤ M := conjugateSpanBy_le_self
    (fun z hz => hTM ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1)
  ext m
  constructor
  · intro hm v hv
    exact Subtype.ext (hm v hv)
  · intro hm v hv
    exact congrArg M.subtype (hm ⟨v,hVM hv⟩ hv)

/-- The existing Section 15.3 quotient has trivial two-core. -/
theorem localActionQuotient_twoReduced_from_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : M ∈ Chapter1.HOver G (T : Set G)) :
    pCore 2 (LocalActionQuotient (centralInvolutions T) M) = ⊥ := by
  have hU := localModule_reduced_from_source hG T hM
  let := hU.normal
  let e := QuotientGroup.quotientMulEquivOfEq (localActionKernel_eq_centralizer T hM.2).symm
  rw [← pCore_map_iso 2 e, hU.quotient_pCore_eq_bot, Subgroup.map_bot]


end CFSG.Quasithin.Chapter15.Section03.InitialSource
