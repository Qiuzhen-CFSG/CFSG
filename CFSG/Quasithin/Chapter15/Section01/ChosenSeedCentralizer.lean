module
public import CFSG.Quasithin.Chapter15.Section01.ChosenNormalizerSource
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.Source
public import Theory.Representation.BinaryOffender.SylowFixedCentralizer
/-!
# Central-seed residuals in the chosen Chapter 15 action

Let V be a normal elementary abelian subgroup of the selected M. It lies
in the original Sylow T, so its Sylow-fixed vectors are precisely vectors
in V lying in Ω₁(Z(T)). If the literal action image has a normal odd subgroup
with two-group quotient, its Sylow-fixed pointwise stabilizer is a two-group.
Thus O²(C_M(Ω₁(Z(T)))) acts trivially on V.

The source H*(T,M) centralization theorem then gives the same conclusion for
O²(H∩M), with the residual mapped by the original ambient inclusion. The odd
normal image hypothesis remains explicit until the source endpoint supplies it.
No irreducibility, full-movement, or replacement of the chosen V is used.

Source: Aschbacher–Smith 15.1.6 and 15.1.9(4), printed pp.1087–1089.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Source 15.1.6 with an explicit normal odd subgroup in the literal chosen action image. -/
theorem chosen_seed_centralizer_residual_of_odd_normal_image
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M)
    (hMV : M ≤ normalizer (V : Set G))
    (P : Subgroup (internalActionImage M V hMV)) [P.Normal]
    (hodd : Odd (Nat.card P)) (hquot : IsPGroup 2 ((internalActionImage M V hMV) ⧸ P)) :
    (pResidual 2 (M ⊓ centralizer (centralInvolutions T : Set G) : Subgroup G)).map
      (M ⊓ centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (V : Set G) := by
  let D := internalActionImage M V hMV
  let ρ := imageRepresentation M V hMV
  let f : M →* D := (actionHom M V hMV).rangeRestrict
  have hf : Function.Surjective f := (actionHom M V hMV).rangeRestrict_surjective
  let S := (T.subtype hTM).mapSurjective hf
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMV
    let := IsElementaryAbelian.subgroupOf hVM (p := 2)
    have h := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal (T.subtype hTM)
    have hm := map_mono (f := M.subtype) h
    simpa only [map_subgroupOf_eq_of_le hVM, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTM] using hm
  have hseed (v : Additive V) (hv : v ∈ fixedSpace ρ (S : Subgroup D)) :
      (v.toMul : G) ∈ centralInvolutions T := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hVT v.toMul.property,?_,?_⟩
    · exact congrArg V.subtype (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) v.toMul)
    · intro t ht
      have htS : f ⟨t,hTM ht⟩ ∈ (S : Subgroup D) := mem_map_of_mem f ht
      have he := congrArg (fun w : Additive V => (w.toMul : G)) (hv ⟨_,htS⟩)
      change t * v.toMul * t⁻¹ = v.toMul at he
      exact mul_inv_eq_iff_eq_mul.mp he
  let K := M ⊓ centralizer (centralInvolutions T : Set G)
  let k : K →* D := f.comp (inclusion inf_le_left)
  have hk : ∀ x : K, k x ∈ (S : Subgroup D) := by
    intro x
    rw [← sylow_fixed_kernel_eq ρ (imageRepresentation_injective _ _ _) S P hodd hquot]
    refine ⟨mem_top _,?_⟩
    intro v hv
    apply Additive.toMul.injective
    apply Subtype.ext
    change (x : G) * v.toMul * (x : G)⁻¹ = v.toMul
    rw [← x.property.2 v.toMul (hseed v hv), mul_inv_cancel_right]
  let ks : K →* S := k.codRestrict S hk
  have hres : pResidual 2 K ≤ k.ker := by
    intro x hx
    have he := pResidual_le_ker_of_isPGroup 2 ks S.isPGroup' hx
    exact congrArg (fun s : S => (s : D)) he
  rintro x ⟨k,hk,rfl⟩ v hv
  have he := hres hk
  have hact : actionHom M V hMV (inclusion inf_le_left k) = 1 :=
    congrArg (fun d : D => (d : MulAut V)) he
  have hc : (inclusion inf_le_left k : M) ∈ (centralizer (V : Set G)).subgroupOf M := by
    rw [← actionHom_ker]
    exact hact
  exact hc v hv

/-- The same conclusion when the actual image two-residual has odd order. -/
theorem chosen_seed_centralizer_residual_of_odd_residual
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M)
    (hMV : M ≤ normalizer (V : Set G))
    (hodd : Odd (Nat.card (pResidual 2 (internalActionImage M V hMV)))) :
    (pResidual 2 (M ⊓ centralizer (centralInvolutions T : Set G) : Subgroup G)).map
      (M ⊓ centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (V : Set G) :=
  chosen_seed_centralizer_residual_of_odd_normal_image T hTM hVM hMV
    (pResidual 2 (internalActionImage M V hMV)) hodd (isPGroup_quotient_pResidual 2)

/-- Transport along the actual inclusion of H∩M into C_M(Ω₁(Z(T))). -/
theorem chosen_intersection_residual_of_odd_normal_image
    (T : Sylow 2 G) {M H V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M)
    (hMV : M ≤ normalizer (V : Set G))
    (P : Subgroup (internalActionImage M V hMV)) [P.Normal]
    (hodd : Odd (Nat.card P)) (hquot : IsPGroup 2 ((internalActionImage M V hMV) ⧸ P))
    (hHZ : H ≤ centralizer (centralInvolutions T : Set G)) :
    (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (V : Set G) := by
  let K := M ⊓ centralizer (centralInvolutions T : Set G)
  have hJK : H ⊓ M ≤ K := le_inf inf_le_right (inf_le_left.trans hHZ)
  have hh := map_mono (f := K.subtype) (map_pResidual_le 2 (inclusion hJK))
  rw [map_map] at hh
  exact hh.trans (chosen_seed_centralizer_residual_of_odd_normal_image T hTM hVM hMV P hodd hquot)

/-- Source 15.1.9(4): original HStar centralization discharges the seed hypothesis. -/
theorem source_15_1_9_4_of_odd_normal_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H V : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hVM : V ≤ M) (hMV : M ≤ normalizer (V : Set G))
    (P : Subgroup (internalActionImage M V hMV)) [P.Normal]
    (hodd : Odd (Nat.card P)) (hquot : IsPGroup 2 ((internalActionImage M V hMV) ⧸ P)) :
    (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (V : Set G) :=
  chosen_intersection_residual_of_odd_normal_image T hM.1.2 hVM hMV P hodd hquot
    (source_centralizing_HStar_le_seed_centralizer hG T hM hH hJ)

/-- The original HStar consumer with only oddness of the actual image residual left explicit. -/
theorem source_15_1_9_4_of_odd_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H V : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hVM : V ≤ M) (hMV : M ≤ normalizer (V : Set G))
    (hodd : Odd (Nat.card (pResidual 2 (internalActionImage M V hMV)))) :
    (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (V : Set G) :=
  source_15_1_9_4_of_odd_normal_image hG T hM hH hJ hVM hMV
    (pResidual 2 (internalActionImage M V hMV)) hodd (isPGroup_quotient_pResidual 2)

end CFSG.Quasithin.Chapter15.Section01
