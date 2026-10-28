module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.Setup
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.Action

/-!
# Fixed codimension and the non-FF step in the parity argument

The subgroup displacement in the source contracts is the fixed codimension
of the actual U/V₁ representation. If every involution of H/O₂(H) moves at
least nine dimensions and that quotient has two-rank at most four, every
nontrivial elementary quotient actor has a larger fixed codimension than
rank. Pulling back an arbitrary offender therefore excludes FF-modules.
No elementary-abelian condition is imposed on its preimage in H.

For the specialized 5.1.17 configuration the two critical-pair centralizer
indices are at most sixteen. The original quotient markings and their
representation-theoretic lower bound remain independent source obligations.
Source: Aschbacher–Smith, 5.1.17, printed pp.641–642 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {E : ChapterF.Section08.Setup G} (h : E.Hypothesis)

include h in
open Representation.BinaryOffender in
theorem displacement_eq_fixedCodim
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E.HStar W)
    (c : Representation.BinaryConjugationSection E.H E.U E.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 E.H))))
    (y : G) (hy : y ∈ E.H) :
    displacement E y = fixedCodim ρ
      (((zpowers y).subgroupOf E.H).map (QuotientGroup.mk' (pCore 2 E.H))) := by
  rw [displacement, fixed_index h ρ c (zpowers y) (zpowers_le.mpr hy),
    Nat.log_pow (by decide : 1 < 2)]

include h in
theorem fixed_index_gt_actor_index
    (hrank : primeRank 2 E.HStar ≤ 4) (hlarge : LargeDisplacement E)
    (A : Subgroup G) (hA : A ≤ E.H)
    (hElem : IsElementaryAbelian 2
      ((A.subgroupOf E.H).map (QuotientGroup.mk' (pCore 2 E.H))))
    (hnot : ¬ A ≤ E.QH) :
    Nat.log 2 (E.QH.relIndex A) <
      Nat.log 2 ((commutatorPreimage E.U A E.V₁).relIndex E.U) := by
  let q := QuotientGroup.mk' (pCore 2 E.H)
  let B := (A.subgroupOf E.H).map q
  let : IsElementaryAbelian 2 B := hElem
  have hcard : E.QH.relIndex A ≤ 2 ^ 4 := by
    rw [← quotient_image_card A hA]
    exact (primeRank_le_iff_elementary_card_le E.HStar).mp hrank B hElem
  have hsmall : Nat.log 2 (E.QH.relIndex A) ≤ 4 := by
    have hh := Nat.log_mono_right (b := 2) hcard
    simpa only [Nat.log_pow (by decide : 1 < 2)] using hh
  obtain ⟨y, hy, hyQ⟩ := SetLike.not_le_iff_exists.mp hnot
  let yH : E.H := ⟨y, hA hy⟩
  have hyB : q yH ∈ B := mem_map_of_mem q hy
  have hy2 : y ^ 2 ∈ E.QH := by
    have hp : (q yH) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (q yH) hyB
    rw [← map_pow] at hp
    exact mem_map_of_mem E.H.subtype ((QuotientGroup.eq_one_iff _).mp hp)
  have hlow := hlarge y (hA hy) hy2 hyQ
  have hfix : commutatorPreimage E.U A E.V₁ ≤
      commutatorPreimage E.U (zpowers y) E.V₁ :=
    le_commutatorPreimage (commutatorPreimage_le _ _ _)
      ((commutator_mono le_rfl (zpowers_le.mpr hy)).trans
        (commutator_commutatorPreimage_le _ _ _ (h.g2.U_le_H.trans h.H_le)))
  have hindex := relIndex_le_of_le_left hfix
    ((commutatorPreimage E.U A E.V₁).subgroupOf E.U).index_ne_zero_of_finite
  have hlog := Nat.log_mono_right (b := 2) hindex
  change 9 ≤ Nat.log 2 ((commutatorPreimage E.U (zpowers y) E.V₁).relIndex E.U) at hlow
  omega

include h in
open Representation.BinaryOffender in
theorem not_ff_of_large_displacement
    (hrank : primeRank 2 E.HStar ≤ 4) (hlarge : LargeDisplacement E)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E.HStar W)
    (c : Representation.BinaryConjugationSection E.H E.U E.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 E.H)))) : ¬ IsFFModule ρ := by
  rintro ⟨B, hB, hcod⟩
  let q := QuotientGroup.mk' (pCore 2 E.H)
  let A := (B.comap q).map E.H.subtype
  have hAH : A ≤ E.H := map_subtype_le _
  have himage : (A.subgroupOf E.H).map q = B := by
    rw [show A.subgroupOf E.H = B.comap q from
      comap_map_eq_self_of_injective E.H.subtype_injective _,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hnot : ¬ A ≤ E.QH := by
    intro ha
    apply hB.1
    rw [← himage]
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    intro a haA
    have hh := ha haA
    obtain ⟨b, hb, he⟩ := hh
    exact (Subtype.ext he : b = a) ▸ hb
  have hElem : IsElementaryAbelian 2 ((A.subgroupOf E.H).map q) := himage.symm ▸ hB.2
  have hi := fixed_index_gt_actor_index h hrank hlarge A hAH hElem hnot
  rw [← quotient_image_card A hAH, himage, fixed_index h ρ c A hAH,
    himage, Nat.log_pow (by decide : 1 < 2)] at hi
  exact (not_lt_of_ge hcod) hi

variable {T : Sylow 2 G} {L H A : Subgroup G} {n : ℕ}

theorem Seed.critical_indices_le_sixteen (s : Seed T L H A n) (C : s.f8.CriticalPath) :
    C.Dg.relIndex C.Ug ≤ 16 ∧ C.DH.relIndex (setup T L s.V H A).U ≤ 16 := by
  have hp : 2 ^ primeRank 2 (setup T L s.V H A).HStar ≤ 16 :=
    (pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) s.quotient_rank)
  exact ⟨(Dg_index_le C).trans hp, (DH_index_le C).trans hp⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
