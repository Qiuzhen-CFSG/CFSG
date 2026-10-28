module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CoreSections

/-!
# The two literal factors of the original core section

The selected degree-one geometry identifies B = V ∩ O₂(I) and its actual
conjugate A as generators of O₂(I), intersecting exactly in U. Their
images in the literal O₂(I)/U are complementary and have the same rank
as the original actor. No abstract replacement of the quotient is used.
Source: Aschbacher--Smith E.2.10(2), E.2.13 and 8.2.8(4--5),
printed pp.222--225,718--719, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE HermitianSource Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
  {H M I : Subgroup G} {i : I} {S : Sylow 2 I}

/-- The actual elementary factors generate the core, intersect in U, and
are conjugate by the selected inverse conjugator. -/
theorem selected_core_factor_geometry (s : Selected H T M V I 1 i S)
    (U : Subgroup G) (hU : U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) :
    let P := I.pCoreIn 2
    let B := V ⊓ P
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ P
    B ⊔ A = P ∧ B ⊓ A = U ∧
      B.map (MulAut.conj i.val⁻¹).toMonoidHom = A ∧
      U.map (MulAut.conj i.val⁻¹).toMonoidHom = U := by
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hBi : (TwoConjugate.B (V.subgroupOf I) (M.subgroupOf I)).map I.subtype =
      V ⊓ I.pCoreIn 2 := by
    rw [s.twoConjugate.B_eq_twoCore_inf,map_inf _ _ _ I.subtype_injective,
      map_subgroupOf_eq_of_le hVI,inf_comm]
    rfl
  have hAi := selected_actor_image I M V hVI S i s.twoConjugate
  change (TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹).map I.subtype =
    V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 at hAi
  have hZi := (selected_intersection_image I V hVI i).trans hU.symm
  have hc : I.subtype.comp (MulAut.conj i⁻¹).toMonoidHom =
      (MulAut.conj i.val⁻¹).toMonoidHom.comp I.subtype := by
    ext x
    rfl
  refine ⟨(selected_one_core_product s).symm,?_,?_,?_⟩
  · rw [←hBi,←hAi,←map_inf _ _ _ I.subtype_injective,
      s.twoConjugate.B_inf_A_eq_Z,hZi]
  · rw [←hBi,←hAi,map_map,←hc,←map_map]
  · let := s.twoConjugate.Z_normal
    have hz := mem_normalizer_iff_map_conj_eq.mp
      (show i⁻¹ ∈ normalizer (TwoConjugate.Z (V.subgroupOf I) i⁻¹ : Set I) from
        le_normalizer_of_normal (mem_top _))
    change (TwoConjugate.Z (V.subgroupOf I) i⁻¹).map
      (MulAut.conj i⁻¹).toMonoidHom = TwoConjugate.Z (V.subgroupOf I) i⁻¹ at hz
    rw [←hZi,map_map,←hc,←map_map,hz]

/-- The original images in O₂(I)/U are complementary rank-r factors.
The two quotient maps retain their full common denominator. -/
theorem selected_core_quotient_factors (s : Selected H T M V I 1 i S)
    (U : Subgroup G) (hU : U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    [(U.subgroupOf (I.pCoreIn 2)).Normal] (r : ℕ)
    (hr : rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2)) = r) :
    let P := I.pCoreIn 2
    let B := V ⊓ P
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ P
    let q := QuotientGroup.mk' (U.subgroupOf P)
    (B.subgroupOf P).map q ⊔ (A.subgroupOf P).map q = ⊤ ∧
      (B.subgroupOf P).map q ⊓ (A.subgroupOf P).map q = ⊥ ∧
      rank ((B.subgroupOf P).map q) = r ∧
      rank ((A.subgroupOf P).map q) = r := by
  let P := I.pCoreIn 2
  let B := V ⊓ P
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ P
  let q := QuotientGroup.mk' (U.subgroupOf P)
  obtain ⟨hjoin,hmeet,hBA,hUU⟩ := selected_core_factor_geometry s U hU
  have hUB : U ≤ B := hmeet ▸ inf_le_left
  have hUA : U ≤ A := hmeet ▸ inf_le_right
  have hjoinP : B.subgroupOf P ⊔ A.subgroupOf P = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le inf_le_right,
      map_subgroupOf_eq_of_le inf_le_right,hjoin]
    ext x
    constructor
    · intro hx
      exact ⟨⟨x,hx⟩,mem_top _,rfl⟩
    · rintro ⟨y,_,rfl⟩
      exact y.property
  have hmeetP : B.subgroupOf P ⊓ A.subgroupOf P = U.subgroupOf P := by
    exact congrArg (fun K : Subgroup G => K.subgroupOf P) hmeet
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hcoreM : P ≤ M := by
    rintro _ ⟨x,hx,rfl⟩
    apply (M.subgroupOf I).normalCore_le
    change x ∈ localCore M I
    rwa [s.core_eq]
  have hAN : A ≤ normalizer (V : Set G) := inf_le_right.trans
    ((le_inf hcoreM (pCoreIn_le 2 I)).trans (s.normalizer_eq ▸ inf_le_right))
  have hker : A ⊓ centralizer (V : Set G) = U :=
    (selected_actor_kernel I M V hVI S i s.twoConjugate).trans hU.symm
  have hAindex : Nat.log 2 (U.relIndex A) = r := by
    have hh := rank_inducedAutomizer V A hAN
    rw [hker] at hh
    exact hh.symm.trans hr
  have hBindex : U.relIndex B = U.relIndex A := by
    have hh := relIndex_map_map_of_injective (f := (MulAut.conj i.val⁻¹).toMonoidHom)
      U B (MulAut.conj i.val⁻¹).injective
    rw [hUU,hBA] at hh
    exact hh.symm
  refine ⟨?_,?_,?_,?_⟩
  · rw [←Subgroup.map_sup,hjoinP,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  · apply comap_injective (QuotientGroup.mk'_surjective (U.subgroupOf P))
    rw [comap_inf,comap_map_eq,comap_map_eq,QuotientGroup.ker_mk',
      sup_eq_left.mpr (show U.subgroupOf P ≤ B.subgroupOf P from fun _ hx => hUB hx),
      sup_eq_left.mpr (show U.subgroupOf P ≤ A.subgroupOf P from fun _ hx => hUA hx),
      hmeetP,MonoidHom.comap_bot,QuotientGroup.ker_mk']
  · rw [rank,←relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf inf_le_right,hBindex]
    exact hAindex
  · rw [rank,←relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf inf_le_right]
    exact hAindex

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
