module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.NaturalModel.Consequences

/-!
# The escaping-conjugate factorization before the index-two argument

C.6.2(3) supplies an actual escaping conjugate. The marked action proves
the geometric rank premise, so C.6.3(3)(i) factors R and its core with no
additional index hypothesis. This is the starting factorization for the
remaining C.6.4 dihedral argument.

Source: Aschbacher–Smith C.6.3(1),(3)(i), C.6.4, pp.166–168.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
open Stellmacher
variable {G : Type*} [Group G] [Finite G] {K R S Λ : Subgroup G}

/-- The first C.6.3 factorization requires no normalizer-index premise. -/
theorem Input.factorization_of_escape (d : Input K R S Λ)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (he : ¬ ((blockU K).map K.subtype).map (MulAut.conj x⁻¹ : G →* G) ≤
      (K ⊔ S).pCoreIn 2) :
    let U := (blockU K).map K.subtype
    let Q := (K ⊔ S).pCoreIn 2
    let V := U.map (MulAut.conj x⁻¹ : G →* G)
    R = V ⊔ Q ∧ R = U ⊔ (R ⊓ centralizer (V : Set G)) ∧
      Q = U ⊔ (Q ⊓ centralizer (V : Set G)) ∧
      R = (U ⊔ V) ⊔ (R ⊓ centralizer ((U ⊔ V : Subgroup G) : Set G)) := by
  let := d.block.2.1.elementary.map K.subtype
  let := d.core_normal_in_R
  let := d.quotient_elementary_rank_one.1
  apply c6_3_factorization_of_quotient_rank R ((blockU K).map K.subtype)
    ((K ⊔ S).pCoreIn 2) (d.module_le_core.trans d.core_le)
    ((d.R_le_S.trans le_sup_right).trans d.normalizes_module)
    d.core_eq_centralizer x hx he
  exact d.quotient_elementary_rank_one.2.trans d.centralizer_rank_minimum.symm

/-- The source obstruction produces an actual escaping conjugate and its
factorizations before any index-two conclusion has been established. -/
theorem Input.exists_escape_factorization (d : Input K R S Λ) :
    let U := (blockU K).map K.subtype
    let Q := (K ⊔ S).pCoreIn 2
    ∃ x ∈ (Λ ⊓ normalizer (R : Set G)) ⊔ S,
      ¬ U.map (MulAut.conj x⁻¹ : G →* G) ≤ Q ∧
      R = U.map (MulAut.conj x⁻¹ : G →* G) ⊔ Q ∧
      R = U ⊔ (R ⊓ centralizer (U.map (MulAut.conj x⁻¹ : G →* G) : Set G)) ∧
      Q = U ⊔ (Q ⊓ centralizer (U.map (MulAut.conj x⁻¹ : G →* G) : Set G)) ∧
      R = (U ⊔ U.map (MulAut.conj x⁻¹ : G →* G)) ⊔
        (R ⊓ centralizer ((U ⊔ U.map (MulAut.conj x⁻¹ : G →* G) : Subgroup G) : Set G)) := by
  have hres : twoResidualAmbient K = K := by
    have hr : twoResidualSubgroup K = pResidual 2 K := by
      unfold twoResidualSubgroup pResidual
      congr 1
      ext N
      constructor
      · rintro ⟨hn,n,hc⟩
        let : N.Normal := hn
        exact ⟨hn,IsPGroup.of_card hc⟩
      · rintro ⟨hn,hp⟩
        exact ⟨hn,hp.exists_card_eq⟩
    rw [twoResidualAmbient, hr, d.block.2.1.residual_eq_top,
      ← MonoidHom.range_eq_map, range_subtype]
  have hU : ⁅(pCore 2 K).map K.subtype,K⁆ ≠ ⊥ := by
    rw [source_module_eq]
    intro he
    exact d.block.2.1.blockU_ne_bot ((map_injective K.subtype_injective)
      (he.trans (map_bot K.subtype).symm))
  have hQR : (pCore 2 (K ⊔ R : Subgroup G)).map (K ⊔ R).subtype ≤ R := by
    rw [d.block_sup_R]
    exact d.core_le
  have hno (W : Subgroup G) (hne : W ≠ ⊥) (hWR : W ≤ R)
      (hn : (W.subgroupOf (K ⊔ S)).Normal) :
      ¬ Λ ⊓ normalizer (R : Set G) ≤ Λ ⊓ normalizer (W : Set G) :=
    d.no_normal_subgroup hne hWR
      ((normal_subgroupOf_iff_le_normalizer
        (hWR.trans (d.R_le_S.trans le_sup_right))).mp hn)
  obtain ⟨x,hx,he⟩ := c6_3_exists_escaping_conjugate_local K R S Λ
    ((d.R_le_S.trans le_sup_right).trans d.normalizes_block) hres hQR hU d.R_le_S
    (normal_subgroupOf_of_le_normalizer d.S_normalizes_R) hno
  have hcore : (pCore 2 (K ⊔ R : Subgroup G)).map (K ⊔ R).subtype =
      (K ⊔ S).pCoreIn 2 := congrArg (pCoreIn 2) d.block_sup_R
  have he' : ¬ ((blockU K).map K.subtype).map (MulAut.conj x⁻¹ : G →* G) ≤
      (K ⊔ S).pCoreIn 2 := by
    simpa only [source_module_eq, hcore] using he
  exact ⟨x,hx,he',d.factorization_of_escape x ((sup_le inf_le_right d.S_normalizes_R) hx) he'⟩

end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
