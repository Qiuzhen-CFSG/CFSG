module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import Theory.Representation.NormalElementaryQuotient.BestOffender
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.GroupTheory.ElementaryThompsonFrattini
public import Theory.GroupTheory.PResidual.NormalSubgroup
/-!
# The internal reduced action used in Thompson factorization

The literal quotient H/C_H(W) acts faithfully on W. Maximum elementary
subgroups of a Sylow two-subgroup map to best offenders, and their join
lies in the full offender subgroup. That subgroup has a genuine SQTK cover
obtained by inverse image in H. Thompson centralization gives Frattini
factorization. These intrinsic B.2 facts are extracted from the earlier
Chapter13 consumer so Chapter10 can apply them without a later chapter.
Source: Aschbacher–Smith B.2.5–7, printed pp.76–77, and B.5.3, p.104.
-/
@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.ChapterB.InternalThompsonAction
universe u v
variable {H : Type u} [Group H]
/-- The actual quotient by the centralizer of the internal module. -/
abbrev ActionQuotient (W : Subgroup H) [W.Normal] := H ⧸ centralizer (W : Set H)

/-- The original centralizer quotient map. -/
abbrev actionMk (W : Subgroup H) [W.Normal] : H →* ActionQuotient W :=
  QuotientGroup.mk' (centralizer (W : Set H))

/-- The faithful binary representation induced by conjugation on W. -/
def action (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W] :
    Representation (ZMod 2) (ActionQuotient W) (Additive W) :=
  NormalElementaryQuotient.representation W (actionMk W)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

/-- The representation uses the literal ambient conjugation convention. -/
theorem action_apply (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (h : H) (w : Additive W) :
    (((action W (actionMk W h) w).toMul : W) : H) =
      h * (w.toMul : H) * h⁻¹ :=
  NormalElementaryQuotient.representation_apply W (actionMk W)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) h w

theorem action_faithful (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W] :
    Function.Injective (action W) :=
  NormalElementaryQuotient.representation_injective W (actionMk W)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

/-- B.2.5 gives containment in the full offender actor, without identifying
that actor with either Thompson image. -/
theorem thompson_image_le [Finite H] (P : Sylow 2 H)
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W] :
    (elementaryAbelianMaxJ (P : Subgroup H)).map (actionMk W) ≤ offenderSubgroup (action W) := by
  rw [map_le_iff_le_comap]
  apply sSup_le
  intro A hA
  apply map_le_iff_le_comap.mp
  by_cases hne : A.map (actionMk W) = ⊥
  · rw [hne]
    exact bot_le
  · exact (NormalElementaryQuotient.maxElementary_isBestOffender W
      (actionMk W) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      (P : Subgroup H) A ((IsElementaryAbelian.isPGroup 2 W).le_sylow_of_normal P)
      hA hne).le_offenderSubgroup (action W)

/-- The Frattini argument of B.2.7, for the maximum-elementary Thompson subgroup. -/
theorem thompson_frattini [Finite H] (P : Sylow 2 H) (W : Subgroup H) [W.Normal]
    (hc : elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H)) :
    normalizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H) ⊔ centralizer (W : Set H) = ⊤ := by
  let C := centralizer (W : Set H)
  obtain ⟨R, hR⟩ := P.exists_subgroupOf_eq_of_normal C
  have he : (R : Subgroup C).map C.subtype = (P : Subgroup H) ⊓ C := by
    rw [hR, subgroupOf_map_subtype]
  have hj : elementaryAbelianMaxJ ((P : Subgroup H) ⊓ C) =
      elementaryAbelianMaxJ (P : Subgroup H) :=
    elementaryAbelianMaxJ_eq_of_intermediate _ _
      (le_inf (sSup_le fun _ hA => hA.1) hc) inf_le_left
  have hn : normalizer ((R : Subgroup C).map C.subtype : Set H) ≤
      normalizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
    rw [he] at hg
    change (elementaryAbelianMaxJ (P : Subgroup H)).map (MulAut.conj g).toMonoidHom = _
    change ((P : Subgroup H) ⊓ C).map (MulAut.conj g).toMonoidHom = _ at hg
    rw [← hj, ← elementaryAbelianMaxJ_map_equiv, hg]
  exact top_unique (R.normalizer_sup_eq_top.symm.le.trans (sup_le_sup_right hn C))

variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (ρ : Representation (ZMod 2) D V)

/-- All B.5.3 hypotheses for the full offender subgroup follow from its
normality and the inverse image in the supplied genuine SQTK cover. -/
theorem offender_hypothesis [Finite H] {𝒦 : GroupClass.{u}}
    (f : H →* D) (hf : Function.Surjective f) (hH : IsSQTK 𝒦 H)
    (hfaith : Function.Injective ρ) (hcore : pCore 2 D = ⊥) :
    SourceInduction.FFHypothesis 𝒦 (ρ.comp (offenderSubgroup ρ).subtype) := by
  let J := offenderSubgroup ρ
  let : J.Normal := offenderSubgroup_normal ρ
  have hgen := offenderSubgroup_restrict_eq_top ρ
  have htwo : pCore 2 J = ⊥ := by
    have hn : ((pCore 2 J).map J.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    have hl : (pCore 2 J).map J.subtype ≤ pCore 2 D := le_sSup ⟨hn, pCore_isPGroup.map _⟩
    rw [hcore] at hl
    exact ((pCore 2 J).map_eq_bot_iff_of_injective J.subtype_injective).mp (le_bot_iff.mp hl)
  refine ⟨inferInstance, hfaith.comp J.subtype_injective, htwo, hgen, ?_⟩
  exact ⟨{ Cover := J.comap f
           kernel := (f.subgroupComap J).ker
           sqtk := hH.subgroup _
           equiv := QuotientGroup.quotientKerEquivOfSurjective _
             (f.subgroupComap_surjective_of_surjective _ hf) }⟩

end CFSG.Quasithin.ChapterB.InternalThompsonAction
