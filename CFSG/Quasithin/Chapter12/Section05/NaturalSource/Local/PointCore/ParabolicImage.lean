module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Parabolic
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.Failure

/-!
# The original point normalizer in the point-core quotient

Restriction of G₁ → G₁/O₂(G₁) to each embedded subgroup has two-group
kernel. The induced core-quotient isomorphism retains both original
diagonal blocks of M₁/O₂(M₁), including its formula on representatives.
Failure of V ≤ O₂(G₁) produces an actual normal elementary eight-group
inside M₁*, ready for the local parabolic exclusions.

Source: Aschbacher--Smith, 12.5.8(1), printed p.820. The construction of
the larger-component embeddings remains with qt-d-1251-local; final
exterior assembly belongs to qt-d-1251-source.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

noncomputable def pointCoreImageHom (A : Subgroup G) (hA : A ≤ s.marking.Gi 1) :
    A →* s.pointCoreImage A :=
  ((QuotientGroup.mk' (pCore 2 (s.marking.Gi 1))).subgroupMap
    (A.subgroupOf (s.marking.Gi 1))).comp
      (subgroupOfEquivOfLe hA).symm.toMonoidHom

omit [Finite G] in
theorem pointCoreImageHom_surjective (A : Subgroup G) (hA : A ≤ s.marking.Gi 1) :
    Function.Surjective (s.pointCoreImageHom A hA) :=
  ((QuotientGroup.mk' (pCore 2 (s.marking.Gi 1))).subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hA).symm.surjective

omit [Finite G] in
theorem pointCoreImageHom_ker_isPGroup (A : Subgroup G) (hA : A ≤ s.marking.Gi 1) :
    IsPGroup 2 (s.pointCoreImageHom A hA).ker := by
  have he : (s.pointCoreImageHom A hA).ker =
      (pCore 2 (s.marking.Gi 1)).comap (inclusion hA) := by
    ext a
    change s.pointCoreImageHom A hA a = 1 ↔ _
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  rw [he]
  exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hA)

/-- The point-normalizer quotient in the source star group keeps both actual factors. -/
noncomputable def pointCoreImage_M₁CoreEquiv :
    (s.pointCoreImage (s.marking.Mi 1) ⧸ pCore 2 (s.pointCoreImage (s.marking.Mi 1))) ≃*
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  ((s.pointCoreImageHom (s.marking.Mi 1) inf_le_right).pCoreQuotientEquiv
    (s.pointCoreImageHom_surjective _ inf_le_right)
    (s.pointCoreImageHom_ker_isPGroup _ inf_le_right)).symm.trans s.M₁CoreEquiv


omit [Finite G] in
theorem pointCoreImageHom_apply (A : Subgroup G) (hA : A ≤ s.marking.Gi 1) (a : A) :
    (s.pointCoreImageHom A hA a : s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1)) =
      QuotientGroup.mk' _ (inclusion hA a) := by rfl

theorem pointCoreImage_M₁CoreEquiv_mk (m : s.marking.Mi 1) :
    s.pointCoreImage_M₁CoreEquiv
      (QuotientGroup.mk' _ (s.pointCoreImageHom _ inf_le_right m)) =
        Representation.SL5ExteriorSquare.parabolicLeviHom 2 (by decide)
          (s.localJoinActor 1 (Or.inl rfl) m) := by
  let f := s.pointCoreImageHom (s.marking.Mi 1) inf_le_right
  let e := f.pCoreQuotientEquiv (s.pointCoreImageHom_surjective _ inf_le_right)
    (s.pointCoreImageHom_ker_isPGroup _ inf_le_right)
  change s.M₁CoreEquiv (e.symm (e (QuotientGroup.mk' _ m))) = _
  rw [MulEquiv.symm_apply_apply]
  exact s.M₁CoreEquiv_mk m

omit [Finite G] in
theorem seed_le_M₁ : V ≤ s.marking.Mi 1 :=
  D.le_sylow.trans (le_inf le_sup_right s.sylow_le_G₁)

omit [Finite G] in
theorem pointCoreImage_seed_normal :
    ((s.pointCoreImage V).subgroupOf (s.pointCoreImage (s.marking.Mi 1))).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer (s.pointCoreImage_mono s.seed_le_M₁)).mpr
  exact s.pointCoreImage_M₁_normalizes_seed

/-- A failure supplies an actual normal eight-group in the point-normalizer image. -/
theorem pointCoreImage_seed_normal_eight
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hf : ¬ V ≤ (s.marking.Gi 1).pCoreIn 2) :
    let B := (s.pointCoreImage V).subgroupOf (s.pointCoreImage (s.marking.Mi 1))
    B.Normal ∧ IsElementaryAbelian 2 B ∧ Nat.card B = 8 := by
  let B := (s.pointCoreImage V).subgroupOf (s.pointCoreImage (s.marking.Mi 1))
  have hv := s.pointCoreImage_mono s.seed_le_M₁
  let := s.pointCoreImage_seed_elementary
  refine ⟨s.pointCoreImage_seed_normal, IsElementaryAbelian.subgroupOf hv, ?_⟩
  rw [Nat.card_congr (subgroupOfEquivOfLe hv).toEquiv]
  exact s.pointCoreImage_seed_card h hf

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
