module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.Maximum
public import Theory.GroupTheory.ElementaryThompsonFrattini
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The literal internal-module action and Thompson image

The actor is exactly H/C_H(W). Its faithful binary representation is induced
by the original conjugation on W. Maximum elementary subgroups map to best
offenders, so the actual Thompson image lies in the full normal offender
subgroup. Restriction gives all B.5.3 hypotheses: faithfulness, trivial
two-core, offender generation, and an SQTK cover obtained by inverse image
in H. No equality of that actor with a Thompson image is assumed.

The final Frattini lemma derives the normalizer factorization from Thompson
centralization, using a Sylow of the normal centralizer and Thompson heredity.
The best-offender inclusion reuses the intrinsic B.2.5 proof in the imported
`BestReduction.Maximum` module; it uses no later Chapter 15 theorem.

Source: Aschbacher–Smith, B.2.5–7, printed pp.76–77, and B.5.3, p.104.
-/

@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.NonquasisimpleFactorization
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives
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
  apply CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.thompson_image_le_internal_offenderSubgroup
  exact (IsElementaryAbelian.isPGroup 2 W).le_sylow_of_normal P

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
    FFHypothesis 𝒦 (ρ.comp (offenderSubgroup ρ).subtype) := by
  let J := offenderSubgroup ρ
  let : J.Normal := offenderSubgroup_normal ρ
  have hgen : offenderSubgroup (ρ.comp J.subtype) = ⊤ := by
    apply map_injective J.subtype_injective
    apply le_antisymm (by simp)
    rw [← MonoidHom.range_eq_map, range_subtype]
    change offenderSubgroup ρ ≤ _
    unfold offenderSubgroup generatedBy
    refine iSup_le fun B => iSup_le fun hB => ?_
    have hBJ : B ≤ J := le_iSup_of_le B (le_iSup_of_le hB le_rfl)
    rw [← map_subgroupOf_eq_of_le hBJ]
    apply map_mono
    exact le_iSup_of_le (B.subgroupOf J)
      (le_iSup_of_le ⟨hB.1.subgroupOf ρ hBJ, le_top⟩ le_rfl)
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

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.NonquasisimpleFactorization
