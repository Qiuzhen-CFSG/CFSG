module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.Intermediate
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.EarlierWeakClosure.Source
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Applying the earlier weak-closure theorem in the solvable endgame

An actual S₃ isomorphism for JR₁/O₂(DR₁) identifies the old core with
O₂(JR₁). Thus the already proved centralizer equality gives reducedness of
E inside JR₁ and every local hypothesis of 14.7.31(2). The original natural
action supplies U ≤ O₂(K), so the returning-point condition has no remaining
containment premise. Both clauses of the universal 14.7.31 then apply to
the same W₀(R₁,V), yielding the contradiction via O²(J).

This is a conditional assembly, not the finished solvable branch: the
three-rank estimate and B.2.16 must still construct the displayed quotient
isomorphism. They remain obligations of this task and its prerequisites.
The source producers qt-14-07-solvable and qt-14-07-components supply the
earlier module-separation and universal weak-closure implications; the
qt-12-02 producer supplies Structural1222.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.67(4), printed pp.1070–1071, and 14.7.31, printed p.1055.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Theory.GroupTheory ResidualNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Data
variable (d : Data T L V F W)

omit d [AddCommGroup W] [Module (ZMod 2) W] in
/-- The S₃ quotient determines the new intrinsic core, without presupposing
an equality between cores of nested groups. -/
theorem residual_thompsonJoin_core_of_quotient
    (e : JRQuotient L F ≃* Equiv.Perm (Fin 3)) :
    coreInJR L F = pCore 2 (JR L F) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (coreInJR L F))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = coreInJR L F := by
    ext x
    change e (QuotientGroup.mk' (coreInJR L F) x) = 1 ↔ x ∈ coreInJR L F
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  exact hk.symm.trans (ker_eq_twoCore_of_surjective_perm_three f hf
    (hk.symm ▸ (isPGroup_pCoreIn 2 (Y L F)).comap_subtype))

include d

/-- With the actual quotient established, the old centralizer is the new core. -/
theorem residual_thompsonJoin_centralizer_eq_core_of_quotient
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (e : JRQuotient L F ≃* Equiv.Perm (Fin 3)) :
    JR L F ⊓ centralizer (E F : Set G) = (JR L F).pCoreIn 2 := by
  rw [d.residual_thompsonJoin_centralizer hSylow]
  have h := congrArg (map (JR L F).subtype) (residual_thompsonJoin_core_of_quotient e)
  rw [coreInJR, map_subgroupOf_eq_of_le
    (show (Y L F).pCoreIn 2 ≤ JR L F from (residual_Y_core_le_R hSylow).trans le_sup_right)] at h
  exact h

/-- Reducedness uses the literal centralizer quotient, now equal to A/O₂(A). -/
theorem residual_thompsonJoin_reduced_of_quotient
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (e : JRQuotient L F ≃* Equiv.Perm (Fin 3)) :
    IsPReduced 2 ((E F).subgroupOf (JR L F)) := by
  obtain ⟨he, hn⟩ := d.residual_thompsonJoin_elementary_normal hSylow
  let := hn
  have hc : centralizer ((E F).subgroupOf (JR L F) : Set (JR L F)) =
      pCore 2 (JR L F) := by
    apply map_injective (JR L F).subtype_injective
    have hc' : (centralizer ((E F).subgroupOf (JR L F) : Set (JR L F))).map
        (JR L F).subtype = JR L F ⊓ centralizer (E F : Set G) := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨a.property, ?_⟩
        intro b hb
        exact congrArg Subtype.val (ha
          ⟨b, (le_sup_right : F.Ri L 1 ≤ JR L F) (d.residualSpan_le_R hSylow hb)⟩ hb)
      · rintro ⟨hx, hc⟩
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        intro b hb
        exact Subtype.ext (hc b hb)
    exact hc'.trans (d.residual_thompsonJoin_centralizer_eq_core_of_quotient hSylow e)
  refine ⟨hn, he, ?_⟩
  let q := QuotientGroup.quotientMulEquivOfEq hc
  apply (map_eq_bot_iff_of_injective (f := q.toMonoidHom) _ q.injective).mp
  rw [pCore_map_iso 2 q]
  exact pCore_quotient_pCore_eq_bot 2

/-- Actual application of both clauses of 14.7.31 to W₀(R₁,V). The outstanding
S₃ identification is explicit; the theorem does not certify B.2.16. -/
theorem false_of_residual_thompson_quotient
    (earlier : d.ModuleSeparation)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (weakClosure : Theorem14731.{u})
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F))
    (e : JRQuotient L F ≃* Equiv.Perm (Fin 3)) : False := by
  have hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G) :=
    (d.plane_centralizer_le earlier).trans (d.natural.sylow_normalizes structural)
  obtain ⟨hfirst, hsecond⟩ := weakClosure G T L V d.counterexample d.natural F d.abelian hplane
  have hc := d.residual_thompsonJoin_centralizer_eq_core_of_quotient hSylow e
  have hmodel : Nonempty (((JR L F) ⧸ pCore 2 (JR L F)) ≃* Equiv.Perm (Fin 3)) := by
    exact ⟨(QuotientGroup.quotientMulEquivOfEq
      (residual_thompsonJoin_core_of_quotient e).symm).trans e⟩
  have hnormal := hsecond (JR L F) (F.Ri L 1) (E F)
    (d.residual_thompsonJoin_characteristicTwo hSylow)
    (residual_thompsonJoin_sylow hSylow)
    ((d.residualSpan_le_R hSylow).trans le_sup_right)
    (d.residual_thompsonJoin_reduced_of_quotient hSylow e) hmodel hc
    (fun g hg => (d.returning_point_U_le_thompsonJoin_core hSylow g hg).trans hc.symm.le)
  exact d.false_of_thompsonJoin_normalizer_bound hDM hSylow hBaum hD
    (ChapterE.indexedWeakClosure V (F.Ri L 1) 0) hnormal.2 hfirst.2.2

/-- Both weak-closure clauses are now supplied by their original source proof,
for the same JR₁ quotient and returning-point maps as above. -/
theorem false_of_residual_thompson_quotient_source14731
    (earlier : d.ModuleSeparation)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F))
    (e : JRQuotient L F ≃* Equiv.Perm (Fin 3)) : False :=
  d.false_of_residual_thompson_quotient earlier structural (source_theorem14731 structural)
    hDM hSylow hBaum hD e

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
