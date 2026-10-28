module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.Intermediate
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.Recognition.OmegaClosure
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.Recognition.Factors

/-!
# Intrinsic symmetric-three quotients in the solvable Thompson branch

Apply the genuine B.2.16 to A = J(DR₁)R₁. The full omega-center closure
has centralizer O₂(A), and the factorization alternative has been excluded.
The three-rank bound passes through this two-group kernel. Exactly one
marked PSL₂(2) factor therefore occurs, giving J/O₂(J) ≃ S₃ and m₃(J)=1.
The Thompson image is normal in A/O₂(A), with two-group quotient; since
that quotient is two-reduced, the normal-S₃ extension lemma identifies
A/O₂(A) itself with S₃.

This module does not identify O₂(A) with the old core O₂(DR₁). The latter
comparison remains necessary for the quotient consumed by 14.7.31. The
universal B.2.16 is the explicit earlier-source input owned by qt-b-02;
the rank upper bound is independently produced by
qt-14-07-residual-thompson-three-rank.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.67(4), printed pp.1070–1071; B.2.16, printed p.79.
-/

@[expose] public section
noncomputable section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Theory.GroupTheory ResidualNormalizer
open Chapter1.RadicalNormalizers.ThompsonSource ResidualThompsonRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace ResidualNormalizer

/-- The intrinsic Thompson subgroup of JR₁ has ambient image J(DR₁). -/
theorem JR_intrinsic_thompson_map :
    (elementaryAbelianMaxJ (⊤ : Subgroup (JR L F))).map (JR L F).subtype = J L F := by
  rw [← elementaryAbelianMaxJ_map_injective _ (JR L F).subtype_injective,
    ← MonoidHom.range_eq_map, range_subtype, JR_thompson_eq_J]

/-- The literal intrinsic-to-ambient identification of the Thompson group. -/
noncomputable def intrinsicThompsonEquiv :
    elementaryAbelianMaxJ (⊤ : Subgroup (JR L F)) ≃* J L F :=
  ((elementaryAbelianMaxJ (⊤ : Subgroup (JR L F))).equivMapOfInjective
    (JR L F).subtype (JR L F).subtype_injective).trans
      (MulEquiv.subgroupCongr JR_intrinsic_thompson_map)

end ResidualNormalizer

namespace Data
variable (d : Data T L V F W)
include d

/-- The rank bound survives the actual two-group centralizer kernel. -/
theorem residual_thompsonClosure_three_rank_le
    (hr : primeRank 3 (Y L F) ≤ 1)
    (S : Sylow 2 (JR L F)) (hS : (S : Subgroup (JR L F)).map (JR L F).subtype = F.Ri L 1) :
    primeRank 3 (CentralQuotient (Chapter1.RadicalNormalizers.ThompsonSource.closure S)) ≤ 1 := by
  have he := QuotientGroup.quotientMulEquivOfEq (d.residual_thompsonOmega_centralizer S hS)
  rw [Theory.GroupTheory.primeRank_equiv 3 he]
  exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
    ((primeRank_mono 3 JR_le_Y).trans hr)

/-- The source J/O₂(J) is the actual symmetric group on three letters. -/
theorem residual_thompson_quotient_symmetricThree
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hsol : Group.IsSolvable (J L F)) (hr : primeRank 3 (Y L F) ≤ 1)
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F)) :
    Nonempty ((J L F ⧸ pCore 2 (J L F)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨S, hS⟩ := residual_thompsonJoin_sylow hSylow
  have hc := hB (JR L F) (residual_thompsonJoin_solvable hsol)
    (d.residual_thompsonJoin_generalizedFitting hSylow) S
  let := hc.elementary
  obtain ⟨ex⟩ := d.residual_thompsonJoin_exceptional hB hsol hDM hSylow hBaum hD S hS
  let q := Chapter1.RadicalNormalizers.ThompsonSource.starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure S)
  let N := elementaryAbelianMaxJ (⊤ : Subgroup (JR L F))
  let e := exceptionalThompsonEquiv ex (d.residual_thompsonClosure_three_rank_le hr S hS)
  let e₀ : N ≃* J L F := intrinsicThompsonEquiv
  let f := e.toMonoidHom.comp ((q.subgroupMap N).comp e₀.symm.toMonoidHom)
  have hf : Function.Surjective f := e.surjective.comp
    ((q.subgroupMap_surjective N).comp e₀.symm.surjective)
  have hq : IsPGroup 2 q.ker := by
    rw [show q.ker = centralizer
      (Chapter1.RadicalNormalizers.ThompsonSource.closure S : Set (JR L F)) from QuotientGroup.ker_mk' _,
      d.residual_thompsonOmega_centralizer S hS]
    exact pCore_isPGroup
  have hk : IsPGroup 2 f.ker := by
    apply (hq.comap_of_injective (N.subtype.comp e₀.symm.toMonoidHom)
      (Subtype.val_injective.comp e₀.symm.injective)).to_le
    intro x hx
    have he : q.subgroupMap N (e₀.symm x) = 1 := e.injective (hx.trans e.map_one.symm)
    exact congrArg Subtype.val he
  have hker := ker_eq_twoCore_of_surjective_perm_three f hf hk
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

/-- The intermediate group modulo its own core is S₃. The old-core quotient
needed by 14.7.31 still requires a separate comparison. -/
theorem residual_thompsonJoin_newCore_quotient_symmetricThree
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hsol : Group.IsSolvable (J L F)) (hr : primeRank 3 (Y L F) ≤ 1)
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F)) :
    Nonempty ((JR L F ⧸ pCore 2 (JR L F)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨S, hS⟩ := residual_thompsonJoin_sylow hSylow
  have hc := hB (JR L F) (residual_thompsonJoin_solvable hsol)
    (d.residual_thompsonJoin_generalizedFitting hSylow) S
  let := hc.elementary
  obtain ⟨ex⟩ := d.residual_thompsonJoin_exceptional hB hsol hDM hSylow hBaum hD S hS
  let q := Chapter1.RadicalNormalizers.ThompsonSource.starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure S)
  let N := elementaryAbelianMaxJ (⊤ : Subgroup (JR L F))
  let : N.Characteristic := elementaryAbelianMaxJ_top_characteristic
  let : N.Normal := inferInstance
  let : (N.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let e := exceptionalThompsonEquiv ex (d.residual_thompsonClosure_three_rank_le hr S hS)
  have hgen : N ⊔ (S : Subgroup (JR L F)) = ⊤ := by
    apply map_injective (JR L F).subtype_injective
    rw [Subgroup.map_sup, JR_intrinsic_thompson_map, hS,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hgenq : N.map q ⊔ (S : Subgroup (JR L F)).map q = ⊤ := by
    rw [← Subgroup.map_sup, hgen]
    exact map_top_of_surjective q (QuotientGroup.mk'_surjective _)
  have hp := isPGroup_quotient_of_sup_eq_top (N.map q) _ (S.isPGroup'.map q) hgenq
  have htop := normal_symmetricThree_eq_top (N.map q) e hp hc.reduced
  let ebar := (topEquiv : (⊤ : Subgroup (CentralQuotient
    (Chapter1.RadicalNormalizers.ThompsonSource.closure S))) ≃* _).symm.trans
    ((MulEquiv.subgroupCongr htop.symm).trans e)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (d.residual_thompsonOmega_centralizer S hS).symm).trans ebar⟩

/-- The same source J has three-rank exactly one. -/
theorem residual_thompson_three_rank_eq_one
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hsol : Group.IsSolvable (J L F)) (hr : primeRank 3 (Y L F) ≤ 1)
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F)) : primeRank 3 (J L F) = 1 := by
  obtain ⟨e⟩ := d.residual_thompson_quotient_symmetricThree hB hsol hr hDM hSylow hBaum hD
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (J L F)))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hd : 3 ∣ Nat.card (J L F) := by
    have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by rw [Nat.card_perm, Nat.card_fin]; decide
    have hh := card_dvd_of_surjective f hf
    rw [hc] at hh
    exact dvd_trans (by decide : 3 ∣ 6) hh
  have hn : primeRank 3 (J L F) ≠ 0 := fun h => PrimeRank.eq_zero_iff_not_dvd_card.mp h hd
  have hu := (primeRank_mono 3 J_le_Y).trans hr
  omega

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
