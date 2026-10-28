module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionUnitaryModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionLayers

/-!
# Excluding the ordinary unitary-four point row for the selected diagram

The actual second parabolic R S A normalizes R ∩ O₂(O²(H)): each of R,
S and the original left Cartan preserves both terms. Its intrinsic image
is therefore normal, and lies in the parabolic two-core. Perfectness puts
R in the parabolic solvable residual. The concrete U₄ Frattini dichotomy
then contradicts one of the two noncentral layers, without assuming a
chief-factor upper bound or identifying R with the whole residual O²(H).

This is the ordinary point-row comparison in 5.2.6. The degree-two
extension and the other model rows require their own comparisons; no
amalgam classification or ambient recognition is asserted here.
Source: Aschbacher–Smith, printed pp.650–651 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

private theorem core_dichotomy_excludes_layer
    {Y X : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y] [Group X] [Finite X]
    {N : Subgroup Y} (h : NoncentralCoreLayer N)
    (f : Y →* X) (hf : Function.Injective f) (hn : (N.map f).Normal)
    (hQ : (pCore 2 Y).map f ≤ pCore 2 X)
    (hD : ∀ D : Subgroup X, D.Normal → D ≤ pCore 2 X →
      ⁅D,solvableResidual X⁆ = ⊥ ∨ D = pCore 2 X) : False := by
  let := hn
  let : Group.IsPerfect f.range := by
    rw [MonoidHom.range_eq_map]
    exact Group.IsPerfect.map f
  have hr : f.range ≤ solvableResidual X := le_solvableResidual_of_isPerfect _
  rcases hD (N.map f) hn ((map_mono h.2.1).trans hQ) with hc | he
  · have hh : ⁅N,(⊤ : Subgroup Y)⁆ = ⊥ := by
      apply map_injective hf
      rw [map_commutator,←MonoidHom.range_eq_map,Subgroup.map_bot]
      exact le_bot_iff.mp ((commutator_mono le_rfl hr).trans hc.le)
    exact h.2.2.1 (by
      simpa only [coe_top,centralizer_univ] using commutator_eq_bot_iff_le_centralizer.mp hh)
  · have hle : pCore 2 Y ≤ N :=
      (map_le_map_iff_of_injective hf).mp (he ▸ hQ)
    exact h.2.2.2 ((commutator_le_left _ _).trans hle)

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The full second parabolic preserves the original intermediate layer;
normality is relative to this parabolic, not to the ambient simple group. -/
theorem Preparation.right_parabolic_normalizes_layer
    {T : Sylow 2 G} {L H A B R : Subgroup G} (d : Preparation T L H A B R)
    (hN : localBorel T L ≤ normalizer (residual H : Set G)) :
    R ⊔ sourceS L H ⊔ A ≤ normalizer ((residual H).pCoreIn 2 ⊓ R : Set G) := by
  have hSH : sourceS L H ≤ H :=
    (map_subtype_le (pCore 2 (intersection L H))).trans inf_le_right
  have hK : R ⊔ sourceS L H ⊔ A ≤ normalizer (residual H : Set G) :=
    sup_le (sup_le (d.right_le_residual.trans (residual H).le_normalizer)
      (hSH.trans (le_normalizer_residual H))) (d.cartans.left_le.trans hN)
  have hQ : R ⊔ sourceS L H ⊔ A ≤ normalizer ((residual H).pCoreIn 2 : Set G) :=
    hK.trans (normalizer_le_normalizer_characteristic_image (residual H) (pCore 2 (residual H)))
  have hR : R ⊔ sourceS L H ⊔ A ≤ normalizer (R : Set G) :=
    sup_le (sup_le R.le_normalizer d.S_normalizes_right) d.cartan_normalizes_right
  exact (le_inf hQ hR).trans inf_normalizer_le_normalizer_inf

open ChapterF.GreenBook.LieModels.UnitaryFour in
/-- The actual right parabolic of a diagram-selected pair cannot be the
unitary-four point parabolic, for any positive field exponent. The model
Frattini calculation discharges the irreducibility comparison in 5.2.6. -/
theorem Preparation.not_unitary_point_parabolic
    {T : Sylow 2 G} {L H A B R : Subgroup G} (d : Preparation T L H A B R)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hp : Group.IsPerfect R)
    (hl : NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R))
    (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty ((R ⊔ sourceS L H ⊔ A : Subgroup G) ≃* pointParabolic m hm) := by
  rintro ⟨e⟩
  let := hp
  let J := R ⊔ sourceS L H ⊔ A
  let R' := R.subgroupOf J
  let N := ((residual H).pCoreIn 2).subgroupOf R
  let f : R →* J := inclusion (show R ≤ J from le_sup_left.trans le_sup_left)
  have hnR : J ≤ normalizer (R : Set G) :=
    sup_le (sup_le R.le_normalizer d.S_normalizes_right) d.cartan_normalizes_right
  let : R'.Normal := normal_subgroupOf_of_le_normalizer hnR
  let r : R ≃* R' :=
    (subgroupOfEquivOfLe (show R ≤ J from le_sup_left.trans le_sup_left)).symm
  have hfr : f = R'.subtype.comp r.toMonoidHom := rfl
  have hQ : (pCore 2 R).map f ≤ pCore 2 J := by
    rw [hfr,←map_map,pCore_map_iso]
    exact le_sSup ⟨inferInstance,pCore_isPGroup.map R'.subtype⟩
  have heN : N.map f = ((residual H).pCoreIn 2 ⊓ R).subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le (inf_le_right.trans (le_sup_left.trans le_sup_left))]
    change N.map R.subtype = _
    exact subgroupOf_map_subtype _ _
  have hn : (N.map f).Normal := by
    rw [heN]
    exact normal_subgroupOf_of_le_normalizer (d.right_parabolic_normalizes_layer hN)
  apply core_dichotomy_excludes_layer hl f (inclusion_injective _) hn hQ
  intro D hD hle
  let := hD
  exact UnitaryFrattini.point_core_dichotomy_of_equiv m hm e D hle

open ChapterF.GreenBook.LieModels.UnitaryFour in
/-- This is the same obstruction on the literal F.1.1 parabolic, with the
original S = O₂(N_G(L) ∩ H), rather than the whole ambient Sylow subgroup. -/
theorem Preparation.not_unitary_point_source_parabolic
    {T : Sylow 2 G} {L H A B R : Subgroup G} (d : Preparation T L H A B R)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hp : Group.IsPerfect R)
    (hl : NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R))
    (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty ((ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) ≃*
      pointParabolic m hm) := by
  rw [d.parabolic_one hTL]
  exact d.not_unitary_point_parabolic hN hp hl m hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
