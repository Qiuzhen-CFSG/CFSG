module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation.LocalSetup
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.BinaryRecognition.DiagramAction.CubicLifts
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource.PairGeometry
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# Inner Sylow action in the four-dimensional branch of 15.3.24

The actual quotient Y₊S/O₂(Y₊S) is S₃ × S₃. Its two normal cubic axes
lift to individually S-invariant two-perfect subgroups of L. Their images
in L/O₂(L) retain cubic two-core quotients and a join quotient of order nine.
The common-coordinate theorem identifies their Sylow joins as two distinct
minimal parabolics. An automorphism fixing both is inner, so graph
interchange is excluded by the actual quotient action.

We work in LS using `component_join_reduction`; only the restriction of L
to this overgroup is normal. The final transport agrees with the specified
`sylowCoreAction` on every quotient representative. No fixed-node hypothesis
or compatibility between independently chosen model markings is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, first
paragraph of 15.3.24, printed p.1129 (PDF p.1146). The cubic lifting argument
also occurs in 15.3.35; common flag coordinates use the checked intrinsic
geometry from 13.8.25, printed pp.959–960.
-/

public section
open Subgroup BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation.DiagramAction
open CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.BinaryRecognition.DiagramAction
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource

private theorem core_quotient_card_image {X H : Type*} [Group X] [Finite X]
    [Group H] [Finite H] (f : X →* H) (hk : IsPGroup 2 f.ker) (A : Subgroup X) :
    Nat.card (A.map f ⧸ pCore 2 (A.map f)) = Nat.card (A ⧸ pCore 2 A) := by
  apply (Nat.card_congr (MonoidHom.quotientPCoreEquivOfSurjective
    (f.subgroupMap A) (f.subgroupMap_surjective A) ?_).toEquiv).symm
  rw [ker_subgroupMap]
  exact hk.comap_subtype

private theorem invariant_image {X H : Type*} [Group X] [Group H]
    (f : X →* H) (a : MulAut X) (b : MulAut H)
    (hf : ∀ x, f (a x) = b (f x)) (A : Subgroup X)
    (hA : A.map a.toMonoidHom = A) : (A.map f).map b.toMonoidHom = A.map f := by
  have he : b.toMonoidHom.comp f = f.comp a.toMonoidHom := by
    ext x
    exact (hf x).symm
  rw [Subgroup.map_map, he, ← Subgroup.map_map, hA]

/-- Lift both cubic axes, retain their invariance through the core quotient,
and recognize their two distinct minimal parabolics in common coordinates. -/
private theorem core_action_inner {X : Type*} [Group X] [Finite X]
    (D Y : Subgroup X) [D.Normal] (S : Sylow 2 X) (hYD : Y ≤ D)
    (hn : (S : Subgroup X) ≤ normalizer (Y : Set X))
    (he : Nonempty (((Y ⊔ (S : Subgroup X) : Subgroup X) ⧸
      pCore 2 (Y ⊔ (S : Subgroup X) : Subgroup X)) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (e : (D ⧸ pCore 2 D) ≃* LinearGroup 4) :
    ∀ s ∈ (S : Subgroup X),
      quotientAut (pCore 2 D) (MulAut.conjNormal s) ∈
        MulAut.innerSubgroup (D ⧸ pCore 2 D) := by
  let : Finite (LinearGroup 4) := Finite.of_equiv _ e.toEquiv
  obtain ⟨A, B, ha, hb, hca, hcb, hcab, hA, hB⟩ :=
    CubicLifts.exists_invariant_cubic_pair D Y S hYD S.isPGroup' hn he
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal D
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    have heq : f.ker = pCore 2 D := by
      ext x
      change e (QuotientGroup.mk' (pCore 2 D) x) = 1 ↔ _
      rw [e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff x
    rw [heq]
    exact pCore_isPGroup
  let U := T.mapSurjective hf
  have hnA : (T : Subgroup D) ≤ normalizer (A : Set D) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    simpa only [MulAut.conjNormal_val, MulEquiv.toMonoidHom_eq_coe] using
      hA (x : X) (show x ∈ (S : Subgroup X).subgroupOf D from hT ▸ hx)
  have hnB : (T : Subgroup D) ≤ normalizer (B : Set D) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    simpa only [MulAut.conjNormal_val, MulEquiv.toMonoidHom_eq_coe] using
      hB (x : X) (show x ∈ (S : Subgroup X).subgroupOf D from hT ▸ hx)
  have hcab' : Nat.card ((A.map f ⊔ B.map f : Subgroup _) ⧸
      pCore 2 (A.map f ⊔ B.map f : Subgroup _)) = 9 := by
    rw [← Subgroup.map_sup, core_quotient_card_image f hk, hcab]
  obtain ⟨b, i, j, _, hAi, hBj, _, _, _, _, _, _, _, _, _, _, hne⟩ :=
    PairGeometry.four_common_coordinates U (A.map f) (B.map f)
      (ha.of_surjective (f.subgroupMap A) (f.subgroupMap_surjective A))
      (hb.of_surjective (f.subgroupMap B) (f.subgroupMap_surjective B))
      ((map_mono hnA).trans (le_normalizer_map _))
      ((map_mono hnB).trans (le_normalizer_map _))
      ((core_quotient_card_image f hk A).trans hca)
      ((core_quotient_card_image f hk B).trans hcb) hcab'
  change A.map f ⊔ (U : Subgroup _) = minimalParabolic b i at hAi
  change B.map f ⊔ (U : Subgroup _) = minimalParabolic b j at hBj
  intro s hs
  let a := quotientAut (pCore 2 D) (MulAut.conjNormal s)
  let b' := MulAut.congr e a
  have hfa : ∀ x, f (MulAut.conjNormal s x) = b' (f x) := by
    intro x
    change e (QuotientGroup.mk' (pCore 2 D) (MulAut.conjNormal s x)) =
      e (a (e.symm (e (QuotientGroup.mk' (pCore 2 D) x))))
    rw [e.symm_apply_apply, quotientAut_apply_mk]
  have hTs : (T : Subgroup D).map (MulAut.conjNormal s).toMonoidHom = T := by
    rw [hT]
    ext x
    rw [mem_map_equiv]
    change ((MulAut.conjNormal s).symm x : X) ∈ (S : Subgroup X) ↔ (x : X) ∈ S
    rw [MulAut.conjNormal_symm_apply]
    constructor
    · intro hx
      change (x : X) ∈ (S : Subgroup X)
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right,
        mul_inv_cancel, mul_one] using
        (S : Subgroup X).mul_mem ((S : Subgroup X).mul_mem hs hx) ((S : Subgroup X).inv_mem hs)
    · intro hx
      exact (S : Subgroup X).mul_mem
        ((S : Subgroup X).mul_mem ((S : Subgroup X).inv_mem hs) hx) hs
  have hUi : (U : Subgroup (LinearGroup 4)).map b'.toMonoidHom = U :=
    invariant_image f _ b' hfa T hTs
  have hi : b' ∈ MulAut.innerSubgroup (LinearGroup 4) := by
    apply preserving_two_minimalParabolics_is_inner (by decide) (by decide) b b i j U
      (hAi ▸ le_sup_right) (hBj ▸ le_sup_right) (by rwa [← hAi, ← hBj]) b'
    · rw [← hAi, Subgroup.map_sup, invariant_image f _ b' hfa A (hA s hs), hUi]
    · rw [← hBj, Subgroup.map_sup, invariant_image f _ b' hfa B (hB s hs), hUi]
  rw [← MulAut.map_innerSubgroup_congr e, mem_map_equiv] at hi
  change (MulAut.congr e).symm ((MulAut.congr e) a) ∈ _ at hi
  simpa only [MulEquiv.symm_apply_apply] using hi
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation.DiagramAction

open Subgroup BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation
variable {G : Type*} [Group G]

/-- The Sylow action on the actual component quotient is inner in the
four-dimensional branch of the first paragraph of 15.3.24. -/
theorem sylow_inner_four [Finite G] {d : LocalData G} {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (_hrank : primeRank 3 d.Yplus = 2) (c : ComponentWitness d I)
    (h : Earlier d c) (e : (c.L ⧸ pCore 2 c.L) ≃* Projective 4) :
    IsInnerOnComponent d c.L h.sylow_normalizes_component := by
  obtain ⟨_, _, hS, _, _, _, hD, _⟩ :=
    component_join_reduction d hI h.sylow hf c h.yplus_le h.component_eq_theta h.solvable_control
  let K := c.L ⊔ d.S
  let D := c.L.subgroupOf K
  let Y := d.Yplus.subgroupOf K
  let : D.Normal := hD
  obtain ⟨S, hS⟩ := hS
  have hS' : (S : Subgroup K) = d.S.subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hS, map_subgroupOf_eq_of_le le_sup_right]
  have hYK : d.Yplus ≤ K := h.yplus_le.trans le_sup_left
  have hjoin : Y ⊔ (S : Subgroup K) = (d.Yplus ⊔ d.S).subgroupOf K := by
    rw [hS', ← subgroupOf_sup hYK (show d.S ≤ K from le_sup_right)]
  let a : (Y ⊔ (S : Subgroup K) : Subgroup K) ≃* (d.Yplus ⊔ d.S : Subgroup G) :=
    (MulEquiv.subgroupCongr hjoin).trans (subgroupOfEquivOfLe (sup_le hYK le_sup_right))
  obtain ⟨eJ⟩ := (source_quotients h (Or.inl rfl) e).2
  have heJ : Nonempty (((Y ⊔ (S : Subgroup K) : Subgroup K) ⧸
      pCore 2 (Y ⊔ (S : Subgroup K) : Subgroup K)) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :=
    ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eJ⟩
  have hnY : (S : Subgroup K) ≤ normalizer (Y : Set K) := by
    rw [hS']
    exact (comap_mono h.sylow_normalizes_yplus).trans (le_normalizer_comap K.subtype)
  let dL : D ≃* c.L := subgroupOfEquivOfLe le_sup_left
  let qL : (D ⧸ pCore 2 D) ≃* (c.L ⧸ pCore 2 c.L) :=
    QuotientGroup.congr _ _ dL (pCore_map_iso 2 dL)
  have hi := DiagramAction.core_action_inner D Y S
    (show Y ≤ D from comap_mono h.yplus_le) hnY heJ
    (qL.trans (e.trans (projectiveEquivLinear (by decide))))
  intro s
  let sK : K := ⟨s, mem_sup_right s.property⟩
  have hsK : sK ∈ (S : Subgroup K) := by
    rw [hS']
    exact s.property
  have hi' : MulAut.congr qL (quotientAut (pCore 2 D) (MulAut.conjNormal sK)) ∈
      MulAut.innerSubgroup (c.L ⧸ pCore 2 c.L) := by
    rw [← MulAut.map_innerSubgroup_congr qL]
    exact mem_map.mpr ⟨_, hi sK hsK, rfl⟩
  have haction : MulAut.congr qL (quotientAut (pCore 2 D) (MulAut.conjNormal sK)) =
      sylowCoreAction d c.L h.sylow_normalizes_component s := by
    apply MulEquiv.ext
    intro x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 c.L) x
    obtain ⟨l, rfl⟩ := dL.surjective l
    have hq (l : D) : qL (QuotientGroup.mk' (pCore 2 D) l) =
        QuotientGroup.mk' (pCore 2 c.L) (dL l) := QuotientGroup.congr_mk' _ _ _ _ l
    rw [← hq l]
    change qL (quotientAut (pCore 2 D) (MulAut.conjNormal sK)
      (qL.symm (qL (QuotientGroup.mk' (pCore 2 D) l)))) = _
    rw [qL.symm_apply_apply, quotientAut_apply_mk, hq, hq, sylowCoreAction_apply]
    congr 1
  exact haction ▸ hi'

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation
