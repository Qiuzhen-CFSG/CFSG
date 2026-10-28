module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.Congruence
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.SymmetricEight
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The original radical action in the remaining pure-point obstruction

Transporting the literal LT-normalizer through its action quotient and
its eight-point permutation marking identifies the image of O₂(X) with
the original sixteen-element parabolic radical. In particular O₂(X)
acts nontrivially on the original doubled module, without an MS premise.

The source consumer combines this calculation with the checked component
exclusions and cubic-normalizer congruence. Every remaining contrary Sylow
configuration has p = 11 or 13 modulo 24, full quotient Sylow intersection,
and noncentral action of both O₂(K₀) and O₂(H). The same cubic complement
satisfies [O₂(K₀),A] = O₂(X). All original component markings, maximality
and Fundamental Setup are retained.

This is a reduction, not the ambient Sylow contradiction or pure fusion.
The remaining noncentral case, point-core control and fusion/abelian closure
stay with this task. The explicit original fixed-subgroup MS premise stays
with `qt-rank-two-ms93` and final `qt-d-double-natural-centralizers`.
Source: Aschbacher--Smith 12.1.4, printed pp.790--791, and B.4.9(2iii),
pp.92,94; the concrete radical calculation is proved in `SymmetricEight`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open ChapterH.NaturalDual.SourceFourActors
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {B : DoubledBranch T L V 4}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
/-- The original two-core acts through precisely the marked parabolic radical. -/
theorem four_xi_core_image
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hm : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G)) :
    (((PureFourXi.residual T L).pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G))).map
      (B.joinActionProjection hTM) =
      A0 S.setup ((T.subtype hTM).mapSurjective B.actionProjection_surjective) := by
  let H := L ⊔ (T : Subgroup G)
  let N := (normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)).subgroupOf H
  let X := PureFourXi.residual T L
  let f := B.joinActionProjection hTM
  let P := (T.subtype hTM).mapSurjective B.actionProjection_surjective
  let e := permutation S.setup P
  have hXH : X ≤ H := (map_subtype_le _).trans inf_le_right
  have hX : X.subgroupOf H = (pResidual 2 N).map N.subtype := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hXH,map_embedded_pResidual]
    rw [show N.map H.subtype = PureFourXi.normalizerJoin T L from subgroupOf_map_subtype _ _]
    rfl
  have hN : N.map f = normalizer (A0 S.setup P : Set B.ActionQuotient) :=
    S.four_thompson_normalizer_image hTM hWT hm
  have hXimage : (X.subgroupOf H).map (e.toMonoidHom.comp f) =
      PureFourXi.SymmetricEight.blockResidual := by
    rw [hX,map_embedded_pResidual,←map_map,hN,S.setup.four_A0_normalizer P]
    rfl
  have hk : IsPGroup 2 (e.toMonoidHom.comp f).ker := by
    have he : (e.toMonoidHom.comp f).ker = f.ker := by
      ext x
      exact e.map_eq_one_iff
    rw [he]
    exact (S.four_join_action hTM).2.1
  have hc : (((X.pCoreIn 2).subgroupOf H).map f).map e.toMonoidHom =
      BinaryNaturalDual.FourActors.permutationA0 := by
    rw [map_map,←pCoreIn_subgroupOf 2 X H hXH,
      map_pCoreIn_of_ker_isPGroup _ hk,hXimage,PureFourXi.SymmetricEight.blockResidual_core]
  have hA : (A0 S.setup P).map e.toMonoidHom =
      BinaryNaturalDual.FourActors.permutationA0 := by
    change (A0 S.setup P).map (BinaryNaturalDual.FourActors.permutationEquiv.toMonoidHom.comp
      (group S.setup P).toMonoidHom) = _
    rw [←map_map,actor_map]
    exact BinaryNaturalDual.FourActors.PermutationCatalogue.actor_map 0
  exact (map_injective e.injective) (hc.trans hA.symm)

include S in
/-- The original residual radical acts nontrivially on W, before any MS input. -/
theorem four_xi_core_moves
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hm : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G)) :
    ¬ (PureFourXi.residual T L).pCoreIn 2 ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
  intro hc
  have him := S.four_xi_core_image hTM hWT hm
  have hz : (((PureFourXi.residual T L).pCoreIn 2).subgroupOf
      (L ⊔ (T : Subgroup G))).map (B.joinActionProjection hTM) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro x hx
    change B.actionProjection (inclusion (sup_le L.le_normalizer hTM) x) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [normalizerAction_ker]
    exact hc hx
  rw [hz] at him
  have hh := actor_card S.setup
    ((T.subtype hTM).mapSurjective B.actionProjection_surjective) 0
  change Nat.card (A0 S.setup
    ((T.subtype hTM).mapSurjective B.actionProjection_surjective)) = 16 at hh
  rw [←him,card_bot] at hh
  norm_num at hh
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The remaining original obstruction has noncentral containing radicals, the
11/13 modulo 24 congruence, and the literal cubic commutator identity. -/
theorem doubleNatural_four_pure_noncentral_swapped_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ →
      let X := PureFourXi.residual T L
      ∃ P : Sylow 2 G, B.pointSylow w < (P : Subgroup G) ∧
        (P : Subgroup G) ≤ B.pointCentralizer w ∧
        (P : Subgroup G) ⊓ normalizer (L : Set G) = B.pointSylow w ∧
        (P : Subgroup G) ≤ normalizer (B.pointSylow w : Set G) ∧
        (B.pointSylow w).relIndex (T : Subgroup G) = 2 ∧
        let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
        H ∈ HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G) ∧
        H ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
        ¬ H ≤ normalizer (L : Set G) ∧
        ∃ A : Sylow 3 X, ∃ K : Subgroup G,
          SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X
            ((A : Subgroup X).map X.subtype) H K ∧
          conjugateSpanBy X H = componentOrbit K (T : Subgroup G) ∧
          X < componentOrbit K (T : Subgroup G) ∧
          (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient K) 2 p ∧
            (p % 8 = 3 ∨ p % 8 = 5) ∧ (p % 24 = 11 ∨ p % 24 = 13)) ∧
          quotientImage (componentOrbit K (T : Subgroup G)) (B.pointSylow w) =
            quotientImage (componentOrbit K (T : Subgroup G)) (T : Subgroup G) ∧
          X.pCoreIn 2 ≤ (componentOrbit K (T : Subgroup G)).pCoreIn 2 ∧
          (¬ (componentOrbit K (T : Subgroup G)).pCoreIn 2 ≤
            centralizer (componentOrbit V (T : Subgroup G) : Set G)) ∧
          (¬ H.pCoreIn 2 ≤ centralizer (componentOrbit V (T : Subgroup G) : Set G)) ∧
          ⁅(componentOrbit K (T : Subgroup G)).pCoreIn 2,
            ((A : Subgroup X).map X.subtype)⁆ = X.pCoreIn 2 ∧
          ¬ ClassicalGroup.IsPSL (XiQuotient K) 2 4 ∧
          K ∈ Chapter1.LStar G (T : Subgroup G) ∧
          K ∈ MainForward.faithfulLocalComponents T ∧
          Nonempty (Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨P,hlt,hPC,hPM,hPN,hiT,hH,hHN,hout,A,K,hs,he,hstrict,hodd,hfull,hcore,hA5,hmax,hfaith,hFS⟩ :=
    D.doubleNatural_four_pure_collapsed_swapped_of_many_of_omega_fixed
      h hmany B S w hw hp hfix hf hne
  let X := PureFourXi.residual T L
  let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
  let Y := componentOrbit K (T : Subgroup G)
  obtain ⟨p,hp',ho,hm,hmod⟩ := hodd
  have hmove := S.four_xi_core_moves D.sylow_normalizes_component
    (D.doubledOrbit_E322 h).le_sylow
    (D.doubleNatural_four_pure_thompson_moves_of_many h hmany B S w hw hp hfix hf).2
  have hmoveY : ¬ Y.pCoreIn 2 ≤ centralizer (componentOrbit V (T : Subgroup G) : Set G) :=
    fun hc => hmove (hcore.trans hc)
  have hYH : Y ≤ H := SwappedSylow.orbit_le_overgroup hs.toSwappedInput
  have hHY : H ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYH).mp hs.orbit_normal
  have hmoveH : ¬ H.pCoreIn 2 ≤ centralizer (componentOrbit V (T : Subgroup G) : Set G) :=
    fun hc => hmoveY ((pCoreIn_mono_of_normalizes hYH hHY).trans hc)
  exact ⟨P,hlt,hPC,hPM,hPN,hiT,hH,hHN,hout,A,K,hs,he,hstrict,
    ⟨p,hp',ho,hm,hmod,PureFourXi.collapsed_small_prime_mod24 T hs hp' ho hm hmod hcore⟩,
    hfull,hcore,hmoveY,hmoveH,PureFourXi.collapsed_core_commutator T hs hcore,hA5,hmax,hfaith,hFS⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
