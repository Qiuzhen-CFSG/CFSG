module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Splitting

/-!
# The source Xi subgroup is not normal in its escaping overgroup

Use the same escaping ambient Sylow P and X from the checked Xi construction.
Both P and T normalize the index-two point Sylow T1. If X were normal in
H = <P,XT>, then P would normalize C_{Omega1(Z(T1))}(X). The proved splitting
identifies this with C_{Omega1(Z(T1))}(L). Its nontriviality and the original
local normalizer uniqueness force P into M, contradicting the escaping Sylow.

Only the literal nontriviality of the L-fixed point omega subgroup remains
as an earlier-source premise. This is the exact consequence of the MS step
needed here; neither the false universal EarlierMSClassifications interface
nor a splitting, centralizer equality, or normalizer callback is assumed.
The existing qt-rank-two-ms93 owner and qt-d-double-natural-pure-fusion must
discharge this original ambient specialization. The latter also retains the
subsequent 1.3.4 component exclusions and final fusion/closure assembly, with
qt-d-double-natural-centralizers as the earlier-input assembly parent.
Source: Aschbacher--Smith 12.1.4, printed p.790, before the use of 1.3.4.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The exact fixed subgroup supplied by the MS step makes X nonnormal in
its original escaping overgroup. No module splitting or local normalizer
callback remains among the premises. -/
theorem doubleNatural_four_pure_xi_nonnormal_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ →
      let X := PureFourXi.residual T L
      X ∈ Chapter1.Xi G (T : Subgroup G) ∧ X ≤ L ∧
        ∃ P : Sylow 2 G, B.pointSylow w < (P : Subgroup G) ∧
          (P : Subgroup G) ≤ B.pointCentralizer w ∧
          (P : Subgroup G) ⊓ normalizer (L : Set G) = B.pointSylow w ∧
          let U := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
          U ∈ Chapter1.HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G) ∧
            X ⊔ (T : Subgroup G) < U ∧
            U ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
            ¬ U ≤ normalizer (L : Set G) ∧ ¬ (X.subgroupOf U).Normal := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  let X := PureFourXi.residual T L
  let R := B.pointSylow w
  let Z := omegaCenterIn R
  let C := Z ⊓ centralizer (L : Set G)
  obtain ⟨hXi,hXL,P,hlt,hPC,hPM,hU,hltU,hUN,hout⟩ :=
    D.doubleNatural_four_pure_xi_overgroup_of_many h hmany B S w hw hp hfix hf
  let U := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
  have he := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
  change R = _ at he
  have hi : R.relIndex (T : Subgroup G) = 2 := by
    rw [he]
    exact S.naturalSylowNormalizer_relIndex D.sylow_normalizes_component
  have hiP : R.relIndex (P : Subgroup G) = 2 := by
    have h1 := relIndex_mul_relIndex (⊥ : Subgroup G) R (T : Subgroup G) bot_le inf_le_left
    have h2 := relIndex_mul_relIndex (⊥ : Subgroup G) R (P : Subgroup G) bot_le hlt.le
    rw [relIndex_bot_left,relIndex_bot_left,hi] at h1
    rw [relIndex_bot_left,relIndex_bot_left] at h2
    have hcard : Nat.card P = Nat.card T := by rw [P.card_eq_multiplicity,T.card_eq_multiplicity]
    rw [hcard,←h1] at h2
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := R)) h2
  let := normal_of_index_eq_two hi
  let := normal_of_index_eq_two hiP
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show R ≤ (T : Subgroup G) from inf_le_left)).mp inferInstance
  have hPR : (P : Subgroup G) ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hlt.le).mp inferInstance
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf (hTR.trans (normalizer_le_normalizer_omegaCenterIn R))
      (D.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
        inf_normalizer_le_normalizer_inf
  have hLC : L ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp (show C ≤ centralizer (L : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCM : normalizer (C : Set G) ≤ normalizer (L : Set G) :=
    D.normal_subgroup_normalizer_le h.toHypothesis1221
      (show C ≤ L ⊔ (T : Subgroup G) from
        inf_le_left.trans ((map_subtype_le _).trans (inf_le_left.trans le_sup_right))) hne
      (sup_le hLC hTC)
  have hfixed : Z ⊓ centralizer (X : Set G) = C :=
    D.doubleNatural_four_point_omega_xi_fixed h B S
      (D.doubleNatural_four_pure_thompson_moves_of_many h hmany B S w hw hp hfix hf).1 w
  refine ⟨hXi,hXL,P,hlt,hPC,hPM,hU,hltU,hUN,hout,?_⟩
  intro hnormal
  have hXU : X ≤ U := le_sup_left.trans le_sup_right
  have hUX : U ≤ normalizer (X : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hXU).mp hnormal
  have hPX : (P : Subgroup G) ≤ normalizer (X : Set G) := le_sup_left.trans hUX
  have hPfix : (P : Subgroup G) ≤ normalizer ((Z ⊓ centralizer (X : Set G) : Subgroup G) : Set G) :=
    (le_inf (hPR.trans (normalizer_le_normalizer_omegaCenterIn R))
      (hPX.trans (normalizer_le_normalizer_centralizer X))).trans inf_normalizer_le_normalizer_inf
  rw [hfixed] at hPfix
  have hPM' := hPfix.trans hCM
  have hPLe : (P : Subgroup G) ≤ R := ((inf_eq_left.mpr hPM').symm.trans hPM).le
  exact (not_le_of_gt hlt) hPLe
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
