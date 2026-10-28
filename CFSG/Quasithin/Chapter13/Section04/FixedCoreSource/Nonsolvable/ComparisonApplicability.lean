module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.LinearChiefFactors
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.PairCentralizers

/-!
# Applying the two-parabolic amalgam theorem at both escaping weights

The weight-two pair has the required two noncentral binary chief factors.
Uniqueness inside the Thompson normalizer identifies its selected parabolic
with the one used for the weight-four comparison. The actual centralizer
intersections discharge the remaining applicability clauses of 13.4.7.
Its commutator alternative contradicts the residual normalization obstruction;
its Thompson-normalizer alternative contradicts the other comparison bound.

The general-pair consequence of earlier 13.4.7 is retained as an explicit
source input, distinct from the restricted plane-pair input. Its proof remains
with the fixed-core source owner. The result here treats all four combinations
of recognized linear-three and ordinary alternating-six components; selecting
and recognizing these components remains a separate source step.

Source: Aschbacher--Smith, 13.4.7(1) and the both-weight comparison in
13.4.12, printed pp.899--901,910.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The consequence of earlier 13.4.7(1) needed for an arbitrary applicable
pair. This is an explicit source input, not a proof of 13.4.7. In case (i)
use its two residual bounds; in cases (ii)--(iv) use Thompson normality.
The restricted plane input alone does not imply this proposition. Its
construction retains ownership with qt-d-1341-fixed-core-source. -/
@[expose] def PairAmalgamSource1347 (T : Sylow 2 G) : Prop :=
  ∀ P Q : Subgroup G,
    let R := (pResidual 2 P).map P.subtype
    let S := (pResidual 2 Q).map Q.subtype
    let X := P ⊔ Q
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (R : Set G) : Subgroup G) : Set G)
    let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (S : Set G) : Subgroup G) : Set G)
    P ∈ Chapter1.HOver G (T : Set G) → Q ∈ Chapter1.HOver G (T : Set G) →
    Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) →
    Nonempty ((Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 3)) → P ≠ Q →
    ((∀ s : NoncentralChiefRefinement.ChiefSeries R,
        s.head = ⊥ → s.last = ⊤ → 2 ≤ s.noncentralTwoCount) ∨
     (∀ s : NoncentralChiefRefinement.ChiefSeries S,
        s.head = ⊥ → s.last = ⊤ → 2 ≤ s.noncentralTwoCount)) →
    (Z ⊓ centralizer (P : Set G)).relIndex Z = 2 →
    (Z ⊓ centralizer (Q : Set G)).relIndex Z = 2 →
    (X ∈ Chapter1.HOver G (T : Set G) →
      (R.subgroupOf C₁).Normal ∧ (S.subgroupOf C₂).Normal ∧
      ((primeToResidual 3 C₁).map C₁.subtype = R ∨
        (primeToResidual 3 C₂).map C₂.subtype = S)) →
    (⁅R,S⁆ ≤ R.pCoreIn 2 ⊓ S.pCoreIn 2 ∨
      X ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))

variable {T : Sylow 2 G} {L V : Subgroup G}
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
/-- The two escaping weights cannot coexist in any combination of the
recognized component rows. All P₂/P₄ applicability clauses are discharged;
only the genuine earlier general-pair and plane amalgam inputs remain. -/
theorem small_components_both_weights_false
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (h1347 : Solvable.PlaneAmalgamSource1347 D m)
    (z w : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hwT : w.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hwL : w.val ∉ centralizer (L : Set G))
    (hz : m.weight z = 2) (hw : m.weight w = 4)
    (K N : Subgroup G)
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hKN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (model : Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)))
    (hN : N ∈ Chapter1.cComponentsIn (centralizer ({w.val} : Set G)))
    (hNN : centralizer ({w.val} : Set G) ≤ normalizer (N : Set G))
    (hNM : ¬ N ≤ normalizer (L : Set G))
    (hfN : N ∈ MainForward.faithfulLocalComponents T)
    (modelN : Nonempty ((N ⧸ pCore 2 N) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 6)))
    (hpair1347 : PairAmalgamSource1347 T) : False := by
  obtain ⟨W,hW,hT,P,Q,hP,hQ,hPz,hQw,⟨eP⟩,⟨eQ⟩,hne,hlocal,hfixP,hfixQ,
      hX,hmax,hquot,hu,hQlocal,hcomm,hBN,hnorm,hnotJ,haction⟩ :=
    small_components_both_weights_comparison hl h₀ h structural modules D m h1332 fixed
      hindex hM h1347 z w hzT hwT hzL hwL hz hw K N hK hKN hKM hfK model
      hN hNN hNM hfN modelN
  obtain ⟨W',hW',hT',P',hP',hP'z,_,hlin,hchief⟩ := small_component_weight_two_chief_amalgam
    hl h₀ h structural modules D m h1332 fixed hindex hM h1347 z hzT hzL
      hK hKN hKM hfK model hz
  have hP'P : P' = P := hu P' hP' (by
    rw [hX]
    exact le_sup_left.trans hlin.2.1)
  have hchiefP : ∀ s : NoncentralChiefRefinement.ChiefSeries ((pResidual 2 P).map P.subtype),
      s.head = ⊥ → s.last = ⊤ → 2 ≤ s.noncentralTwoCount := hP'P ▸ hchief
  have hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V := by
    rcases model with he | he <;> obtain ⟨eK⟩ := he
    · obtain ⟨_,_,_,_,_,_,_,_,_,hZ,_⟩ := linear_component_geometry
        hl h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK.1 hKN hKM hfK eK
      exact hZ.le.trans inf_le_left
    · obtain ⟨_,_,_,_,_,_,hZ,_⟩ := ordinary_six_component_geometry
        h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hKN hKM hfK eK
      exact hZ.le.trans inf_le_left
  have hz1 : z ≠ 1 := fun he => hzL (congrArg Subtype.val he ▸ one_mem _)
  have hw1 : w ≠ 1 := fun he => hwL (congrArg Subtype.val he ▸ one_mem _)
  have hzw : z ≠ w := by intro he; rw [he,hw] at hz; omega
  have hiP := escaping_residual_fixed_index h structural m z hz1 hzT P hP hPz.le
  have hiQ := escaping_residual_fixed_index h structural m w hw1 hwT Q hQ hQw.le
  rw [inf_eq_right.mpr hZV,Amalgam.omega_fixed_twoResidual P hP.1.1.2] at hiP
  rw [inf_eq_right.mpr hZV,Amalgam.omega_fixed_twoResidual Q hQ.1.1.2] at hiQ
  obtain ⟨_,_,_,_,hnP,hnQ,hrP,_⟩ := escaping_pair_residual_centralizers h₀ h structural
    D m h1332 hZV z w hz1 hw1 hzw hzT hwT hP hQ hPz hQw eP eQ K N hK hfK hN hfN
  rcases hpair1347 P Q hP.1.1 hQ.1.1 ⟨eP⟩ ⟨eQ⟩ hne (Or.inl hchiefP) hiP hiQ
      (fun _ => ⟨hnP,hnQ,Or.inl hrP⟩) with hc | hJ
  · exact hnorm (le_normalizer_iff_commutator_le_right.mpr
      ((hc.trans inf_le_right).trans (pCoreIn_le 2 _)))
  · exact hnotJ hJ

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
