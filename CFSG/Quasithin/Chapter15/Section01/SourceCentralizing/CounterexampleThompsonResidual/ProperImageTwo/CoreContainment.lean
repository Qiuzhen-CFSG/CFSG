module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Residual.ThompsonCore
public import Theory.GroupTheory.CharacteristicTwoCoreFour

/-!
# The original four-element Thompson fixed subgroup in a parabolic core

A prepared chosen subgroup has a nonzero seed in Ω₁Z(T). If its Thompson
fixed subgroup E has order four, E is an elementary four normalized by T.
For an overgroup P of T inside C_G(Ω₁Z(T)), the seed supplies a central
involution of P. Characteristic two and the four-group normal-closure
criterion then put this same E in O₂(P).

If the residual of an outside minimal parabolic moves E, its two-core
cannot centralize E: otherwise E lies in the core's central omega, already
centralized by the residual. This retains the actual moving parabolic;
there is no descent to a smaller H-star and no global normalization claim.

Source: Aschbacher--Smith, 15.1.14(1), printed p.1091, using the seed
from 15.1.5(1), characteristic two (1.1.4(6)), and B.6.8(4),(6c).
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original fixed plane lies in the two-core of every Sylow overgroup
inside the centralizer of the original central seed. -/
theorem PreparedChosenModule.thompsonFixed_four_le_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V P : Subgroup G} (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V)
    (hfour : Nat.card (thompsonFixed T V) = 4)
    (hP : P ∈ Chapter1.HOver G (T : Set G))
    (hPC : P ≤ centralizer (centralInvolutions T : Set G)) :
    thompsonFixed T V ≤ P.pCoreIn 2 := by
  let E := thompsonFixed T V
  let := h.elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  have hET : E ≤ (T : Subgroup G) := by
    intro e he
    exact ChapterB.thompsonJ_le _ _
      (((mem_omegaOneCenterAmbient_iff _ e).mp (h.thompsonFixed_le_omega T hM he)).1)
  have hEP : E ≤ P := hET.trans hP.2
  let EP := E.subgroupOf P
  let : IsElementaryAbelian 2 EP := IsElementaryAbelian.subgroupOf hEP
  have hEPcard : Nat.card EP = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv).trans hfour
  have hTJ : (T : Subgroup G) ≤ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change (ChapterB.thompsonJ (T : Subgroup G) 1).map (MulAut.conj t).toMonoidHom = _
    rw [← ChapterB.thompsonJ_map_equiv]
    exact congrArg (fun S => ChapterB.thompsonJ S 1)
      (mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht))
  have hTN : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_inf (hM.1.2.trans h.normalized)
      (hTJ.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hQN : pCore 2 P ≤ normalizer (EP : Set P) := by
    intro q hq
    apply le_normalizer_comap P.subtype
    exact hTN (pCore_isPGroup.le_sylow_of_normal (T.subtype hP.2) hq)
  have hseed : centralInvolutions T ⊓ V ≤ E := by
    refine le_inf inf_le_right ?_
    intro z hz j hj
    exact ((mem_omegaOneCenterAmbient_iff _ z).mp hz.1).2.2 j (ChapterB.thompsonJ_le _ _ hj)
  have hz : centralInvolutions T ⊓ V ≠ ⊥ := by
    intro he
    apply h.nontrivial
    rw [h.seed_span, he]
    exact bot_unique (conjugateSpanBy_le bot_le (by
      change M ≤ normalizer (⊥ : Subgroup G)
      rw [normalizer_eq_top]
      exact le_top))
  obtain ⟨⟨z, hz⟩, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hz
  have hzone : z ≠ 1 := fun he => hzne (Subtype.ext he)
  have hzP : z ∈ P := hEP (hseed hz)
  let zP : P := ⟨z, hzP⟩
  have hzord : orderOf zP = 2 := by
    apply orderOf_eq_prime
    · exact Subtype.ext (((mem_omegaOneCenterAmbient_iff _ z).mp hz.1).2.1)
    · intro he
      exact hzone (congrArg P.subtype he)
  have hzZ : zP ∈ center P := by
    apply mem_center_iff.mpr
    intro p
    exact Subtype.ext ((hPC p.property z hz.1).symm)
  have hchar : centralizer (pCore 2 P : Set P) ≤ pCore 2 P :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hP)
  have hle := elementary_four_le_pCore_of_normalized_of_central_involution
    hchar EP hEPcard hQN zP hzord (hseed hz) hzZ
  intro e he
  exact mem_map_of_mem P.subtype (hle (show (⟨e, hEP he⟩ : P) ∈ EP from he))

/-- A moving residual forces the original fixed plane to be noncentral in
the very same parabolic's two-core. -/
theorem PreparedChosenModule.moving_fixed_four_core_not_centralizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V P : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (hfour : Nat.card (thompsonFixed T V) = 4)
    (hP : P ∈ Chapter1.HOver G (T : Set G))
    (hPC : P ≤ centralizer (centralInvolutions T : Set G))
    (hpar : ChapterB.IsMinimalParabolicOver T P) (hPM : ¬ P ≤ M)
    (hmove : ¬ (pResidual 2 P).map P.subtype ≤ centralizer (thompsonFixed T V : Set G)) :
    ¬ P.pCoreIn 2 ≤ centralizer (thompsonFixed T V : Set G) := by
  let := h.elementary
  have hEQ := h.thompsonFixed_four_le_core hG T hM hfour hP hPC
  have hω := source_outside_minimalParabolic_residual_centralizes_core_omega
    hG T hempty hM hJ hP hpar hPM
  intro hc
  apply hmove
  rintro r ⟨r, hr, rfl⟩ e he
  have heP : e ∈ P := pCoreIn_le 2 P (hEQ he)
  have heQ : (⟨e, heP⟩ : P) ∈ pCore 2 P := by
    obtain ⟨q, hq, hqe⟩ := hEQ he
    exact (show q = ⟨e, heP⟩ from Subtype.ext hqe) ▸ hq
  have heω : (⟨e, heP⟩ : P) ∈ omegaCenterIn (pCore 2 P) := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨heQ, ?_, ?_⟩
    · intro q hq
      exact Subtype.ext ((hc (mem_map_of_mem P.subtype hq) e he).symm)
    · exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian e he.1)
  exact congrArg P.subtype (hω hr _ heω)

end CFSG.Quasithin.Chapter15.Section01
