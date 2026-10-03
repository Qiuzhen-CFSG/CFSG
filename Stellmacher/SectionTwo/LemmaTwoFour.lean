module
public import Stellmacher.PushingUp.SL2Two
public import Stellmacher.SectionTwo.LemmaTwoThree
public import Stellmacher.SectionTwo.TwoFourInitialReduction
public import Stellmacher.SectionTwo.TwoFourCharacteristicTransport
public import Stellmacher.SectionTwo.TwoFourLocalTransport
public import Stellmacher.SectionTwo.TwoFourHallTransfer
public import Stellmacher.SectionTwo.TwoFourLocalFactor

/-!
# Stellmacher (2.4): the two-core residual commutator lies in V

Under the standing Section Two hypotheses, no nontrivial characteristic
subgroup of S is ambient-normal, and the whole group is the unique maximal
overgroup of S. Then [O₂(G),O²(G)] lies in the normal closure V of Ω₁(Z(S)).
Both extra hypotheses remain explicit in the public statement.

The initial reduction identifies the two-core centralizer and supplies the
characteristic Baumann subgroup. Results (2.2) and (2.3) give its normal
closure and local Sylow model. A minimal local SL₂(2) Frattini factor inherits
the characteristic-subgroup obstruction. The proved pushing-up theorem
bounds its local residual commutator, and the local transport puts that bound
in V. Finally the Hall odd-order residual transfer lifts the containment from
the selected factor to the original group.

The local factor retains the exact nested Frattini quotient; no unbarred
SL₂(2) quotient is assumed. Source: `refs/latex/stellmacher-n-group.tex`,
(2.4), and Stellmacher, *Pushing up*, Arch. Math. 46 (1986), Theorems 1--2.
-/

namespace Stellmacher.SectionTwo

universe u

public theorem lemma_two_four
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hcharacteristic :
      ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
        ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hunique :
      IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G)) :
    ⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆ ≤ vSubgroup S := by
  classical
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  let E := Subgroup.normalClosure (J : Set G)
  let V := vSubgroup S
  have hVnormal : V.Normal := by
    dsimp only [V, vSubgroup]
    infer_instance
  let _ : V.Normal := hVnormal
  let B := (S : Subgroup G) ⊓
    Subgroup.centralizer (omegaOneCenterAmbient J : Set G)
  let L := Subgroup.normalClosure (B : Set G)
  obtain ⟨hcore, hnot, BS, hBSchar, _hBSne, hBSmap⟩ :=
    two_four_initial_reduction h S hcharacteristic hunique
  let C₀ := cSubgroup S
  let _ : C₀.Normal := by
    dsimp only [C₀, cSubgroup]
    infer_instance
  let q : G →* G ⧸ C₀ := QuotientGroup.mk' C₀
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective C₀
  have hker : q.ker = cSubgroup S := QuotientGroup.ker_mk' C₀
  have hJne : J.map q ≠ ⊥ := by
    intro hbot
    have hJC : J ≤ Subgroup.centralizer (V : Set G) := by
      change J ≤ cSubgroup S
      rw [← hker]
      exact (Subgroup.map_eq_bot_iff J).mp hbot
    exact hnot (Subgroup.le_centralizer_iff.mp hJC)
  have h22 := lemma_two_two h S q hq hker ((S : Subgroup G).map q)
    (J.map q) (B.map q) rfl B rfl rfl rfl hJne
  have hLsup : L = E ⊔ B :=
    normalClosure_baumann_eq_thompson_sup_of_image_eq
      S B rfl q hker hcore h22.part_b
  obtain ⟨PL, hPLmap⟩ : ∃ PL : Sylow 2 L, PL.map L.subtype = B :=
    lemma_two_three h S hcore B L rfl rfl
  obtain ⟨L₁, P₁, _hBL₁, hL₁L, hP₁map, hA, hgen⟩ :=
    two_four_exists_local_sl2Frattini_factor h S hcore hnot hunique
  have hP₁characteristic := two_four_local_characteristic_not_normal
    S B L₁ P₁ BS hBSchar hBSmap hP₁map hgen hcharacteristic
  have hlocalPush :=
    Stellmacher.PushingUp.sl2Two_localCommutator_le_centerNormalClosureCommutator
      P₁ hP₁characteristic hA
  have hlocal :
      (⁅pCore 2 L₁, twoResidualAmbient (⊤ : Subgroup L₁)⁆).map
          L₁.subtype ≤ V :=
    two_four_local_bound_maps_to_v h S hcore hnot B L L₁ rfl hLsup
      hL₁L P₁ hP₁map hlocalPush
  obtain ⟨_hWelem, hWE, _hEnormW, _hWEcomm, _hfixed⟩ :=
    two_three_omega_normal_supplement h S hcore hnot
  have hVL : V ≤ L := by
    calc
      V ≤ omegaOneCenterAmbient J ⊔ V := le_sup_right
      _ ≤ E := hWE
      _ ≤ E ⊔ B := le_sup_left
      _ = L := hLsup.symm
  have hLnormal : L.Normal := by
    dsimp only [L]
    infer_instance
  have hVelem : IsElementaryAbelian 2 V :=
    (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  exact two_four_hall_residual_transfer h.solvable S V L L₁ B
    hVnormal hLnormal hVelem hVL
    inf_le_left PL hPLmap P₁ hP₁map hL₁L hgen hlocal

end Stellmacher.SectionTwo
