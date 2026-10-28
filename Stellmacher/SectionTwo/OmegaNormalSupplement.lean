module

public import Stellmacher.SectionTwo.OmegaCoreSetup
public import Stellmacher.SectionTwo.OmegaCoreCommutator
public import Theory.GroupTheory.Commutator.NormalizesSupplement

/-!
# The normal omega supplement in Stellmacher (2.3)

Under the Section Two hypotheses, the core-centralizer equality and the
noncentralizing case, let E be the normal closure of J(S), Z = Ω₁Z(J(S)),
and W = ZV(S). Then W is elementary abelian, lies in E and is normalized
by E. Its commutator with E lies in V(S), and C_W(J(S)) is exactly Z.

The concrete omega-core configuration contains W in the elementary subgroup
Ω₁Z(J(O₂(E))). Maximal replacement control and the normal-closure commutator
transfer give its commutator bound. The normalization lemma then makes W
normal inside E. Finally W lies in S, so its elementary subgroup centralizing
J(S) lies in Z by the maximal-elementary fixed-center theorem.

This is the normal abelian module used for the two-conjugate construction in
the noncentralizing proof of (2.3), Stellmacher, Journal of Algebra 190 (1997),
p. 20. It is independent of the eventual factor-based conjugate choice.
-/

namespace Stellmacher.SectionTwo

private theorem elementary_of_le
    {G : Type*} [Group G] {A B : Subgroup G} [IsElementaryAbelian 2 B]
    (hAB : A ≤ B) : IsElementaryAbelian 2 A where
  toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
    (setLike_mul_comm (hAB a.property) (hAB b.property))⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro a
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ (hAB a.property))

/-- The abelian normal omega supplement and its exact Thompson fixed subgroup in (2.3). -/
public theorem two_three_omega_normal_supplement
    {G : Type*} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    (hcore : pCore 2 G = (S : Subgroup G) ⊓ Subgroup.centralizer (vSubgroup S : Set G))
    (hnot : ¬ vSubgroup S ≤ Subgroup.centralizer
      (elementaryAbelianMaxJ (S : Subgroup G) : Set G)) :
    let E := Subgroup.normalClosure (elementaryAbelianMaxJ (S : Subgroup G) : Set G)
    let Z := omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G))
    let W := Z ⊔ vSubgroup S
    IsElementaryAbelian 2 W ∧ W ≤ E ∧
      E ≤ Subgroup.normalizer (W : Set G) ∧ ⁅W, E⁆ ≤ vSubgroup S ∧
      W ⊓ Subgroup.centralizer (elementaryAbelianMaxJ (S : Subgroup G) : Set G) = Z := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  let E := Subgroup.normalClosure (J : Set G)
  let Q := twoCoreAmbient E
  let V := vSubgroup S
  let Z := omegaOneCenterAmbient J
  let Z0 := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
  let W := Z ⊔ V
  obtain ⟨hZ0N, hZZ0, hVZ0, hcontrol⟩ := two_three_omega_core_setup h S hcore hnot
  let _ : Z0.Normal := hZ0N
  let _ : V.Normal := Subgroup.normalClosure_normal
  let _ : IsElementaryAbelian 2 Z0 := omegaOneCenterAmbient_elementaryAbelian _
  have hWZ0 : W ≤ Z0 := sup_le hZZ0 hVZ0
  have hWe : IsElementaryAbelian 2 W := elementary_of_le hWZ0
  let _ : IsElementaryAbelian 2 W := hWe
  have hJQS : elementaryAbelianMaxJ Q ≤ Q := sSup_le fun _ hA ↦ hA.1
  have hZ0E : Z0 ≤ E := (Subgroup.map_subtype_le _).trans
    (hJQS.trans (Subgroup.map_subtype_le _))
  have hcomm : ⁅Z0, E⁆ ≤ V :=
    omega_core_normalClosure_commutator_le (S : Subgroup G) Z0 V hcontrol
  have hWS : W ≤ (S : Subgroup G) := by
    apply sup_le
    · exact (Subgroup.map_subtype_le _).trans (sSup_le fun _ hA ↦ hA.1)
    · exact (vSubgroup_le_twoCore_and_elementaryAbelian h S).1.trans
        (fitting_pCore_le_sylow S)
  refine ⟨hWe, hWZ0.trans hZ0E,
    Subgroup.le_normalizer_sup_of_commutator_le Z0 E Z V hZZ0 hcomm,
    (Subgroup.commutator_mono hWZ0 le_rfl).trans hcomm, ?_⟩
  let C := W ⊓ Subgroup.centralizer (J : Set G)
  let _ : IsElementaryAbelian 2 C := elementary_of_le (show C ≤ W from inf_le_left)
  apply le_antisymm
  · exact elementary_centralizer_maxJ_le_omegaCenter (S : Subgroup G) C
      (inf_le_left.trans hWS) inf_le_right
  · refine le_inf le_sup_left ?_
    intro z hz
    exact Subgroup.mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff J z).mp hz).2.2

end Stellmacher.SectionTwo
