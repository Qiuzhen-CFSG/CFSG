module

public import Stellmacher.SectionTwo.QuotientHypotheses
public import Stellmacher.SectionOne.LemmaOneFiveRelativeM
public import Stellmacher.MaxElementaryOffender

/-!
# Maximal elementary replacement in Stellmacher (2.3)

When V does not centralize J(S), every maximum-order elementary abelian
subgroup A of S can be replaced by V C_A(V), again of maximum order in S.
The noncentralizing hypothesis makes the image of J(S) in G/C_G(V)
nontrivial. The named faithful quotient action therefore satisfies the
Section 1 hypotheses. The relative lower bound (1.5)(e), applied to the
image of A, gives |C_V(A)| |q(A)| ≤ |V|.

The replacement is elementary abelian inside S. Relative-index and
kernel-image counting, using V∩C_A(V)≤C_V(A), show that its order is at
least |A|. Maximality of A then gives maximality of the replacement.
The proof does not require Lemma (2.2), nor the extra core-centralizer
hypothesis of the final (2.3) statement.

Source: refs/latex/stellmacher-n-group.tex, proof of (2.3), journal page 20,
the assertion C_A(V)V belongs to A(S) by (1.5)(e).
-/

namespace Stellmacher.SectionTwo
universe u

private theorem replacement_reverse_card_bound
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    (hnot : ¬ vSubgroup S ≤ Subgroup.centralizer (elementaryAbelianMaxJ (S : Subgroup G) : Set G))
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G)) :
    let C := cSubgroup S
    letI : C.Normal := by
      let : (vSubgroup S).Normal := Subgroup.normalClosure_normal
      exact Subgroup.normal_centralizer
    Nat.card (↥(vSubgroup S ⊓ Subgroup.centralizer (A : Set G))) *
      Nat.card (A.map (QuotientGroup.mk' C)) ≤ Nat.card (vSubgroup S) := by
  let V := vSubgroup S
  let C := cSubgroup S
  let _ : V.Normal := Subgroup.normalClosure_normal
  let _ : C.Normal := Subgroup.normal_centralizer
  let q : G →* G ⧸ C := QuotientGroup.mk' C
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective C
  have hker : q.ker = cSubgroup S := QuotientGroup.ker_mk' C
  have hJne : (elementaryAbelianMaxJ (S : Subgroup G)).map q ≠ ⊥ := by
    intro hbot
    have hJC : elementaryAbelianMaxJ (S : Subgroup G) ≤ q.ker :=
      (Subgroup.map_eq_bot_iff (f := q) _).mp hbot
    rw [hker] at hJC
    exact hnot (Subgroup.le_centralizer_iff.mpr hJC)
  let _ : IsElementaryAbelian 2 V := (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  let _ := quotientConjugationAction S q hq hker
  have hbar := quotientConjugationAction_hypotheses h S q hq hker hJne
  let T : Sylow 2 (G ⧸ C) := S.mapSurjective hq
  have hAT : A.map q ≤ (T : Subgroup (G ⧸ C)) := Subgroup.map_mono hA.1
  have hm := SectionOne.lemma_one_five_m_ge_one_relative hbar T (A.map q) hAT (hA.2.1.map q)
  have hpos : (0 : ℚ) < (Nat.card (FixedPoints.subgroup (A.map q) V) : ℚ) * Nat.card (A.map q) := by
    exact_mod_cast Nat.mul_pos Nat.card_pos Nat.card_pos
  have hbound : (Nat.card (FixedPoints.subgroup (A.map q) V) : ℚ) * Nat.card (A.map q) ≤
      (Nat.card V : ℚ) := by
    have hb := (le_div_iff₀ hpos).mp hm
    simpa only [one_mul] using hb
  rw [quotientConjugationAction_fixedPoints_card S q hq hker A] at hbound
  exact_mod_cast hbound

public theorem maxElementary_centralizer_replacement
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    (hnot : ¬ vSubgroup S ≤ Subgroup.centralizer (elementaryAbelianMaxJ (S : Subgroup G) : Set G))
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G)) :
    vSubgroup S ⊔ (A ⊓ Subgroup.centralizer (vSubgroup S : Set G)) ∈
      elementaryAbelianMaxSubgroups (S : Subgroup G) := by
  let V := vSubgroup S
  let K := cSubgroup S
  let C := A ⊓ Subgroup.centralizer (V : Set G)
  let I := V ⊓ C
  let _ : V.Normal := Subgroup.normalClosure_normal
  let _ : K.Normal := Subgroup.normal_centralizer
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  have hker : q.ker = Subgroup.centralizer (V : Set G) := QuotientGroup.ker_mk' K
  obtain ⟨hVcore, hVelem⟩ := vSubgroup_le_twoCore_and_elementaryAbelian h S
  let _ : IsElementaryAbelian 2 V := hVelem
  let _ : IsElementaryAbelian 2 A := hA.2.1
  have hAA : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  let _ : IsElementaryAbelian 2 C := {
    toIsMulCommutative := Subgroup.le_centralizer_iff_isMulCommutative.mp
      ((inf_le_left.trans hAA).trans (Subgroup.centralizer_le inf_le_left))
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro c
      exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (A := A) (c : G) c.property.1) }
  have hVS : V ≤ (S : Subgroup G) := hVcore.trans (fitting_pCore_le_sylow S)
  have hRS : V ⊔ C ≤ (S : Subgroup G) := sup_le hVS (inf_le_left.trans hA.1)
  have hRelem : IsElementaryAbelian 2 (↥(V ⊔ C)) :=
    IsElementaryAbelian.sup_of_le_centralizer inf_le_right
  have hcount (H L : Subgroup G) : Nat.card (↥(H ⊓ L)) * H.relIndex L = Nat.card L := by
    simpa only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right] using
      Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (H ⊓ L) L bot_le inf_le_right
  have hprod : Nat.card V * V.relIndex C = Nat.card (↥(V ⊔ C)) := by
    simpa only [inf_sup_self, Subgroup.relIndex_sup_left] using hcount V (V ⊔ C)
  have hCcard : Nat.card I * V.relIndex C = Nat.card C := hcount V C
  have hAcard : Nat.card C * Nat.card (A.map q) = Nat.card A := by
    have hc := hcount q.ker A
    rw [Subgroup.relIndex_ker] at hc
    simpa only [hker, inf_comm, C] using hc
  have hIle : I ≤ V ⊓ Subgroup.centralizer (A : Set G) :=
    le_inf inf_le_left ((inf_le_right.trans inf_le_left).trans hAA)
  have hIcard : Nat.card I ≤ Nat.card (↥(V ⊓ Subgroup.centralizer (A : Set G))) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hIle)
  have hbound := replacement_reverse_card_bound h S hnot A hA
  have hIimage : Nat.card I * Nat.card (A.map q) ≤ Nat.card V :=
    (Nat.mul_le_mul_right (Nat.card (A.map q)) hIcard).trans hbound
  have hAr : Nat.card A ≤ Nat.card (↥(V ⊔ C)) := by
    calc
      Nat.card A = (Nat.card I * Nat.card (A.map q)) * V.relIndex C := by
        rw [← hAcard, ← hCcard]
        ac_rfl
      _ ≤ Nat.card V * V.relIndex C := Nat.mul_le_mul_right _ hIimage
      _ = Nat.card (↥(V ⊔ C)) := hprod
  refine ⟨hRS, hRelem, ?_⟩
  intro D hDS hDelem
  exact (hA.2.2 D hDS hDelem).trans hAr

end Stellmacher.SectionTwo

