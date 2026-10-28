module
public import Stellmacher.SectionTwo.NativeBaumannActionFactors
public import Stellmacher.SectionOne.OneSevenOddFixedIntersection

/-!
# An odd fixed space meets the native Baumann fixed space

Under Section Two, suppose the native elementary Thompson image is nontrivial.
Any nontrivial fixed subgroup of a subgroup of the quotient odd core meets the
Baumann-image fixed subgroup nontrivially, on the original native module with
its exact quotient-conjugation action.

The actual native Baumann normal closure has the one-seven factors from (2.2).
The Baumann image is a two-group inside that closure and normalizes every
factor. The odd fixed-intersection theorem applies to this finite family.
No normality of the chosen odd subgroup or its fixed space is assumed.

This is the native action step in Stellmacher (9.1), Journal of Algebra 190
(1997), p.47, applying (2.2). The actual graph module comparison is separate.
-/

namespace Stellmacher.SectionTwo
universe u
public theorem native_baumann_odd_fixed_inf_ne_bot
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    {X : Type u} [Group X] [Finite X]
    (q : G →* X) (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (B : Subgroup G)
    (hB : B = (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G))
    (hJne : (elementaryAbelianMaxJ (S : Subgroup G)).map q ≠ ⊥)
    (F : Subgroup X) (hF : F ≤ SectionOne.oddCore X) :
    letI := quotientConjugationAction S q hq hker
    FixedPoints.subgroup F (vSubgroup S) ≠ ⊥ →
      FixedPoints.subgroup F (vSubgroup S) ⊓
        FixedPoints.subgroup (B.map q) (vSubgroup S) ≠ ⊥ := by
  let _ := quotientConjugationAction S q hq hker
  let _ : IsElementaryAbelian 2 (vSubgroup S) :=
    (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  intro hfix
  obtain ⟨_,n,D,hgen,_,_,hD,hDN,_⟩ := nativeBaumann_action_factors h S q hq hker B hB hJne
  let E := Subgroup.normalClosure (B.map q : Set X)
  have hBE : B.map q ≤ E := Subgroup.le_normalClosure
  have hBp : IsPGroup 2 (B.map q) :=
    (S.isPGroup'.to_le (by rw [hB]; exact inf_le_left)).map q
  have hBD : ∀ i, B.map q ≤ Subgroup.normalizer (D i : Set X) := by
    intro i
    have hDE : D i ≤ E := by change D i ≤ Subgroup.normalClosure (B.map q : Set X); rw [hgen]; exact le_iSup D i
    exact hBE.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hDE).mp (hDN i))
  exact SectionOne.oneSeven_odd_fixed_inf_two_fixed_ne_bot D hD E (B.map q) F
    hgen hBE hBp hBD hF hfix
end Stellmacher.SectionTwo
