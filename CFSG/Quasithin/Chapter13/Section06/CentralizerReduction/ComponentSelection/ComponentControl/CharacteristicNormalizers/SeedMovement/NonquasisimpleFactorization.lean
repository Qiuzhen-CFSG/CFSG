module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.CharacteristicNormalizers.SeedMovement.NonquasisimpleFactorization.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.CharacteristicNormalizers.SeedMovement.NonquasisimpleFactorization.Classification
public import Theory.GroupTheory.CComponent.NonquasisimpleAction

/-!
# Thompson factorization for a nonquasisimple component action

Let H be a finite SQTK-group, P a Sylow two-subgroup, K a normal C-component
with KP = H, and W a normal elementary abelian two-subgroup. In the literal
conjugation quotient A = H/C_H(W), assume O₂(A) = 1 and the image of K is not
quasisimple. Then J(P) centralizes W and H = N_H(J(P)) C_H(W).

The full offender subgroup of A is normal and inherits every B.5.3
hypothesis from the actual action and the inverse-image SQTK cover. The
complete B.5.6 alternatives either supply an ordinary component, or give
the trivial group, S₃, or S₃×S₃. C-component minimality excludes ordinary
components, and the two small solvable cases vanish by their characteristic
cubic subgroups and the two-group quotient over the perfect image of K.
B.2.5 then kills the actual Thompson image; B.2.7's Frattini argument gives
the required factorization.

The complete universal B.5.1/B.5.6 implication remains an explicit input,
as authorized by this earlier-source conditional task. Its separately named
projective-line contract corrects the known triple-six offender convention.
No classification of the image of K, factorization, Thompson centralization,
or later Chapter 13 replacement-control result is assumed. The parent
SeedMovement task retains the application to H = K₀ C_T(v) and
W = ⟨z^H⟩ in 13.6.16(2).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.3 (pp.42–43), B.2.5–7 (pp.76–77), B.5.3–6 (pp.104–105),
and the application in 13.6.16(2), printed p.930.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.NonquasisimpleFactorization
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives Theory.GroupTheory.NonquasisimpleAction
universe u v

/-- The complete alternatives force the full offender actor to vanish.
The normal component image can be trivial; that case is retained literally. -/
theorem offender_eq_bot {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal] [Group.IsPerfect K]
    (hK : K = ⊥ ∨ K.IsCComponent) (hq : IsPGroup 2 (D ⧸ K))
    (hcore : pCore 2 D = ⊥) (hnq : ¬ IsQuasisimple K)
    (hclass : ProjectiveLine.SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype)) :
    offenderSubgroup ρ = ⊥ := by
  let J := offenderSubgroup ρ
  let : J.Normal := offenderSubgroup_normal ρ
  rcases source_group_cases (ρ.comp J.subtype) hclass with ht | ⟨L, hL⟩ | hs | hp
  · let := ht
    exact J.eq_bot_iff_forall.mpr (fun x hx => congrArg Subtype.val
      (Subsingleton.elim (⟨x, hx⟩ : J) 1))
  · have hc : IsComponent D (L.map J.subtype) := by
      let := hL.2
      exact ⟨hL.1.trans' (inferInstance : J.Normal).isSubnormal,
        IsQuasisimple.of_mulEquiv (L.equivMapOfInjective J.subtype J.subtype_injective)⟩
    exact (no_ordinary_components K hK hq hnq _ hc).elim
  · exact hs.elim (normal_symmetricThree_eq_bot K J hq hcore)
  · exact hp.elim (normal_symmetricThreePair_eq_bot K J hq hcore)

variable {H : Type u} [Group H] [Finite H]

/-- Intrinsic nonquasisimple branch: the actual Sylow Thompson subgroup
centralizes W. The only earlier-source input is the complete universal
B.5.1/B.5.6 contract, with its corrected projective-line convention. -/
theorem thompson_centralizes {𝒦 : GroupClass.{u}}
    (classification : ProjectiveLine.CompleteClassificationInput.{u,u} 𝒦)
    (hH : IsSQTK 𝒦 H) (P : Sylow 2 H) (K W : Subgroup H)
    [K.Normal] [W.Normal] [IsElementaryAbelian 2 W]
    (hK : K.IsCComponent) (hKP : K ⊔ (P : Subgroup H) = ⊤)
    (hcore : pCore 2 (ActionQuotient W) = ⊥)
    (hnq : ¬ IsQuasisimple (K.map (actionMk W))) :
    elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H) := by
  let q := actionMk W
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let B := K.map q
  let : B.Normal := (inferInstance : K.Normal).map q hq
  let := hK.perfect
  let : Group.IsPerfect B := Group.IsPerfect.map q
  have hjoin : B ⊔ (P : Subgroup H).map q = ⊤ := by
    rw [← Subgroup.map_sup, hKP, map_top_of_surjective _ hq]
  have hquot : IsPGroup 2 (ActionQuotient W ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B _ (P.isPGroup'.map q) hjoin
  have hh := offender_hypothesis (action W) q hq hH (action_faithful W) hcore
  have hz := offender_eq_bot (action W) B (ccomponent_image_or_bot hK q hq)
    hquot hcore hnq (classification.general _ _ _ hh)
  have hj : (elementaryAbelianMaxJ (P : Subgroup H)).map q = ⊥ :=
    eq_bot_iff.mpr (hz ▸ thompson_image_le P W)
  simpa only [q, actionMk, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hj

/-- The intrinsic factorization needed by the nonquasisimple seed-action
branch of 13.6.16(2), including its Thompson-centralization conclusion. -/
theorem thompson_factorization {𝒦 : GroupClass.{u}}
    (classification : ProjectiveLine.CompleteClassificationInput.{u,u} 𝒦)
    (hH : IsSQTK 𝒦 H) (P : Sylow 2 H) (K W : Subgroup H)
    [K.Normal] [W.Normal] [IsElementaryAbelian 2 W]
    (hK : K.IsCComponent) (hKP : K ⊔ (P : Subgroup H) = ⊤)
    (hcore : pCore 2 (ActionQuotient W) = ⊥)
    (hnq : ¬ IsQuasisimple (K.map (actionMk W))) :
    elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H) ∧
      normalizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H) ⊔
        centralizer (W : Set H) = ⊤ := by
  have hc := thompson_centralizes classification hH P K W hK hKP hcore hnq
  exact ⟨hc, thompson_frattini P W hc⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.NonquasisimpleFactorization
