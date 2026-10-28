module

public import Theory.GroupTheory.RankTwoInnerCubicAction
public import Theory.GroupTheory.PResidual.PrimeSection
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.LocalCubic
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.ActionKernel
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.ContainedAction

/-!
# Nontrivial local action on the supercritical Frattini plane

For either local group M of a Goldschmidt triple, its two-residual R has
R/O₂(R) of order three. An actual order-three complement generates R with
O₂(R). If that complement lay in the embedded normal supercritical subgroup,
two-perfectness would force all of R into it. Thus noncontainment gives an
outside cubic element, whose Frattini action is nontrivial by the rank-two
inner-action obstruction.

The action is the literal composite of conjugation on O₃(G), characteristic
restriction to X, passage to X/Φ(X), and the chosen injective matrix map.
Both local noncontainments therefore discharge the image hypotheses of
ActionKernel. The final corollary combines the contained and noncontained
cases, retaining the earlier F.6.13 rigidity input with its source owner.
No full F.6.16 classification or rigidity input is asserted here.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
F.6.16, printed p.308, especially lines 15774–15778 of the searchable
combined manuscript of 1 March 2004.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Noncyclic
universe u
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The cubic complement cannot lie in a normal subgroup omitting the
local residual: adjoining its two-core cannot contain a two-perfect group. -/
private theorem local_residual_outside_cubic (M N : Subgroup G) [N.Normal]
    (he : Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ (pResidual 2 M).map M.subtype ≤ N) :
    ∃ d : G, d ∈ (pResidual 2 M).map M.subtype ∧ orderOf d = 3 ∧ d ∉ N := by
  let R := pResidual 2 M
  let ι := M.subtype.comp R.subtype
  let K := (pCore 2 R).map ι
  obtain ⟨x, hx, hgen⟩ := exists_prime_order_sup_pCore_eq_top (G := R)
    (by decide : Nat.Coprime 2 3) (local_residual_quotient_card_three he)
  have hi : Function.Injective ι := M.subtype_injective.comp R.subtype_injective
  have hd : orderOf (ι x) = 3 := (orderOf_injective ι hi x).trans hx
  have hgen' : zpowers (ι x) ⊔ K = R.map M.subtype := by
    have hm := congrArg (fun A : Subgroup R => A.map ι) hgen
    simpa only [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      ι, MonoidHom.range_comp, range_subtype] using hm
  refine ⟨ι x, mem_map_of_mem M.subtype x.property, hd, ?_⟩
  intro hm
  apply hout
  apply le_normal_of_isPPerfect_of_le_sup_pGroup _ N K
    (isPPerfect_embedded_pResidual 2 M) (pCore_isPGroup.map ι)
  rw [← hgen']
  exact sup_le_sup (zpowers_le.mpr hm) le_rfl

/-- A local symmetric-three quotient and noncontainment force a nontrivial
image under every injective matrix realization of the actual Frattini action. -/
theorem supercritical_local_image_ne_bot
    (hr : primeRank 3 G ≤ 2) (M : Subgroup G)
    (he : Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 3)))
    (X : Subgroup (pCore 3 G)) (hX : IsSupercriticalPSubgroup 3 X)
    (hm : Nonempty (X ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
      Nonempty (X ≃* HeisenbergPrime 3))
    (hout : ¬ (pResidual 2 M).map M.subtype ≤ X.map (pCore 3 G).subtype) :
    letI : X.Characteristic := hX.characteristic
    ∀ j : MulAut (X ⧸ frattini X) →*
        Matrix.GeneralLinearGroup (Fin 2) (ZMod 3), Function.Injective j →
      let f := j.comp ((quotientAut (frattini X)).comp
        ((MulAut.characteristic X).comp (MulAut.conjNormal : G →* MulAut (pCore 3 G))))
      ((pResidual 2 M).map M.subtype).map f ≠ ⊥ := by
  let : X.Characteristic := hX.characteristic
  intro j hj
  let a : G →* MulAut X := (MulAut.characteristic X).comp
    (MulAut.conjNormal : G →* MulAut (pCore 3 G))
  let f := j.comp ((quotientAut (frattini X)).comp a)
  change ((pResidual 2 M).map M.subtype).map f ≠ ⊥
  intro hzero
  let ι : X →* G := (pCore 3 G).subtype.comp X.subtype
  have hi : Function.Injective ι := (pCore 3 G).subtype_injective.comp X.subtype_injective
  have hι : ι.range = X.map (pCore 3 G).subtype := by
    rw [MonoidHom.range_comp, range_subtype]
  obtain ⟨d, hdM, hd, hdout⟩ := local_residual_outside_cubic M
    (X.map (pCore 3 G).subtype) he hout
  have hf : f d = 1 := mem_bot.mp (hzero ▸ mem_map_of_mem f hdM)
  have hq : quotientAut (frattini X) (a d) = 1 := hj (hf.trans (map_one j).symm)
  apply RankTwoInnerCubicAction.frattini_action_ne_one ι hi hr hm d hd
    (by simpa only [hι] using hdout) (a d) _ hq
  intro y
  exact MulAut.conjNormal_apply d (y : pCore 3 G)

/-- Both Goldschmidt local residuals have nontrivial Frattini images.
The model alternatives match `exists_three_core_supercritical` literally. -/
theorem supercritical_local_residual_images_ne_bot
    (h : IsGoldschmidtTriple G₁ G₂) (hr : primeRank 3 G ≤ 2)
    (X : Subgroup (pCore 3 G)) (hX : IsSupercriticalPSubgroup 3 X)
    (hm : (Nat.card X = 9 ∧ Nonempty (X ≃*
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))) ∨
      (Nat.card X = 27 ∧ IsExtraspecial 3 X ∧ Nonempty (X ≃* HeisenbergPrime 3)))
    (h₁ : ¬ (pResidual 2 G₁).map G₁.subtype ≤ X.map (pCore 3 G).subtype)
    (h₂ : ¬ (pResidual 2 G₂).map G₂.subtype ≤ X.map (pCore 3 G).subtype) :
    letI : X.Characteristic := hX.characteristic
    ∀ j : MulAut (X ⧸ frattini X) →*
        Matrix.GeneralLinearGroup (Fin 2) (ZMod 3), Function.Injective j →
      let f := j.comp ((quotientAut (frattini X)).comp
        ((MulAut.characteristic X).comp (MulAut.conjNormal : G →* MulAut (pCore 3 G))))
      ((pResidual 2 G₁).map G₁.subtype).map f ≠ ⊥ ∧
      ((pResidual 2 G₂).map G₂.subtype).map f ≠ ⊥ := by
  have hmodel := hm.imp And.right (fun hh => hh.2.2)
  let : X.Characteristic := hX.characteristic
  intro j hj
  exact ⟨supercritical_local_image_ne_bot hr G₁ h.quotient_left X hX hmodel h₁ j hj,
    supercritical_local_image_ne_bot hr G₂ h.quotient_right X hX hmodel h₂ j hj⟩

/-- Apply the two nontrivial local images to the actual action-kernel theorem. -/
theorem residual_isThreeGroup_of_supercritical_noncontainments
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hprime : pPrimeCore 3 G = ⊥) (hr : primeRank 3 G ≤ 2)
    (X : Subgroup (pCore 3 G)) (hX : IsSupercriticalPSubgroup 3 X)
    (hm : (Nat.card X = 9 ∧ Nonempty (X ≃*
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))) ∨
      (Nat.card X = 27 ∧ IsExtraspecial 3 X ∧ Nonempty (X ≃* HeisenbergPrime 3)))
    (h₁ : ¬ (pResidual 2 G₁).map G₁.subtype ≤ X.map (pCore 3 G).subtype)
    (h₂ : ¬ (pResidual 2 G₂).map G₂.subtype ≤ X.map (pCore 3 G).subtype) :
    IsPGroup 3 (pResidual 2 G) := by
  exact residual_isThreeGroup_of_supercritical_images h hcore hprime hr X hX
    (supercritical_local_residual_images_ne_bot h hr X hX hm h₁ h₂)

/-- Close the supercritical branch using the proved contained-local reduction.
The full earlier F.6.13 premise remains explicit for source assembly. -/
theorem residual_isThreeGroup_of_supercritical_models
    (source : GoldschmidtRigidityInput.{u})
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hprime : pPrimeCore 3 G = ⊥) (hr : primeRank 3 G ≤ 2)
    (X : Subgroup (pCore 3 G)) (hX : IsSupercriticalPSubgroup 3 X)
    (hm : (Nat.card X = 9 ∧ Nonempty (X ≃*
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))) ∨
      (Nat.card X = 27 ∧ IsExtraspecial 3 X ∧ Nonempty (X ≃* HeisenbergPrime 3))) :
    IsPGroup 3 (pResidual 2 G) := by
  by_contra hnot
  obtain ⟨h₁, h₂⟩ := neither_local_residual_le_supercritical source h hcore hr X hX hnot
  exact hnot (residual_isThreeGroup_of_supercritical_noncontainments h hcore hprime hr
    X hX hm h₁ h₂)
end CFSG.Quasithin.ChapterF.Noncyclic
