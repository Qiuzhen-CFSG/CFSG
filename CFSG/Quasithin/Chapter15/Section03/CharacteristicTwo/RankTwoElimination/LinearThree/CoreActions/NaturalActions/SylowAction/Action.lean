module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.Residual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Frattini
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The actual normalizer action on the marked component quotient

Conjugation by N_G(L) descends through the characteristic two-core and is
transported along the given isomorphism L/O₂(L) ≃ SL₃(2). Elements of L act
by the corresponding inner automorphisms. The literal sectionCentralizer
convention is recovered from quotient displacements, and normalized subgroups
have invariant quotient images.

Source: Aschbacher–Smith, proof of 15.3.23, printed p.1129.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction
variable {G : Type*} [Group G]

/-- The quotient map followed by the chosen actual matrix-group marking. -/
noncomputable def quotientMap (L : Subgroup G) (e : (L ⧸ pCore 2 L) ≃* SL) : L →* SL :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

/-- Conjugation by the normalizer on the marked characteristic quotient. -/
noncomputable def action (L : Subgroup G) (e : (L ⧸ pCore 2 L) ≃* SL) :
    normalizer (L : Set G) →* MulAut SL :=
  (MulAut.congr e).toMonoidHom.comp ((quotientAut (pCore 2 L)).comp L.normalizerMonoidHom)

/-- Equivariance of the quotient map for the actual ambient conjugation. -/
theorem action_apply (L : Subgroup G) (e : (L ⧸ pCore 2 L) ≃* SL)
    (n : normalizer (L : Set G)) (l : L) :
    action L e n (quotientMap L e l) = quotientMap L e (L.normalizerMonoidHom n l) := by
  change e ((quotientAut (pCore 2 L) (L.normalizerMonoidHom n))
    (e.symm (e (QuotientGroup.mk' (pCore 2 L) l)))) = _
  rw [e.symm_apply_apply, quotientAut_apply_mk]
  rfl

/-- Every matrix-group element has a lift in L. -/
theorem quotientMap_surjective (L : Subgroup G) (e : (L ⧸ pCore 2 L) ≃* SL) :
    Function.Surjective (quotientMap L e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

/-- A lift in L induces conjugation by its quotient image. -/
theorem action_inner (L : Subgroup G) (e : (L ⧸ pCore 2 L) ≃* SL) (l : L) :
    action L e ⟨l, L.le_normalizer l.property⟩ = MulAut.conj (quotientMap L e l) := by
  apply MulEquiv.ext
  intro z
  obtain ⟨k, rfl⟩ := quotientMap_surjective L e z
  rw [action_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

/-- Actual centralization of L kills its quotient action. -/
theorem action_centralizer (L : Subgroup G) (e : (L ⧸ pCore 2 L) ≃* SL)
    (n : normalizer (L : Set G)) (hn : (n : G) ∈ centralizer (L : Set G)) :
    action L e n = 1 := by
  apply MulEquiv.ext
  intro z
  obtain ⟨l, rfl⟩ := quotientMap_surjective L e z
  rw [action_apply]
  change quotientMap L e (L.normalizerMonoidHom n l) = quotientMap L e l
  congr 1
  apply Subtype.ext
  change (n : G) * (l : G) * (n : G)⁻¹ = l
  rw [← hn l l.property, mul_inv_cancel_right]

/-- Trivial quotient action gives the literal commutator-preimage kernel. -/
theorem le_sectionCentralizer_of_action (L D : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL) (hn : D ≤ normalizer (L : Set G))
    (h : ∀ x : D, action L e ⟨x, hn x.property⟩ = 1) :
    D ≤ Chapter4.sectionCentralizer L := by
  apply (Chapter4.le_sectionCentralizer_iff D L).mpr
  refine ⟨hn, commutator_le.mpr ?_⟩
  intro x hx l hl
  let n : normalizer (L : Set G) := ⟨x, hn hx⟩
  have he := DFunLike.congr_fun (h ⟨x,hx⟩) (quotientMap L e ⟨l,hl⟩)
  rw [action_apply] at he
  have heq : (QuotientGroup.mk' (pCore 2 L)) (L.normalizerMonoidHom n ⟨l,hl⟩) =
      QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩ := e.injective he
  have hm := QuotientGroup.eq_iff_div_mem.mp heq
  have hm' := mem_map_of_mem L.subtype hm
  simpa only [div_eq_mul_inv, map_mul, map_inv, subtype_apply,
    normalizerMonoidHom_apply_apply_coe, commutatorElement_def, pCoreIn, n] using hm'

/-- An ambient normalizer of A preserves the quotient image of A ∩ L. -/
theorem action_preserves_image (L A : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL) (n : normalizer (L : Set G))
    (hn : (n : G) ∈ normalizer (A : Set G)) :
    ((A.subgroupOf L).map (quotientMap L e)).map (action L e n).toMonoidHom =
      (A.subgroupOf L).map (quotientMap L e) := by
  have hm (u : normalizer (L : Set G)) (hu : (u : G) ∈ normalizer (A : Set G)) :
      ((A.subgroupOf L).map (quotientMap L e)).map (action L e u).toMonoidHom ≤
        (A.subgroupOf L).map (quotientMap L e) := by
    rintro _ ⟨_, ⟨a,ha,rfl⟩, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, action_apply]
    refine mem_map_of_mem _ ?_
    change ↑(L.normalizerMonoidHom u a) ∈ A
    rw [normalizerMonoidHom_apply_apply_coe]
    exact (hu a).mp ha
  apply le_antisymm (hm n hn)
  intro z hz
  have hi := hm n⁻¹ ((normalizer (A : Set G)).inv_mem hn)
    (mem_map_of_mem (action L e n⁻¹).toMonoidHom hz)
  refine ⟨action L e n⁻¹ z, hi, ?_⟩
  simp only [map_inv, MulEquiv.coe_toMonoidHom, MulAut.inv_apply, MulEquiv.apply_symm_apply]
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction
