module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.ModelBounds
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport
public import Theory.AtlasPort.LinearGroups.G2.Unipotent
public import Theory.AtlasPort.LinearGroups.G2.FieldTransport
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction

/-!
# Quasisimple FF models under the Goldschmidt Sylow bound

An injected group's defining two-power divides an ambient Sylow order.
The bound 128 therefore gives degree at most seven for SL₂ and at most two
for SL₃. The actual unipotent subgroups leave only the binary field for
Sp₄ and G₂, whose full binary groups are not perfect. The order formula
excludes SL₅(2), since 1024 divides its order. These deductions preserve
actual model equivalences, including the triple-six central quotient and
G₂(2)′, and do not assume a bound on three-rank.

The SL₅ arithmetic simplifies only the field-order formula; unfolding a
finite carrier here is unnecessary and substantially more expensive.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.6(1),
p.105, compared with the Sylow orders in F.6.18, pp.309–310, for 15.4.18,
p.1163. The imported ATLAS model counts retain their original attribution.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives
namespace QuasisimpleComparison
universe u v
variable {D : Type u} [Group D] [Finite D]
variable {A : Type v} [Group A]

/-- A defining two-power divisor remains bounded through an actual embedding. -/
theorem two_power_le (small : ∀ S : Sylow 2 D, Nat.card S ≤ 128)
    (f : A →* D) (hf : Function.Injective f) {k : ℕ}
    (hd : 2 ^ k ∣ Nat.card A) : k ≤ 7 := by
  let S : Sylow 2 D := Classical.choice inferInstance
  have h := S.pow_dvd_card_of_pow_dvd_card (hd.trans (card_dvd_of_injective f hf))
  have hb : 2 ^ k ≤ 2 ^ 7 := (Nat.le_of_dvd (Nat.card_pos (α := S)) h).trans (small S)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb

private noncomputable def fieldTwoEquiv (F : BinaryField) (h : F.degree = 1) :
    F.Carrier ≃+* ZMod 2 := by
  let : Fintype F.Carrier := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, F.card_eq, h]
    simp)

/-- The binary rank-one field degree is bounded by seven. -/
theorem linearTwo_degree_le (small : ∀ S : Sylow 2 D, Nat.card S ≤ 128)
    (F : BinaryField) (f : SL(2,F.Carrier) →* D) (hf : Function.Injective f) :
    F.degree ≤ 7 := by
  apply two_power_le small f hf
  rw [GorensteinWalter.sl2_card_formula, F.card_eq]
  exact dvd_mul_right _ _

/-- The concrete unipotent group bounds degree three without an odd-degree premise. -/
theorem linearThree_degree_le (small : ∀ S : Sylow 2 D, Nat.card S ≤ 128)
    (F : BinaryField) (f : SL(3,F.Carrier) →* D) (hf : Function.Injective f) :
    F.degree ≤ 2 := by
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL, F.card_eq, ← pow_mul] at hd
  have := two_power_le small f hf hd
  omega

/-- Only the binary field can occur for a symplectic four-space embedding. -/
theorem symplectic_degree_eq_one (small : ∀ S : Sylow 2 D, Nat.card S ≤ 128)
    (F : BinaryField) (f : Matrix.symplecticGroup (Fin 2) F.Carrier →* D)
    (hf : Function.Injective f) : F.degree = 1 := by
  have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F.Carrier)).card_subgroup_dvd_card
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent, F.card_eq, ← pow_mul] at hd
  have := two_power_le small f hf hd
  have := F.degree_pos
  omega

/-- Only the binary field can occur for a full G₂ embedding. -/
theorem g2_degree_eq_one (small : ∀ S : Sylow 2 D, Nat.card S ≤ 128)
    (F : BinaryField) (f : Atlas.G2.Model F.Carrier →* D)
    (hf : Function.Injective f) : F.degree = 1 := by
  have hd := (Atlas.G2.unipotent (K := F.Carrier)).card_subgroup_dvd_card
  rw [Atlas.G2.card_unipotent, F.card_eq, ← pow_mul] at hd
  have := two_power_le small f hf hd
  have := F.degree_pos
  omega

/-- The binary SL₅ model already has a two-power divisor 1024. -/
theorem no_linearFive (small : ∀ S : Sylow 2 D, Nat.card S ≤ 128)
    (f : SL(5,ZMod 2) →* D) (hf : Function.Injective f) : False := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
  norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Fin.val_zero, Fin.val_succ, Nat.mul_one] at h
  have hd : 2 ^ 10 ∣ Nat.card PSL(5,ZMod 2) := by rw [h]; norm_num
  have hd' := hd.trans (card_dvd_of_surjective
    (QuotientGroup.mk' (center SL(5,ZMod 2))) (QuotientGroup.mk'_surjective _))
  have := two_power_le small f hf hd'
  omega

private theorem quasisimple_not_solvable (h : IsQuasisimple A) : ¬ Group.IsSolvable A := by
  let : IsQuasisimple A := h
  let : IsSimpleGroup (A ⧸ center A) := h.simple
  let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
  exact Group.IsPerfect.not_isSolvable A

private theorem linearTwo_degree_ge_two (h : IsQuasisimple A)
    (F : BinaryField) (e : A ≃* SL(2,F.Carrier)) : 2 ≤ F.degree := by
  by_contra hn
  have hd : F.degree = 1 := by have := F.degree_pos; omega
  let b := e.trans ((Atlas.fieldEquivSL 2 (fieldTwoEquiv F hd)).trans
    SLTwoPermThree.sl2Two_equiv_perm_three.some)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := Group.isSolvable_of_isSolvable_injective
    (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  exact quasisimple_not_solvable h
    (Group.isSolvable_of_isSolvable_injective (f := b.toMonoidHom) b.injective)

private theorem no_perfect_symmetric [Group.IsPerfect A] {n : ℕ} [Nontrivial (Fin n)]
    (e : A ≃* Equiv.Perm (Fin n)) : False := by
  let : Nontrivial ℤˣ := ⟨⟨1, -1, by decide⟩⟩
  let f := Equiv.Perm.sign.comp e.toMonoidHom
  let : Group.IsPerfect ℤˣ := Group.IsPerfect.ofSurjective
    (f := f) ((Equiv.Perm.sign_surjective (α := Fin n)).comp e.surjective)
  exact Group.IsPerfect.not_isSolvable ℤˣ inferInstance

private theorem no_perfect_g2_binary [Group.IsPerfect A]
    (e : A ≃* Atlas.G2.Model (ZMod 2)) : False := by
  let : Group.IsPerfect (Atlas.G2.Model (ZMod 2)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have h := Atlas.G2.LieAutomorphismExtensions.card_binaryDerived
  rw [Atlas.G2.LieAutomorphismExtensions.BinaryDerived,
    Group.IsPerfect.commutator_eq_top, Subgroup.card_top,
    Atlas.G2.LieAutomorphismExtensions.card_binaryFull] at h
  norm_num at h

/-- The finite-parameter component list obtained from the uniform Sylow bound.
Every alternative retains an actual group equivalence, including the central
quotient and cubic center in the triple-cover case. -/
inductive BoundedQuasisimpleModel (A : Type*) [Group A] : Prop
  | linearTwo (F : BinaryField) (lower : 2 ≤ F.degree) (upper : F.degree ≤ 7)
      (equiv : A ≃* SL(2,F.Carrier))
  | linearThree (F : BinaryField) (upper : F.degree ≤ 2) (equiv : A ≃* SL(3,F.Carrier))
  | alternatingSix (equiv : A ≃* alternatingGroup (Fin 6))
  | alternatingSeven (equiv : A ≃* alternatingGroup (Fin 7))
  | tripleSix (centerEquiv : center A ≃* Multiplicative (ZMod 3))
      (quotientEquiv : (A ⧸ center A) ≃* alternatingGroup (Fin 6))
  | g2DerivedTwo (equiv : A ≃* commutator (Atlas.G2.Model (ZMod 2)))
  | linearFourTwo (equiv : A ≃* SL(4,ZMod 2))

/-- Eliminate large field parameters, full binary Sp₄/G₂, and SL₅.
No three-rank assumption or ambient classification conclusion is used. -/
theorem bounded_quasisimple_model (small : ∀ S : Sylow 2 D, Nat.card S ≤ 128)
    (i : A →* D) (hi : Function.Injective i) (hq : IsQuasisimple A)
    (model : QuasisimpleModel A) : BoundedQuasisimpleModel A := by
  let : IsQuasisimple A := hq
  cases model with
  | linearTwo F e =>
    exact .linearTwo F (linearTwo_degree_ge_two hq F e)
      (linearTwo_degree_le small F (i.comp e.symm.toMonoidHom) (hi.comp e.symm.injective)) e
  | linearThree F e =>
    exact .linearThree F
      (linearThree_degree_le small F (i.comp e.symm.toMonoidHom) (hi.comp e.symm.injective)) e
  | symplecticFour F e =>
    have hd := symplectic_degree_eq_one small F
      (i.comp e.symm.toMonoidHom) (hi.comp e.symm.injective)
    let a := (Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivSp (fieldTwoEquiv F hd)).trans
      Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
    exact (no_perfect_symmetric (e.trans a)).elim
  | g2 F e =>
    have hd := g2_degree_eq_one small F
      (i.comp e.symm.toMonoidHom) (hi.comp e.symm.injective)
    exact (no_perfect_g2_binary (e.trans (Atlas.G2.fieldEquiv (fieldTwoEquiv F hd)))).elim
  | alternatingSix e => exact .alternatingSix e
  | alternatingSeven e => exact .alternatingSeven e
  | tripleSix e a => exact .tripleSix e a
  | g2DerivedTwo e => exact .g2DerivedTwo e
  | linearFourTwo e => exact .linearFourTwo e
  | linearFiveTwo e =>
    exact (no_linearFive small
      (i.comp e.symm.toMonoidHom) (hi.comp e.symm.injective)).elim

end QuasisimpleComparison
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
