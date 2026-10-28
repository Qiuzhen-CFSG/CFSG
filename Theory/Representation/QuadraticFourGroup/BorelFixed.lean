module
public import Theory.Representation.QuadraticFourGroup.TensorOddCommutator
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

public import Theory.Representation.BinaryOffender.IrreducibleSection

/-!
# Sylow normalizers on natural binary tensor sections

A Sylow normalizer maps onto the normalizer in a product of two projective
SL₂ groups. That image contains a nonidentity odd element in the first
factor. In a faithful two-dimensional action of a perfect group this
element has no fixed vector; its tensor action therefore has no fixed
vector either. The map onto the model remains the original quotient map.

The final central-section lemmas identify the literal Irr⁺ quotient as a
nontrivial irreducible section. They let the source tensor theorem apply
without splitting off the fixed vectors of the original module.

Source: Aschbacher–Smith, D.3.7, printed pp.197–199, and the Borel
fixed-space calculation in 15.3.65, printed p.1152.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Representation.QuadraticFourGroup
open BinaryOffender

private theorem odd_in_rankOne_normalizer {n : ℕ} (hn : 1 < n)
    (P : Sylow 2 (Factor n)) :
    ∃ g : Factor n, g ∈ normalizer (P : Set (Factor n)) ∧
      Odd (orderOf g) ∧ g ≠ 1 := by
  let F := GaloisField 2 n
  have hn0 : n ≠ 0 := by omega
  have hcard : Nat.card F = 2 ^ n := GaloisField.card 2 n hn0
  have hu : 1 < Nat.card Fˣ := by
    rw [Nat.card_units, hcard]
    have hh : 4 ≤ 2 ^ n := (show 4 = 2 ^ 2 by rfl).le.trans
      (Nat.pow_le_pow_right (by decide) (by omega))
    omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  let e := Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.torusEquiv F
  let j : Fˣ →* Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F :=
    (inclusion (show Matrix.ProjectiveSpecialLinearGroup.OddBorel.complement F ≤
      Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F from le_sup_right)).comp
      e.toMonoidHom
  have hj : Function.Injective j := by
    intro a b h
    apply e.injective
    exact Subtype.ext (congrArg
      (fun z : Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F => (z : Factor n)) h)
  let f := Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.sylowNormalizerEquiv F P
  let x := f.symm (j a)
  have hxo : orderOf (x : Factor n) = orderOf a := by
    rw [Subgroup.orderOf_coe, show x = f.symm (j a) from rfl,
      f.symm.orderOf_eq, orderOf_injective j hj]
  refine ⟨x,x.property,?_,?_⟩
  · rw [hxo]
    have hc : Odd (Nat.card Fˣ) := by
      rw [Nat.card_units,hcard,Nat.odd_iff]
      have hp : 0 < 2 ^ n := pow_pos (by decide) n
      have hm : 2 ^ n % 2 = 0 := by simp [Nat.pow_mod,hn0]
      omega
    exact hc.of_dvd_nat (orderOf_dvd_natCard a)
  · intro h
    have hx : x = 1 := Subtype.ext h
    exact ha (hj ((f.symm.injective (hx.trans f.symm.map_one.symm)).trans j.map_one.symm))

private theorem odd_in_pair_normalizer {n : ℕ} (hn : 1 < n)
    (P : Sylow 2 (Factor n × Factor n)) :
    ∃ g : Factor n, (g,1) ∈ normalizer (P : Set (Factor n × Factor n)) ∧
      Odd (orderOf g) ∧ g ≠ 1 := by
  let D := Factor n
  let Q := P.mapSurjective (f := MonoidHom.fst D D) (fun x => ⟨(x,1),rfl⟩)
  let R := P.mapSurjective (f := MonoidHom.snd D D) (fun x => ⟨(1,x),rfl⟩)
  have htwo : IsPGroup 2 ((Q : Subgroup D).prod (R : Subgroup D)) := by
    obtain ⟨a,ha⟩ := Q.isPGroup'.exists_card_eq
    obtain ⟨b,hb⟩ := R.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := a+b) (by
      rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,ha,hb,pow_add])
  have hle : (P : Subgroup (D × D)) ≤ (Q : Subgroup D).prod (R : Subgroup D) := by
    intro x hx
    exact ⟨mem_map_of_mem (MonoidHom.fst D D) hx,mem_map_of_mem (MonoidHom.snd D D) hx⟩
  have he : (P : Subgroup (D × D)) = (Q : Subgroup D).prod (R : Subgroup D) :=
    (P.is_maximal' htwo hle).symm
  obtain ⟨g,hg,ho,hne⟩ := odd_in_rankOne_normalizer hn Q
  refine ⟨g,?_,ho,hne⟩
  rw [show (P : Set (D × D)) = ((Q : Subgroup D).prod (R : Subgroup D) : Set _) from
    congrArg SetLike.coe he]
  apply mem_normalizer_iff.mpr
  rintro ⟨x,y⟩
  change (x ∈ (Q : Subgroup D) ∧ y ∈ (R : Subgroup D) ↔
    g * x * g⁻¹ ∈ (Q : Subgroup D) ∧ 1 * y * 1⁻¹ ∈ (R : Subgroup D))
  simpa only [inv_one,one_mul,mul_one] using
    (mem_normalizer_iff.mp hg x).and
      (Iff.rfl : y ∈ (R : Subgroup D) ↔ y ∈ (R : Subgroup D))

theorem IsNaturalTensorAlong.sylowNormalizer_fixed_eq_zero
    {E W : Type*} [Group E] [Finite E] [AddCommGroup W] [Module (ZMod 2) W]
    {n : ℕ} [Group.IsPerfect (Factor n)] (hn : 1 < n)
    {π : E →* Factor n × Factor n} (hπ : Function.Surjective π)
    {σ : Representation (ZMod 2) E W} (h : IsNaturalTensorAlong π σ)
    (P : Sylow 2 E) (w : W)
    (hw : ∀ x ∈ normalizer (P : Set E), σ x w = w) : w = 0 := by
  let Q := P.mapSurjective hπ
  obtain ⟨g,hg,ho,hne⟩ := odd_in_pair_normalizer hn Q
  change (g,1) ∈ normalizer (P.map π : Set (Factor n × Factor n)) at hg
  rw [← P.normalizer_map_surjective π hπ] at hg
  obtain ⟨x,hx,hxg⟩ := hg
  exact h.first_odd_fixed x g hxg ho hne w (hw x hx)

end Representation.QuadraticFourGroup

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

set_option backward.isDefEq.respectTransparency false in
theorem IsIrrPlus.centralQuotient_not_isTrivial {K : Subgroup G}
    {I : Submodule (ZMod 2) V} (hi : IsIrrPlus ρ K I)
    (hs : K ≤ subspaceStabilizer ρ I) :
    ¬ (centralQuotientRepresentation ρ K I hs).IsTrivial := by
  intro ht
  let := ht
  apply hi.not_le_fixedSpace ρ
  rw [← hi.choose_spec.1]
  apply Submodule.span_le.mpr
  rintro _ ⟨g,hg,v,hv,rfl⟩
  have he := Representation.isTrivial_apply
    (centralQuotientRepresentation ρ K I hs) ⟨g,hg⟩
    (Submodule.Quotient.mk (⟨v,hv⟩ : I))
  change Submodule.Quotient.mk (⟨ρ g v,(hs hg v).2 hv⟩ : I) =
    Submodule.Quotient.mk (⟨v,hv⟩ : I) at he
  have hz : Submodule.Quotient.mk
      ((⟨ρ g v,(hs hg v).2 hv⟩ : I) - ⟨v,hv⟩) =
      (0 : centralQuotient ρ K I) := by
    rw [Submodule.Quotient.mk_sub,he,sub_self]
  exact (Submodule.Quotient.mk_eq_zero ((fixedSpace ρ K).comap I.subtype)).mp hz

theorem IsIrrPlus.centralQuotient_isIrreducibleSection {K : Subgroup G}
    {I : Submodule (ZMod 2) V} (hi : IsIrrPlus ρ K I)
    (hs : K ≤ subspaceStabilizer ρ I) :
    QuadraticFourGroup.IsIrreducibleSection (ρ.comp K.subtype)
      (centralQuotientRepresentation ρ K I hs) := by
  refine ⟨hi.choose_spec.2,invariantSubspace ρ K I hs,centralSubspace ρ K I hs,?_⟩
  exact ⟨Representation.Equiv.refl _⟩

end Representation.BinaryOffender

