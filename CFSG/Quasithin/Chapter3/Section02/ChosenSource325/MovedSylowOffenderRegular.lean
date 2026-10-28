module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderGeometry

/-!
# Excluding regular cubic orbits of large constituents

On an independent regular summand orbit, a nonzero third displacement
would have eight independent supports. Cubicity therefore restricts an
elementary actor to order at most four. An involution's diagonal has the
summand dimension; for an actor of order four two independent diagonals
have twice that dimension. Both cases contradict the two-rank fixed-space
bound when each constituent has dimension greater than two.

This proves that the constituent stabilizer is nontrivial, closing the
central-stabilizer branch in D.2.9(1) for faithful chosen constituents.
The application is in `SeedAlternativesMovedActor`.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
D.2.9(1--2), printed pp.180--181, applied in D.3.5, pp.195--196.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)

/-- On a regular independent summand orbit, a cubic action cannot support
three independent involutions: one nonempty product must be the identity. -/
theorem cubic_regular_orbit_cube_product
    (I : Submodule (ZMod 2) W) (hI : I ≠ ⊥) (A : Subgroup H)
    (hc : IsCubic ρ A) (hind : sSupIndep (subspaceOrbit ρ A I))
    (hs : A ⊓ subspaceStabilizer ρ I = ⊥) (a b c : A) :
    a = 1 ∨ b = 1 ∨ c = 1 ∨ b*a = 1 ∨ c*a = 1 ∨ c*b = 1 ∨ c*(b*a) = 1 := by
  by_contra hn
  push Not at hn
  have hinj := subspace_orbitMap_injective ρ hs
  have hImem : I ∈ subspaceOrbit ρ A I := by
    refine ⟨1,?_⟩
    simp only [Subgroup.coe_one,map_one,Module.End.one_eq_id,Submodule.map_id]
  let R := sSup (subspaceOrbit ρ A I \ {I})
  have hrest (d : A) (hd : d ≠ 1) : I.map (ρ d) ≤ R := by
    apply le_sSup
    refine ⟨⟨d,rfl⟩,?_⟩
    intro he
    change I.map (ρ d) = I at he
    apply hd
    apply hinj
    simpa only [Subgroup.coe_one,map_one,Module.End.one_eq_id,Submodule.map_id] using he
  apply hI
  apply bot_unique
  intro v hv
  have hmem (d : A) (hd : d ≠ 1) : ρ d v ∈ R := hrest d hd ⟨v,hv,rfl⟩
  have he := hc c c.property b b.property a a.property v
  change ρ c (ρ b (ρ a v-v) - (ρ a v-v)) -
    (ρ b (ρ a v-v) - (ρ a v-v)) = 0 at he
  simp only [map_sub, ← Module.End.mul_apply, ← map_mul] at he
  have hev : v = ρ (c*(b*a)) v - ρ (c*b) v - ρ (c*a) v + ρ c v -
      ρ (b*a) v + ρ b v + ρ a v := by
    change ρ ((c : H)*((b : H)*(a : H))) v - ρ ((c : H)*(b : H)) v -
      (ρ ((c : H)*(a : H)) v - ρ c v) - (ρ ((b : H)*(a : H)) v - ρ b v -
      (ρ a v-v)) = 0 at he
    apply sub_eq_zero.mp
    calc
      _ = -(ρ ((c : H)*((b : H)*(a : H))) v - ρ ((c : H)*(b : H)) v -
        (ρ ((c : H)*(a : H)) v - ρ c v) - (ρ ((b : H)*(a : H)) v - ρ b v -
        (ρ a v-v))) := by abel
      _ = 0 := by rw [he,neg_zero]
  have hvR : v ∈ R := by
    rw [hev]
    exact R.add_mem (R.add_mem (R.sub_mem
      (R.add_mem (R.sub_mem (R.sub_mem (hmem _ hn.2.2.2.2.2.2)
        (hmem _ hn.2.2.2.2.2.1)) (hmem _ hn.2.2.2.2.1)) (hmem _ hn.2.2.1))
      (hmem _ hn.2.2.2.1)) (hmem _ hn.2.1)) (hmem _ hn.1)
  exact Submodule.disjoint_def.mp (hind hImem) v hv hvR

/-- A regular cubic elementary orbit has at most four summands. -/
theorem cubic_regular_actor_card_le_four [Finite H]
    (I : Submodule (ZMod 2) W) (hI : I ≠ ⊥) (A : Subgroup H)
    (hA : IsElementaryTwo A) (hc : IsCubic ρ A)
    (hind : sSupIndep (subspaceOrbit ρ A I))
    (hs : A ⊓ subspaceStabilizer ρ I = ⊥) : Nat.card A ≤ 4 := by
  classical
  let : IsElementaryAbelian 2 A := hA.2
  let : Fintype A := Fintype.ofFinite A
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot _).mpr hA.1
  obtain ⟨a,ha⟩ := exists_ne (1 : A)
  have hinv (x : A) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A) x
  by_cases he : ∀ b : A, b = 1 ∨ b = a
  · have hsub : (Finset.univ : Finset A) ⊆ {1,a} := by
      intro b _
      simpa only [Finset.mem_insert,Finset.mem_singleton] using he b
    have hn := Finset.card_le_card hsub
    have hi := Finset.card_insert_le (1 : A) {a}
    simpa only [Nat.card_eq_fintype_card,Finset.card_univ,Finset.card_singleton] using
      (show Fintype.card A ≤ 4 by simp only [Finset.card_univ,Finset.card_singleton] at *; omega)
  · push Not at he
    obtain ⟨b,hb1,hba⟩ := he
    have hcover (c : A) : c = 1 ∨ c = a ∨ c = b ∨ c = b*a := by
      rcases cubic_regular_orbit_cube_product ρ I hI A hc hind hs a b c with
        h | h | h | h | h | h | h
      · exact (ha h).elim
      · exact (hb1 h).elim
      · exact Or.inl h
      · exact (hba ((eq_inv_of_mul_eq_one_left h).trans (hinv a))).elim
      · exact Or.inr (Or.inl ((eq_inv_of_mul_eq_one_left h).trans (hinv a)))
      · exact Or.inr (Or.inr (Or.inl ((eq_inv_of_mul_eq_one_left h).trans (hinv b))))
      · exact Or.inr (Or.inr (Or.inr ((eq_inv_of_mul_eq_one_left h).trans (hinv (b*a)))))
    have hsub : (Finset.univ : Finset A) ⊆ {1,a,b,b*a} := by
      intro c _
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hcover c
    have hn := Finset.card_le_card hsub
    have h1 := Finset.card_insert_le (1 : A) {a,b,b*a}
    have h2 := Finset.card_insert_le a {b,b*a}
    have h3 := Finset.card_insert_le b {b*a}
    rw [Nat.card_eq_fintype_card]
    simp only [Finset.card_univ,Finset.card_singleton] at *
    omega

/-- A disjoint translate contributes one whole summand to the codimension
of the actor's fixed space. -/
theorem finrank_le_fixedCodim_of_disjoint_translate [FiniteDimensional (ZMod 2) W]
    (I : Submodule (ZMod 2) W) (A : Subgroup H) {a : H} (ha : a ∈ A)
    (hd : Disjoint I (I.map (ρ a))) : Module.finrank (ZMod 2) I ≤ fixedCodim ρ A := by
  let f := ρ a - LinearMap.id
  have hf : fixedSpace ρ A ≤ f.ker := by
    intro v hv
    exact sub_eq_zero.mpr (hv ⟨a,ha⟩)
  have him : diagonalSubspace ρ I a ≤ f.range := by
    rintro _ ⟨v,_,rfl⟩
    exact ⟨v,rfl⟩
  have hdiag := finrank_diagonal_eq_of_disjoint ρ I a hd
  have himdim := Submodule.finrank_mono him
  have hkdim := Submodule.finrank_mono hf
  have hnull := f.finrank_range_add_finrank_ker
  have hcodim := fixedCodim_add_finrank ρ A
  omega

/-- A cubic elementary actor satisfying the two-rank bound cannot have a
regular independent orbit of constituents of dimension greater than two. -/
theorem cubic_stabilizer_ne_bot [Finite H] [FiniteDimensional (ZMod 2) W]
    (I : Submodule (ZMod 2) W) (A : Subgroup H) (hA : IsElementaryTwo A)
    (hc : IsCubic ρ A) (hind : sSupIndep (subspaceOrbit ρ A I))
    (hdim : 2 < Module.finrank (ZMod 2) I)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    A ⊓ subspaceStabilizer ρ I ≠ ⊥ := by
  classical
  intro hs
  let : IsElementaryAbelian 2 A := hA.2
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot _).mpr hA.1
  have hI : I ≠ ⊥ := Submodule.nontrivial_iff_ne_bot.mp
    (Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) I))
  have hcard := cubic_regular_actor_card_le_four ρ I hI A hA hc hind hs
  have hrank : rank A ≤ 2 := by
    exact (Nat.log_mono_right (b := 2) hcard).trans (by decide)
  have hinj := subspace_orbitMap_injective ρ hs
  have hf : Function.Injective (fun a : A =>
      (⟨I.map (ρ a),⟨a,rfl⟩⟩ : subspaceOrbit ρ A I)) := by
    intro a b he
    exact hinj (congrArg Subtype.val he)
  have hi := ((sSupIndep_iff _).mp hind).comp hf
  change iSupIndep (fun a : A => I.map (ρ a)) at hi
  obtain ⟨a,ha⟩ := exists_ne (1 : A)
  have hdis : Disjoint I (I.map (ρ a)) := by
    simpa only [Function.onFun,Subgroup.coe_one,map_one,Module.End.one_eq_id,Submodule.map_id] using
      hi.pairwiseDisjoint (show (1 : A) ≠ a from ha.symm)
  by_cases htwo : ∀ b : A, b = 1 ∨ b = a
  · have hc2 : Nat.card A = 2 := Nat.card_eq_two_iff.mpr ⟨1,a,ha.symm,
      Set.eq_univ_of_forall (fun b => htwo b)⟩
    have hr : rank A = 1 := by change Nat.log 2 (Nat.card A) = 1; rw [hc2]; decide
    have hd := finrank_le_fixedCodim_of_disjoint_translate ρ I A a.property hdis
    rw [hr] at hbound
    omega
  · push Not at htwo
    obtain ⟨b,hb1,hba⟩ := htwo
    have hainv : a⁻¹ = a := by
      apply inv_eq_of_mul_eq_one_left
      simpa only [pow_two] using
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A) a
    have hab1 : a*b ≠ 1 := by
      intro he
      exact hba ((eq_inv_of_mul_eq_one_right he).trans hainv)
    have habb : a*b ≠ b := by
      intro he
      exact ha (mul_right_cancel (show a*b = 1*b by simpa only [one_mul] using he))
    have hdset : Disjoint ({1,b} : Set A) {a,a*b} := by
      apply Set.disjoint_left.mpr
      rintro x (rfl | rfl) (he | he)
      · exact ha he.symm
      · exact hab1 he.symm
      · exact hba he
      · exact habb he.symm
    have hds := hi.disjoint_biSup_biSup' hdset (Set.toFinite _)
    simp only [iSup_insert,iSup_singleton,Subgroup.coe_one,map_one,
      Module.End.one_eq_id,Submodule.map_id] at hds
    have hdU : Disjoint (I ⊔ I.map (ρ b)) ((I ⊔ I.map (ρ b)).map (ρ a)) := by
      rw [Submodule.map_sup, ← subspace_map_mul]
      exact hds
    have hdIb : Disjoint I (I.map (ρ b)) := by
      simpa only [Function.onFun,Subgroup.coe_one,map_one,Module.End.one_eq_id,Submodule.map_id] using
        hi.pairwiseDisjoint (show (1 : A) ≠ b from hb1.symm)
    have hdimU := I.finrank_sup_add_finrank_inf_eq (I.map (ρ b))
    rw [hdIb.eq_bot,finrank_bot,add_zero,finrank_map_action] at hdimU
    have hd := finrank_le_fixedCodim_of_disjoint_translate ρ (I ⊔ I.map (ρ b)) A a.property hdU
    omega

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
