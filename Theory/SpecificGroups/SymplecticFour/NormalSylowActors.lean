module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Index
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.AutomorphismCentralizers.NonbinaryNormalForms
public import Theory.GroupTheory.NormalizedOrbitCard

/-!
# Small normal elementary actors on a symplectic Sylow subgroup

An outer diagram-preserving involution of Sp₄(2ⁿ) has a fixed subgroup over
its half-size field. Two-subgroups of that fixed group have order at most
2^(2n). The inner Sylow has order 2^(4n), so its conjugacy orbit cannot fit
in a normal elementary actor of order at most 2^(2n). Such actors are inner.

Source: Aschbacher–Smith G.11.7, printed pp.367–368; the field fixed-group
calculation is the same one used in 16.1.7–8, printed pp.1172–1173.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour.NormalSylowActors
open DiagramAutomorphisms DiagramAutomorphisms.InvolutionNormalForms
open DiagramAutomorphisms.FieldFixedResidual
open SymplecticConjugatePair.Ambient.AutomorphismCentralizers
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Two-subgroups in the fixed group of an outer natural involution have
order at most the square of the original field order. -/
theorem outer_fixed_two_subgroup_card {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (a : MulAut (Sp F)) (hao : orderOf a = 2) (ha : PreservesDiagram a)
    (hi : a ∉ MulAut.innerSubgroup (Sp F))
    (E : Subgroup a.fixedSubgroup) (hE : IsPGroup 2 E) : Nat.card E ≤ 2^(2*n) := by
  obtain ⟨he,hc⟩ := preserving_outer_normal_form hF hn
    (fun he g hg => half_frobenius_cocycle_coboundary hF (by omega) he g hg) a hao ha hi
  obtain ⟨c,hc⟩ := isConj_iff.mp hc
  have hcompat : ∀ x, c (a x) = fieldAutomorphism (frobeniusEquiv F 2^(n/2)) (c x) := by
    intro x
    exact congrArg (fun d : MulAut (Sp F) => d x) (mul_inv_eq_iff_eq_mul.mp hc)
  let e := (MulAut.fixedSubgroupEquivOfCompatible c a _ hcompat).trans
    (fixedEquiv (frobeniusEquiv F 2^(n/2)))
  let f := e.toMonoidHom.comp E.subtype
  have hp := hE.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
  have hhalf : Nat.card (halfField (F := F) (n/2)) = 2^(n/2) :=
    card_halfField (by omega) (by rw [Nat.mul_div_cancel' (even_iff_two_dvd.mp he)]; exact hF)
  have hQc : Nat.card Q = (2^(n/2))^4 := by
    exact (Nat.card_congr (Q.equiv (unipotentSylow hhalf (by omega))).toEquiv).trans
      (by rw [coe_unipotentSylow,card_unipotent,hhalf])
  have hle : Nat.card E ≤ Nat.card Q := Nat.card_le_card_of_injective
    (fun x : E => (⟨f x,hQ ⟨x,rfl⟩⟩ : Q)) (fun x y h =>
      Subtype.ext (e.injective (congrArg Subtype.val h)))
  rw [hQc,←pow_mul] at hle
  convert hle using 1
  congr 1
  have hh := Nat.mod_add_div n 2
  have hd := Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp he)
  omega

/-- A small elementary actor normalized by the whole inner Sylow cannot
contain an outer natural involution: its conjugacy orbit is too large. -/
theorem small_normal_elementary_inner {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (P : Sylow 2 (Sp F)) (E : Subgroup (MulAut (Sp F))) [IsElementaryAbelian 2 E]
    (hPE : (P : Subgroup (Sp F)).map (MulAut.conj : Sp F →* MulAut (Sp F)) ≤
      normalizer (E : Set (MulAut (Sp F))))
    (hcard : Nat.card E ≤ 2^(2*n)) (hdiagram : ∀ a ∈ E, PreservesDiagram a) :
    E ≤ MulAut.innerSubgroup (Sp F) := by
  intro a ha
  by_contra hi
  have ha1 : a ≠ 1 := fun h => hi (h ▸ (MulAut.innerSubgroup (Sp F)).one_mem)
  have hao : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  let Q := (P : Subgroup (Sp F)).map (MulAut.conj : Sp F →* MulAut (Sp F))
  let C := Q ⊓ centralizer ({a} : Set (MulAut (Sp F)))
  let eP : P ≃* Q := (P : Subgroup (Sp F)).equivMapOfInjective _ inner_injective
  let f : C →* P := eP.symm.toMonoidHom.comp (Subgroup.inclusion inf_le_left)
  have hfi : Function.Injective f := eP.symm.injective.comp (Subgroup.inclusion_injective _)
  have hf (x : C) : MulAut.conj (f x : Sp F) = x.val := by
    exact congrArg Subtype.val (eP.apply_symm_apply (Subgroup.inclusion inf_le_left x))
  let j : C →* a.fixedSubgroup := {
    toFun x := ⟨f x, by
      rw [MulAut.mem_fixedSubgroup]
      apply inner_injective
      have heq : a * MulAut.conj (f x : Sp F) * a⁻¹ = MulAut.conj (a (f x)) := by
        ext y
        simp
      rw [←heq,hf]
      have hh := mem_centralizer_singleton_iff.mp x.property.2
      rw [←hh,mul_assoc,mul_inv_cancel,mul_one]⟩
    map_one' := by
      apply Subtype.ext
      exact congrArg (fun z : P => (z : Sp F)) f.map_one
    map_mul' x y := by
      apply Subtype.ext
      exact congrArg (fun z : P => (z : Sp F)) (f.map_mul x y) }
  have hji : Function.Injective j := by
    intro x y h
    apply hfi
    exact Subtype.ext (congrArg (fun z : a.fixedSubgroup => (z : Sp F)) h)
  have hCp : IsPGroup 2 C := P.isPGroup'.of_injective f hfi
  have hb := outer_fixed_two_subgroup_card hn hF a hao (hdiagram a ha) hi j.range
    (hCp.of_surjective j.rangeRestrict j.rangeRestrict_surjective)
  rw [←Nat.card_congr (MonoidHom.ofInjective hji).toEquiv] at hb
  have horbit := card_lt_normalized_card_mul_centralizer Q E hPE a ha ha1
  have hQ : Nat.card Q = 2^(4*n) := by
    rw [←Nat.card_congr eP.toEquiv]
    rw [Nat.card_congr (P.equiv (unipotentSylow hF (by omega))).toEquiv,
      coe_unipotentSylow,card_unipotent,hF,←pow_mul]
    congr 1
    omega
  change Nat.card Q < Nat.card E * Nat.card C at horbit
  have hm := Nat.mul_le_mul hcard hb
  have heq : 2^(2*n)*2^(2*n) = 2^(4*n) := by rw [←pow_add]; congr 1; omega
  rw [heq] at hm
  rw [hQ] at horbit
  exact (not_lt_of_ge hm horbit)
end Theory.SpecificGroups.SymplecticFour.NormalSylowActors
