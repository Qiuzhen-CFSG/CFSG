module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Identification
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.ExceptionalFixed
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Involution fixed subgroups for faithful two-group actions on A₆

The fixed subgroups of the involutions in a faithful two-group action generate
A₆ whenever the actor contains two noncommuting involutions. In the marked
Sylow model, their product forces the central inner involution into the actor.
Its fixed subgroup is Sylow of order eight. An exceptional involution supplies
a fixed subgroup of order ten; for natural involutions, four explicit even
permutations supply fixed elements whose product has order five. A proper
Sylow overgroup has order eight or twenty-four, excluding either possibility.

The finite checks use the thirty-two-element holomorph and sixteen-element
natural subgroup. Transport retains the given faithful action on the actual
six-point alternating group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 2.5.21, printed p.566, the A₆ case of the
involution-centralizer generation step for a nonquaternion core.
-/

open Subgroup GLS3.Chapter5
namespace AlternatingSix.NonabelianInvolutionGeneration
open ShadowLocal

namespace Natural

private abbrev Actor := Holomorph.C2 × DihedralGroup 4

private def naturalPermutation (a : Actor) : Equiv.Perm (Fin 6) :=
  Identification.transpositionPerm ^ a.1.toAdd.val * (dihedralEmbedding a.2).val

private theorem embedding_natural (a : Actor) :
    Identification.embedding (Holomorph.naturalEmbedding a) =
      permutationAction (naturalPermutation a) := by
  have hd (d : DihedralGroup 4) :
      Identification.embedding (Holomorph.innerEmbedding d) =
        permutationAction (dihedralEmbedding d).val := by
    cases d with
    | r i =>
      change Identification.embedding ((Holomorph.rotation ^ 2) ^ i.val) =
        permutationAction (dihedralRotation.val ^ i.val)
      rw [map_pow, map_pow, Identification.embedding_rotation,
        Identification.rotation_sq, map_pow]
    | sr i =>
      change Identification.embedding (Holomorph.reflection * (Holomorph.rotation ^ 2) ^ i.val) =
        permutationAction (dihedralReflection.val * dihedralRotation.val ^ i.val)
      simp only [map_mul, map_pow,
        Identification.embedding_rotation, Identification.rotation_sq,
        Identification.embedding_reflection, Identification.reflection]
  change Identification.embedding
    (Holomorph.transposition ^ a.1.toAdd.val * Holomorph.innerEmbedding a.2) = _
  rw [map_mul, map_pow, Identification.embedding_transposition, hd]
  simp only [naturalPermutation, map_mul, map_pow, Identification.transposition]

private def witnessPerm : Fin 4 → Equiv.Perm (Fin 6)
  | 0 => Equiv.swap 2 3 * Equiv.swap 4 5
  | 1 => Equiv.swap 1 2 * Equiv.swap 4 5
  | 2 => Equiv.swap 1 4 * Equiv.swap 3 5
  | 3 => Equiv.swap 0 4 * Equiv.swap 2 5

private theorem witness_even (i : Fin 4) : witnessPerm i ∈ alternatingGroup (Fin 6) := by
  fin_cases i <;> rw [Equiv.Perm.mem_alternatingGroup] <;> decide +kernel

private def witness (i : Fin 4) : A6 := ⟨witnessPerm i, witness_even i⟩

private def selectedWitness (a : Actor) : Fin 4 :=
  match a.2 with
  | .r _ => 0
  | .sr i => if i = 1 then 0 else if i = 3 then 1 else
      if i.val = 2 * a.1.toAdd.val then 3 else 2

private instance permDecEq : DecidableEq (Equiv.Perm (Fin 6)) := inferInstance
private instance actorDecEq : DecidableEq Actor := inferInstance

private theorem selected_table : ∀ a b : Actor, a ^ 2 = 1 → b ^ 2 = 1 → a * b ≠ b * a →
    witnessPerm (selectedWitness a) * naturalPermutation a =
        naturalPermutation a * witnessPerm (selectedWitness a) ∧
      witnessPerm (selectedWitness b) * naturalPermutation b =
        naturalPermutation b * witnessPerm (selectedWitness b) ∧
      (witnessPerm (selectedWitness a) * witnessPerm (selectedWitness b)) ^ 5 = 1 ∧
      witnessPerm (selectedWitness a) * witnessPerm (selectedWitness b) ≠ 1 := by
  decide +kernel

private theorem finite_table : ∀ a b : Actor, a ^ 2 = 1 → b ^ 2 = 1 → a * b ≠ b * a →
    ∃ i j : Fin 4,
      witnessPerm i * naturalPermutation a = naturalPermutation a * witnessPerm i ∧
      witnessPerm j * naturalPermutation b = naturalPermutation b * witnessPerm j ∧
      (witnessPerm i * witnessPerm j) ^ 5 = 1 ∧ witnessPerm i * witnessPerm j ≠ 1 := by
  intro a b ha hb hn
  exact ⟨selectedWitness a, selectedWitness b, selected_table a b ha hb hn⟩

private theorem exists_fixed_product_five (a b : Actor)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hne : a * b ≠ b * a) :
    ∃ x y : A6, permutationAction (naturalPermutation a) x = x ∧
      permutationAction (naturalPermutation b) y = y ∧ orderOf (x * y) = 5 := by
  obtain ⟨i, j, hi, hj, hp, hn⟩ := finite_table a b ha hb hne
  refine ⟨witness i, witness j, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change naturalPermutation a * witnessPerm i * (naturalPermutation a)⁻¹ = witnessPerm i
    rw [← hi, mul_assoc, mul_inv_cancel, mul_one]
  · apply Subtype.ext
    change naturalPermutation b * witnessPerm j * (naturalPermutation b)⁻¹ = witnessPerm j
    rw [← hj, mul_assoc, mul_inv_cancel, mul_one]
  · let : Fact (Nat.Prime 5) := ⟨by decide⟩
    apply orderOf_eq_prime
    · exact Subtype.ext hp
    · intro he
      exact hn (congrArg Subtype.val he)

private theorem exists_model_fixed_product_five (a b : Actor)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hne : a * b ≠ b * a) :
    ∃ x y : A6, Identification.embedding (Holomorph.naturalEmbedding a) x = x ∧
      Identification.embedding (Holomorph.naturalEmbedding b) y = y ∧
      orderOf (x * y) = 5 := by
  rw [embedding_natural, embedding_natural]
  exact exists_fixed_product_five a b ha hb hne

end Natural

private theorem natural_model_product (a b : Holomorph.Model)
    (haN : a ∈ Holomorph.natural) (hbN : b ∈ Holomorph.natural)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b ≠ b * a) :
    ∃ x y : A6, Identification.embedding a x = x ∧
      Identification.embedding b y = y ∧ orderOf (x * y) = 5 := by
  obtain ⟨a, rfl⟩ := (Holomorph.mem_natural _).mp haN
  obtain ⟨b, rfl⟩ := (Holomorph.mem_natural _).mp hbN
  have ha' : a ^ 2 = 1 := Holomorph.naturalEmbedding_injective
    (by simpa only [map_pow, map_one] using ha)
  have hb' : b ^ 2 = 1 := Holomorph.naturalEmbedding_injective
    (by simpa only [map_pow, map_one] using hb)
  have hab' : a * b ≠ b * a := by
    intro h
    exact hab (by simpa only [map_mul] using congrArg Holomorph.naturalEmbedding h)
  exact Natural.exists_model_fixed_product_five a b ha' hb' hab'


private theorem top_of_fixed_and_five (N : Subgroup A6) (z : A6)
    (hz : orderOf z = 2) (hfix : automorphismFixedSubgroup (MulAut.conj z) ≤ N)
    (hfive : 5 ∣ Nat.card N) : N = ⊤ := by
  let F := automorphismFixedSubgroup (MulAut.conj z)
  have hc : Nat.card F = 8 := inner_involution_fixed_card z hz
  have hp : IsPGroup 2 F := IsPGroup.of_card (show Nat.card F = 2 ^ 3 from hc)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have he : F = (P : Subgroup A6) := eq_of_le_of_card_ge hP
    (by rw [hc, alternatingSylow_card])
  by_contra hn
  have hh := ProperSylowOvergroups.card_eight_or_twentyFour P N (he ▸ hfix) hn
  rcases hh with hh | hh <;> rw [hh] at hfive <;> norm_num at hfive

private theorem model_central_power (a b : Holomorph.Model)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b ≠ b * a) :
    (a * b) ^ 2 = Holomorph.rotation ^ 4 ∨
      (a * b) ^ 4 = Holomorph.rotation ^ 4 := by
  revert a b
  decide +kernel

private theorem model_central_image :
    Identification.embedding (Holomorph.rotation ^ 4) =
      MulAut.conj (dihedralRotation ^ 2) := by
  rw [map_pow, Identification.embedding_rotation, show 4 = 2 * 2 from rfl,
    pow_mul, Identification.rotation_sq, permutationAction_coe, ← map_pow]

private theorem model_central_order : orderOf (Holomorph.rotation ^ 4) = 2 := by
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

private theorem model_central_inner_order : orderOf (dihedralRotation ^ 2) = 2 := by
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

private theorem embedding_natural (a : Holomorph.Model) (ha : a ∈ Holomorph.natural) :
    Identification.embedding a ∈ natural := by
  apply (show Holomorph.natural ≤ natural.comap Identification.embedding from ?_) ha
  apply (closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · change Identification.embedding (Holomorph.rotation ^ 2) ∈ natural
    rw [map_pow, Identification.embedding_rotation, Identification.rotation_sq]
    exact ⟨_, rfl⟩
  · change Identification.embedding Holomorph.transposition ∈ natural
    rw [Identification.embedding_transposition, Identification.transposition]
    exact ⟨_, rfl⟩
  · change Identification.embedding Holomorph.reflection ∈ natural
    rw [Identification.embedding_reflection, Identification.reflection]
    exact ⟨_, rfl⟩

private theorem embedding_natural_iff (a : Holomorph.Model) :
    Identification.embedding a ∈ natural ↔ a ∈ Holomorph.natural := by
  refine ⟨?_, embedding_natural a⟩
  intro ha
  by_contra hn
  have hindex : Holomorph.natural.index = 2 := by
    have hc : Nat.card Holomorph.natural = 16 := by
      rw [Nat.card_congr Holomorph.naturalEquiv.toEquiv, Nat.card_prod,
        DihedralGroup.nat_card]
      norm_num [Holomorph.C2, Nat.card_eq_fintype_card]
    have hh := Holomorph.natural.card_mul_index
    rw [hc, Holomorph.card_model] at hh
    omega
  have hr : Holomorph.rotation ∉ Holomorph.natural := by
    rw [Holomorph.mem_natural]
    decide +kernel
  have hm : Holomorph.rotation * a ∈ Holomorph.natural :=
    (mul_mem_iff_of_index_two hindex).mpr (iff_of_false hr hn)
  have hx := embedding_natural _ hm
  rw [map_mul] at hx
  exact Identification.rotation_not_mem_natural
    (Identification.embedding_rotation ▸ (natural.mul_mem_cancel_right ha).mp hx)

private theorem model_generation (R : Subgroup Holomorph.Model)
    (a b : Holomorph.Model) (haR : a ∈ R) (hbR : b ∈ R)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b ≠ b * a)
    (N : Subgroup A6)
    (hfixed : ∀ d ∈ R, orderOf d = 2 →
      automorphismFixedSubgroup (Identification.embedding d) ≤ N) : N = ⊤ := by
  have hzR : Holomorph.rotation ^ 4 ∈ R := by
    rcases model_central_power a b ha hb hab with h | h
    · exact h ▸ R.pow_mem (R.mul_mem haR hbR) 2
    · exact h ▸ R.pow_mem (R.mul_mem haR hbR) 4
  have hzfixed : automorphismFixedSubgroup (MulAut.conj (dihedralRotation ^ 2)) ≤ N := by
    rw [← model_central_image]
    exact hfixed _ hzR model_central_order
  by_contra hn
  have hnat (d : Holomorph.Model) (hd : d ∈ R) (hdo : orderOf d = 2) :
      d ∈ Holomorph.natural := by
    apply (embedding_natural_iff d).mp
    by_contra hdout
    have heo : orderOf (Identification.embedding d) = 2 :=
      (orderOf_injective _ Identification.embedding_injective d).trans hdo
    have hdiv := card_dvd_of_le (hfixed d hd hdo)
    rw [outside_natural_involution_fixed_card _ heo hdout] at hdiv
    exact hn (top_of_fixed_and_five N _ model_central_inner_order hzfixed
      ((by decide : 5 ∣ 10).trans hdiv))
  have hao : orderOf a = 2 := orderOf_eq_prime ha
    (by intro h; subst a; simp at hab)
  have hbo : orderOf b = 2 := orderOf_eq_prime hb
    (by intro h; subst b; simp at hab)
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    natural_model_product a b (hnat a haR hao) (hnat b hbR hbo) ha hb hab
  have hxyN : x * y ∈ N := N.mul_mem (hfixed a haR hao hx) (hfixed b hbR hbo hy)
  have hdiv := card_dvd_of_le (zpowers_le.mpr hxyN)
  rw [Nat.card_zpowers, hxy] at hdiv
  exact hn (top_of_fixed_and_five N _ model_central_inner_order hzfixed hdiv)

/-- Involution fixed subgroups generate A₆ for a faithful two-group action
with two noncommuting involutions. -/
public theorem fixed_generation_of_noncommuting_involutions {D : Type*} [Group D] [Finite D]
    (hp : IsPGroup 2 D) (f : D →* AutA6) (hf : Function.Injective f)
    (a b : D) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b ≠ b * a)
    (N : Subgroup A6)
    (hfixed : ∀ d : D, orderOf d = 2 → (f d).fixedSubgroup ≤ N) : N = ⊤ := by
  have hpR : IsPGroup 2 f.range := hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨P, hP⟩ := hpR.exists_le_sylow
  let g : D →* P := f.codRestrict (P : Subgroup AutA6) (fun d => hP ⟨d, rfl⟩)
  let e := Identification.sylowEquiv P
  let q : D →* Holomorph.Model := e.symm.toMonoidHom.comp g
  have hg : Function.Injective g := fun x y h => hf (congrArg Subtype.val h)
  have hq : Function.Injective q := e.symm.injective.comp hg
  let c : AutA6 := permutationAction (Identification.conjugatingPermutation P)
  have haction (d : D) : f d = c * Identification.embedding (q d) * c⁻¹ := by
    have h := Identification.sylowEquiv_coe P (q d)
    have hh : e (q d) = g d := e.apply_symm_apply (g d)
    rw [show Identification.sylowEquiv P (q d) = g d from hh] at h
    exact h
  let N' := N.comap c.toMonoidHom
  have hfixed' (u : Holomorph.Model) (hu : u ∈ q.range) (huo : orderOf u = 2) :
      automorphismFixedSubgroup (Identification.embedding u) ≤ N' := by
    obtain ⟨d, rfl⟩ := hu
    have hd : orderOf d = 2 := (orderOf_injective q hq d).symm.trans huo
    intro x hx
    apply hfixed d hd
    rw [MulAut.mem_fixedSubgroup]
    change (f d) (c x) = c x
    rw [haction]
    change c (Identification.embedding (q d) (c⁻¹ (c x))) = c x
    rw [MulAut.inv_apply_self]
    exact congrArg c hx
  have hn := model_generation q.range (q a) (q b) ⟨a,rfl⟩ ⟨b,rfl⟩
    (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one])
    (fun h => hab (hq (by simpa only [map_mul] using h))) N' hfixed'
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := c.surjective x
  exact (show y ∈ N' from by rw [hn]; exact mem_top y)

end AlternatingSix.NonabelianInvolutionGeneration

