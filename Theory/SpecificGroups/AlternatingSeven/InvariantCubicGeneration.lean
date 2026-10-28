module
public import Theory.SpecificGroups.AlternatingSeven.CubicSylowGeneration
public import Theory.Alternating.Aut
import all Theory.SpecificGroups.AlternatingSeven.CubicSylowGeneration
import all Theory.SpecificGroups.AlternatingSeven.DihedralLocals.CubicCatalogue
import Mathlib.Tactic

/-!
# Automorphism-invariant cubic Sylow generation of A₇

Use two S₄ subgroups in the six-point stabilizer and the order-24 group
obtained by adjoining the three-cycle on the other three letters. Each is
preserved by the full normalizer of the fixed dihedral Sylow in S₇.
Their cubic elements generate A₇, and Aut(A₇) = S₇ gives invariance under
all abstract automorphisms preserving the Sylow subgroup. Conjugacy then
transports the statement to every Sylow subgroup.

This is the invariant generation needed in Aschbacher--Smith 14.3.6(5),
printed p.992: the ambient Sylow need only normalize the component.
-/

@[expose] public section
open Equiv Subgroup
namespace AlternatingSeven.InvariantCubicGeneration
open DihedralLocals CubicSylowGeneration
private def c (j : Fin 3) : Perm7 := if j=0 then cubic 0 else if j=1 then cubic 3
  else swap 4 5 * swap 5 6
private def word (j : Fin 3) (v : Fin 8 × Fin 3) : Perm7 := tWord v.1 * c j ^ v.2.val
private def Criterion (g : Perm7) : Prop :=
  (∃ i : Fin 8, tWord i = g*r*g⁻¹) ∧ (∃ i : Fin 8, tWord i = g*s*g⁻¹)
private def Conclusion (g : Perm7) : Prop :=
  ∀ j : Fin 3, ∃ v : Fin 8 × Fin 3, word j v = g * c j * g⁻¹
private instance (g : Perm7) : Decidable (Criterion g) := inferInstanceAs (Decidable (_ ∧ _))
private instance (g : Perm7) : Decidable (Conclusion g) := inferInstanceAs (Decidable (∀ _j : Fin 3, ∃ _v : Fin 8 × Fin 3, _))
private def Block (i : Fin 7) (j : Fin 6) : Prop :=
  ∀ a ∈ permsOfList ([2,3,4,5,6] : List (Fin 7)),
    Criterion (swap 0 i * swap 1 j.succ * a) → Conclusion (swap 0 i * swap 1 j.succ * a)
private instance (i : Fin 7) (j : Fin 6) : Decidable (Block i j) := List.decidableBAll _ _
set_option maxRecDepth 10000 in
private theorem blocks0 (j : Fin 6) : Block 0 j := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
private theorem blocks1 (j : Fin 6) : Block 1 j := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
private theorem blocks2 (j : Fin 6) : Block 2 j := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
private theorem blocks3 (j : Fin 6) : Block 3 j := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
private theorem blocks4 (j : Fin 6) : Block 4 j := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
private theorem blocks5 (j : Fin 6) : Block 5 j := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
private theorem blocks6 (j : Fin 6) : Block 6 j := by
  fin_cases j <;> decide +kernel

private theorem blocks (i : Fin 7) (j : Fin 6) : Block i j := by
  fin_cases i
  · exact blocks0 j
  · exact blocks1 j
  · exact blocks2 j
  · exact blocks3 j
  · exact blocks4 j
  · exact blocks5 j
  · exact blocks6 j


private theorem normalized_cubics (p : Perm7) (hp : Criterion p) : Conclusion p := by
  obtain ⟨i,j,b,hb,rfl⟩ := split_seven p
  exact blocks i j b hb hp

private theorem words_mul (j : Fin 3) (v w : Fin 8 × Fin 3) :
    ∃ u : Fin 8 × Fin 3, word j v * word j w = word j u := by
  decide +revert +kernel
private theorem words_inv (j : Fin 3) (v : Fin 8 × Fin 3) :
    ∃ u : Fin 8 × Fin 3, (word j v)⁻¹ = word j u := by
  decide +revert +kernel
private def localGroup (j : Fin 3) : Subgroup Perm7 where
  carrier := Set.range (word j)
  one_mem' := ⟨(0,0), by decide +revert +kernel⟩
  mul_mem' := by
    rintro _ _ ⟨v,rfl⟩ ⟨w,rfl⟩
    obtain ⟨u,hu⟩ := words_mul j v w
    exact ⟨u,hu.symm⟩
  inv_mem' := by
    rintro _ ⟨v,rfl⟩
    obtain ⟨u,hu⟩ := words_inv j v
    exact ⟨u,hu.symm⟩
private theorem localGroup_card (j : Fin 3) : Nat.card (localGroup j) = 24 := by
  let f : (Fin 8 × Fin 3) → localGroup j := fun v => ⟨word j v, v, rfl⟩
  have hi : Function.Injective (word j) := by decide +revert +kernel
  have hb : Function.Bijective f := ⟨fun v w h => hi (congrArg Subtype.val h), by
    rintro ⟨g,v,rfl⟩
    exact ⟨v,rfl⟩⟩
  rw [←Nat.card_congr (Equiv.ofBijective f hb)]
  simp
private theorem localGroup_le_alternating (j : Fin 3) :
    localGroup j ≤ alternatingGroup (Fin 7) := by
  rintro _ ⟨v,rfl⟩
  exact (by decide +kernel : ∀ j : Fin 3, ∀ v : Fin 8 × Fin 3,
    Perm.sign (word j v) = 1) j v
private theorem twoGroup_le (j : Fin 3) : twoGroup ≤ localGroup j := by
  rintro _ ⟨i,rfl⟩
  exact ⟨(i,0), by simp [word]⟩
private theorem c_mem (j : Fin 3) : c j ∈ localGroup j :=
  ⟨(0,1), by simp [word,tWord]⟩
private def localInAlternating (j : Fin 3) : Subgroup A7 :=
  (localGroup j).subgroupOf (alternatingGroup (Fin 7))
private theorem local_card (j : Fin 3) : Nat.card (localInAlternating j) = 24 :=
  (Nat.card_congr (subgroupOfEquivOfLe (localGroup_le_alternating j)).toEquiv).trans
    (localGroup_card j)
private theorem sylow_le_local (j : Fin 3) :
    (fixedSylow : Subgroup A7) ≤ localInAlternating j := by
  rintro ⟨g,hg⟩ hx
  exact twoGroup_le j hx
private theorem local_index (j : Fin 3) :
    (fixedSylow : Subgroup A7).relIndex (localInAlternating j) = 3 := by
  have he := ((fixedSylow : Subgroup A7).subgroupOf (localInAlternating j)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (sylow_le_local j)).toEquiv,
    show Nat.card (fixedSylow : Subgroup A7) = 8 from fixedTwoGroup_card,local_card] at he
  change 8 * (fixedSylow : Subgroup A7).relIndex (localInAlternating j) = 24 at he
  omega

private theorem invariant (j : Fin 3) (a : MulAut A7)
    (ha : (fixedSylow : Subgroup A7).map a.toMonoidHom = fixedSylow) :
    (localInAlternating j).map a.toMonoidHom = localInAlternating j := by
  obtain ⟨p,rfl⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    7 (by decide) (by decide)).2 a
  have hp : twoGroup.map (MulAut.conj p).toMonoidHom = twoGroup := by
    have hmap : (fixedSylow : Subgroup A7).map (alternatingGroup (Fin 7)).subtype = twoGroup := by
      change (twoGroup.subgroupOf (alternatingGroup (Fin 7))).map _ = _
      rw [subgroupOf_map_subtype, inf_eq_left.mpr twoGroup_le_alternating]
    have he := congrArg (fun H : Subgroup A7 => H.map (alternatingGroup (Fin 7)).subtype) ha
    rw [map_map] at he
    have hcomp : (alternatingGroup (Fin 7)).subtype.comp (MulAut.conjNormal p).toMonoidHom =
        (MulAut.conj p).toMonoidHom.comp (alternatingGroup (Fin 7)).subtype := by ext x; rfl
    rw [hcomp, ← map_map, hmap] at he
    exact he
  have hcrit : Criterion p := by
    change p*r*p⁻¹ ∈ twoGroup ∧ p*s*p⁻¹ ∈ twoGroup
    constructor
    · rw [←hp]; exact mem_map_of_mem _ r_mem_twoGroup
    · rw [←hp]; exact mem_map_of_mem _ s_mem_twoGroup
  have hc : p*c j*p⁻¹ ∈ localGroup j := normalized_cubics p hcrit j
  apply eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conjNormal p).injective).ge
  rintro _ ⟨⟨x,hx⟩,⟨v,rfl⟩,rfl⟩
  change p * word j v * p⁻¹ ∈ localGroup j
  have ht : p*tWord v.1*p⁻¹ ∈ localGroup j := twoGroup_le j
    (hp ▸ mem_map_of_mem _ (tWord_mem_twoGroup v.1))
  have he : p * word j v * p⁻¹ =
      (p*tWord v.1*p⁻¹) * (p*c j*p⁻¹)^v.2.val := by
    change MulAut.conj p (tWord v.1 * c j ^ v.2.val) = _
    rw [map_mul,map_pow]
    rfl
  rw [he]
  exact (localGroup j).mul_mem ht ((localGroup j).pow_mem hc _)

private theorem generate (H : Subgroup A7)
    (hs : (fixedSylow : Subgroup A7) ≤ H)
    (hl : ∀ j : Fin 3, localInAlternating j ≤ H) : H = ⊤ := by
  apply CubicSylowGeneration.locals_generate H hs
  have hc (j : Fin 3) : (⟨c j,localGroup_le_alternating j (c_mem j)⟩ : A7) ∈ H := hl j (c_mem j)
  intro j
  fin_cases j
  · exact hc 0
  · convert H.mul_mem (hc 0) (hc 2) using 1
    apply Subtype.ext
    decide +kernel
  · convert H.mul_mem (hc 0) (H.inv_mem (hc 2)) using 1
    apply Subtype.ext
    decide +kernel
  · exact hc 1

theorem fixed_invariant_cubic_generation (H : Subgroup A7)
    (hs : (fixedSylow : Subgroup A7) ≤ H)
    (hl : ∀ J : Subgroup A7, (fixedSylow : Subgroup A7) ≤ J →
      (fixedSylow : Subgroup A7).relIndex J = 3 →
      (∀ a : MulAut A7, (fixedSylow : Subgroup A7).map a.toMonoidHom = fixedSylow →
        J.map a.toMonoidHom = J) → J ≤ H) : H = ⊤ :=
  generate H hs fun j => hl _ (sylow_le_local j) (local_index j) (invariant j)


/-- Every Sylow subgroup admits generating cubic overgroups invariant under
all automorphisms preserving that Sylow subgroup. -/
theorem sylow_invariant_cubic_generation (P : Sylow 2 A7) (H : Subgroup A7)
    (hs : (P : Subgroup A7) ≤ H)
    (hl : ∀ J : Subgroup A7, (P : Subgroup A7) ≤ J →
      (P : Subgroup A7).relIndex J = 3 →
      (∀ a : MulAut A7, (P : Subgroup A7).map a.toMonoidHom = P →
        J.map a.toMonoidHom = J) → J ≤ H) : H = ⊤ := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A7 P fixedSylow
  let a := MulAut.conj g
  have hmap : (P : Subgroup A7).map a.toMonoidHom = (fixedSylow : Subgroup A7) :=
    congrArg Sylow.toSubgroup hg
  have he : H.map a.toMonoidHom = ⊤ := by
    apply fixed_invariant_cubic_generation
    · exact hmap ▸ map_mono hs
    · intro J hPJ hi hinv
      have hPpre : (P : Subgroup A7) ≤ J.comap a.toMonoidHom :=
        (map_le_iff_le_comap).mp (hmap ▸ hPJ)
      have hindex : (P : Subgroup A7).relIndex (J.comap a.toMonoidHom) = 3 := by
        have hh := relIndex_map_map_of_injective (f := a.toMonoidHom)
          (P : Subgroup A7) (J.comap a.toMonoidHom) a.injective
        rw [hmap,map_comap_eq_self_of_surjective a.surjective] at hh
        exact hh.symm.trans hi
      have hpreinv (b : MulAut A7) (hb : (P : Subgroup A7).map b.toMonoidHom = P) :
          (J.comap a.toMonoidHom).map b.toMonoidHom = J.comap a.toMonoidHom := by
        let d : MulAut A7 := a.symm.trans (b.trans a)
        have hd : d.toMonoidHom.comp a.toMonoidHom = a.toMonoidHom.comp b.toMonoidHom := by
          apply MonoidHom.ext
          intro x
          exact congrArg a (congrArg b (a.symm_apply_apply x))
        have hdP : (fixedSylow : Subgroup A7).map d.toMonoidHom = fixedSylow := by
          rw [←hmap,map_map,hd,←map_map,hb]
        have heq := hinv d hdP
        apply map_injective (f := a.toMonoidHom) a.injective
        rw [map_map,←hd,←map_map,map_comap_eq_self_of_surjective a.surjective,heq]
      have hh := map_mono (f := a.toMonoidHom) (hl _ hPpre hindex hpreinv)
      rwa [map_comap_eq_self_of_surjective a.surjective] at hh
  apply map_injective (f := a.toMonoidHom) a.injective
  rw [he,map_top_of_surjective _ a.surjective]

end AlternatingSeven.InvariantCubicGeneration
