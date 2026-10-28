module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.PlaneAvoidance

/-!
# Compatibility of cubic actors with an exceptional factor

An actor plane outside the exceptional three-space meets it in at most a
line. Two actual cubic conjugate planes avoid that line. The pair dimension
bound therefore makes the outside actor commute with both cubic subgroups,
which generate the exceptional factor. An actor supported inside the
three-space belongs to the factor by quotient-fixer rigidity.

The explicit pair-bound premise is the independent finite-actor theorem;
no global commutation condition is assumed. Source: E.6.24, printed p.255.
-/

public section
open Module Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure
open FactorConstruction
variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] {ρ : Representation (ZMod 2) A W} {C B : Subgroup A}

private theorem disjoint_line_of_not_mem (I R : Submodule (ZMod 2) W)
    (hI : finrank (ZMod 2) I ≤ 1) (v : W) (hv : v ∈ I) (hvR : v ∉ R) : Disjoint I R := by
  apply disjoint_iff.mpr
  by_contra he
  let : Nontrivial (I ⊓ R : Submodule (ZMod 2) W) := Submodule.nontrivial_iff_ne_bot.mpr he
  have hp : 0 < finrank (ZMod 2) ↥(I ⊓ R) := finrank_pos
  have hm := Submodule.finrank_mono (inf_le_left : I ⊓ R ≤ I)
  have hi : I ⊓ R = I := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
  have hh : v ∈ I ⊓ R := hi.symm ▸ hv
  exact hvR hh.2

/-- The finite pair bound forces each actual cubic actor either into the
same exceptional factor or into its centralizer. -/
theorem ExceptionalCandidate.actor_contained_or_centralizes_of_pair_bound
    (hB : ExceptionalCandidate ρ C B) (h : Input ρ C)
    (hpair : ∀ a b : A,
      (¬ ∀ c ∈ C.map (MulAut.conj a).toMonoidHom,
        ∀ d ∈ C.map (MulAut.conj b).toMonoidHom, Commute c d) →
      finrank (ZMod 2) ↥(displacementSpan ρ (C.map (MulAut.conj a).toMonoidHom) ⊤ ⊔
        displacementSpan ρ (C.map (MulAut.conj b).toMonoidHom) ⊤) ≤ 3)
    (a : A) :
    C.map (MulAut.conj a).toMonoidHom ≤ B ∨
      C.map (MulAut.conj a).toMonoidHom ≤ centralizer (B : Set A) := by
  classical
  let T := displacementSpan ρ B ⊤
  let E := C.map (MulAut.conj a).toMonoidHom
  let P := displacementSpan ρ E ⊤
  let I := P ⊓ T
  have hdim := h.moved_finrank_eq_two_of_card_three hB.cyclic_card
  have hmove (b : A) : displacementSpan ρ (C.map (MulAut.conj b).toMonoidHom) ⊤ =
      (displacementSpan ρ C ⊤).map (ρ b) := by
    have hh := displacementSpan_conjugate ρ C ⊤ b
    rw [map_top_action] at hh
    exact hh
  have hdim' (b : A) : finrank (ZMod 2)
      (displacementSpan ρ (C.map (MulAut.conj b).toMonoidHom) ⊤) = 2 := by
    rw [hmove, ← (Submodule.equivMapOfInjective (ρ b) (ρ.apply_bijective b).injective
      (displacementSpan ρ C ⊤)).finrank_eq, hdim]
  have hP : finrank (ZMod 2) P = 2 := hdim' a
  by_cases hPT : P ≤ T
  · left
    rw [← hB.quotientFixer_moved_eq h]
    intro e he v
    exact hPT (Submodule.subset_span ⟨e, he, v, Submodule.mem_top, rfl⟩)
  right
  have hI : finrank (ZMod 2) I ≤ 1 := by
    have hi := Submodule.finrank_mono (inf_le_left : I ≤ P)
    by_contra! hh
    have hrank : finrank (ZMod 2) I = finrank (ZMod 2) P := by
      dsimp only [I] at hh ⊢
      omega
    have he : I = P := Submodule.eq_of_le_of_finrank_eq (S₁ := I) inf_le_left hrank
    exact hPT (he ▸ (inf_le_right : I ≤ T))
  have hex : ∃ v ∈ T, v ≠ 0 ∧ ∀ R : Submodule (ZMod 2) W,
      v ∉ R → Disjoint I R := by
    by_cases hi : I = ⊥
    · let : Nontrivial T := Module.nontrivial_of_finrank_pos (R := ZMod 2)
        (by have ht : finrank (ZMod 2) T = 3 := hB.moved_dimension; omega)
      obtain ⟨v, hv⟩ := exists_ne (0 : T)
      exact ⟨v, v.property, fun he => hv (Subtype.ext he), fun R _ => hi ▸ disjoint_bot_left⟩
    · let : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr hi
      obtain ⟨v, hv⟩ := exists_ne (0 : I)
      exact ⟨v, v.property.2, fun he => hv (Subtype.ext he),
        fun R hn => disjoint_line_of_not_mem I R hI v v.property hn⟩
  obtain ⟨v, hv, hv0, havoid⟩ := hex
  obtain ⟨b, k, hne, hb, hk⟩ := hB.two_planes_avoiding h v hv hv0
  have hle (b : B) : C.map (MulAut.conj (b : A)).toMonoidHom ≤ B := by
    rintro _ ⟨c, hc, rfl⟩
    exact B.mul_mem (B.mul_mem b.property (hB.contained hc)) (B.inv_mem b.property)
  have hcomm (b : B) (hvR : v ∉ (displacementSpan ρ C ⊤).map (ρ b)) :
      C.map (MulAut.conj (b : A)).toMonoidHom ≤ centralizer (E : Set A) := by
    let R := displacementSpan ρ (C.map (MulAut.conj (b : A)).toMonoidHom) ⊤
    have hRT : R ≤ T := displacementSpan_mono ρ (hle b) le_rfl
    have hd : Disjoint I R := havoid R (by change v ∉ displacementSpan ρ _ ⊤; rwa [hmove])
    have hd' : Disjoint R P := by
      apply Submodule.disjoint_def.mpr
      intro w hwR hwP
      exact Submodule.disjoint_def.mp hd w ⟨hwP, hRT hwR⟩ hwR
    have hc : ∀ c ∈ C.map (MulAut.conj (b : A)).toMonoidHom, ∀ d ∈ E, Commute c d := by
      by_contra hn
      have hh := hpair b a hn
      change finrank (ZMod 2) ↥(R ⊔ P) ≤ 3 at hh
      have he := R.finrank_sup_add_finrank_inf_eq P
      rw [hd'.eq_bot, finrank_bot, add_zero, hdim' b, hP] at he
      omega
    intro c hc'
    exact mem_centralizer_iff.mpr (fun d hd => (hc c hc' d hd).symm.eq)
  have hgen := Frobenius21.sup_eq_of_distinct_cubic (hle b) (hle k)
    ((card_map_of_injective (MulAut.conj (b : A)).injective).trans hB.cyclic_card)
    ((card_map_of_injective (MulAut.conj (k : A)).injective).trans hB.cyclic_card)
    hB.factor_card hne
  apply le_centralizer_iff.mp
  rw [← hgen]
  exact sup_le (hcomm b hb) (hcomm k hk)

end Representation.RegularCyclicNormalClosure
