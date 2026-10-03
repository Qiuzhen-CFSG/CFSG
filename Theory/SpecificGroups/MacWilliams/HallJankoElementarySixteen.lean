module

public import Theory.SpecificGroups.MacWilliams.HallJankoSubgroups

/-!
# Elementary sixteens in the Hall–Janko Sylow group

There are exactly two elementary abelian subgroups of order sixteen in the
coordinate group. Their normalizers have order sixty-four, their normalizer
quotients have exponent two, and every nontrivial normalizer action fixes
exactly the marked four.

For coverage, an elementary sixteen must contain an involution outside a set
of twelve exceptional involutions. The commuting involutions of any such
element lie in one of the two explicit sixteens. Cardinality then gives equality.
All finite certificates are checked by kernel reduction; no subgroup census is
assumed. In particular, self-centralization follows without a centricity
hypothesis.

Source: `SylowPresentations`; Janko–Thompson, Math. Z. 113 (1970), Theorem 1.4,
p.386 and its application on p.395; MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace MacWilliamsSylow.HallJankoCoordinates
set_option maxRecDepth 10000
open scoped IsMulCommutative

/-- The two elementary sixteens, distinguished by their low five coordinate bits. -/
@[expose] public def sixteen (b : Bool) : Subgroup Code where
  carrier := {x | x.toFin.val % 32 ∈ (if b then [0,10,20,30] else [0,2,4,6] : List ℕ)}
  one_mem' := by revert b; decide +kernel
  mul_mem' := by revert b; decide +kernel
  inv_mem' := by revert b; decide +kernel

public instance (b : Bool) (x : Code) : Decidable (x ∈ sixteen b) :=
  inferInstanceAs (Decidable (x.toFin.val % 32 ∈ (if b then [0,10,20,30] else [0,2,4,6] : List ℕ)))

/-- Each coordinate sixteen has order sixteen. -/
public theorem sixteen_card (b : Bool) : Nat.card (sixteen b) = 16 := by
  rw [Nat.card_eq_fintype_card]
  revert b
  decide +kernel

public instance sixteen_elementary (b : Bool) : IsElementaryAbelian 2 (sixteen b) where
  toIsMulCommutative := by
    apply isMulCommutative_iff.mpr
    revert b
    decide +kernel
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    revert b
    decide +kernel

-- These are the twelve involutions outside the noncentral parts of the sixteens.
private def exceptional : Set Code := {x | x*x = 1 ∧
  ¬ ∃ b : Bool, x ∈ sixteen b ∧ x ∉ four}
private instance (x : Code) : Decidable (x ∈ exceptional) :=
  inferInstanceAs (Decidable (x*x = 1 ∧ ¬ ∃ b : Bool, x ∈ sixteen b ∧ x ∉ four))
private theorem exceptional_card : Nat.card exceptional = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem commuting_involutions : ∀ (b : Bool) (x y : Code),
    x ∈ sixteen b → x ∉ four → y*y = 1 → x*y = y*x → y ∈ sixteen b := by
  decide +kernel

/-- Every elementary subgroup of order sixteen is one of the two coordinate sixteens. -/
public theorem elementary_sixteen_eq (U : Subgroup Code) [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 16) : ∃ b : Bool, U = sixteen b := by
  have hp (x : Code) (hx : x ∈ U) : x*x = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  have hc (x y : Code) (hx : x ∈ U) (hy : y ∈ U) : x*y = y*x := by
    exact congrArg Subtype.val (mul_comm (⟨x,hx⟩ : U) ⟨y,hy⟩)
  have hex : ∃ x : U, ∃ b : Bool, (x : Code) ∈ sixteen b ∧ (x : Code) ∉ four := by
    by_contra! hn
    have hi : Nat.card U ≤ Nat.card exceptional :=
      Nat.card_le_card_of_injective
        (fun x : U => (⟨x.val, hp x.val x.property, by
          rintro ⟨b,hb,hf⟩
          exact hf (hn x b hb)⟩ : exceptional))
        (fun _ _ h => Subtype.ext (congrArg (fun z : exceptional => (z : Code)) h))
    rw [hU, exceptional_card] at hi
    omega
  obtain ⟨x,b,hb,hf⟩ := hex
  refine ⟨b, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · intro y hy
    exact commuting_involutions b x y hb hf (hp y hy) (hc x y x.property hy)
  · rw [sixteen_card, hU]

private theorem normalizer_test : ∀ (b : Bool) (g : Code),
    g ∈ Subgroup.normalizer (sixteen b : Set Code) ↔ g.toFin.val % 2 = 0 := by
  simp only [Subgroup.mem_normalizer_iff]
  decide +kernel

/-- The normalizer of each coordinate sixteen has order sixty-four. -/
public theorem sixteen_normalizer_card (b : Bool) :
    Nat.card (Subgroup.normalizer (sixteen b : Set Code)) = 64 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (normalizer_test b))]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- Each coordinate sixteen is self-centralizing. -/
public theorem sixteen_centralizer (b : Bool) :
    Subgroup.centralizer (sixteen b : Set Code) = sixteen b := by
  have h : ∀ (b : Bool) (g : Code),
      (∀ x : Code, x ∈ sixteen b → x*g = g*x) ↔ g ∈ sixteen b := by
    decide +kernel
  ext g
  exact h b g

private theorem square_test : ∀ (b : Bool) (g : Code),
    g.toFin.val % 2 = 0 → g*g ∈ sixteen b := by
  decide +kernel

private theorem fixed_test : ∀ (b : Bool) (g u : Code),
    g.toFin.val % 2 = 0 → g ∉ sixteen b → u ∈ sixteen b →
      (g*u = u*g ↔ u ∈ four) := by
  decide +kernel

/-- Every elementary sixteen is self-centralizing; no centricity assumption is needed. -/
public theorem elementary_sixteen_centralizer (U : Subgroup Code) [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 16) : Subgroup.centralizer (U : Set Code) = U := by
  obtain ⟨b, rfl⟩ := elementary_sixteen_eq U hU
  exact sixteen_centralizer b

/-- The normalizer of an elementary sixteen has order sixty-four. -/
public theorem elementary_sixteen_normalizer_card (U : Subgroup Code) [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 16) : Nat.card (Subgroup.normalizer (U : Set Code)) = 64 := by
  obtain ⟨b, rfl⟩ := elementary_sixteen_eq U hU
  exact sixteen_normalizer_card b

/-- Every normalizer element has its square in the elementary sixteen. -/
public theorem elementary_sixteen_normalizer_square (U : Subgroup Code) [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 16) (g : Subgroup.normalizer (U : Set Code)) : (g : Code)^2 ∈ U := by
  obtain ⟨b, rfl⟩ := elementary_sixteen_eq U hU
  simpa only [pow_two] using square_test b g ((normalizer_test b g).mp g.property)

/-- Every normalizer element outside the elementary sixteen fixes exactly the marked four. -/
public theorem elementary_sixteen_normalizer_fixed (U : Subgroup Code) [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 16) (g : Subgroup.normalizer (U : Set Code)) (hg : (g : Code) ∉ U)
    (u : U) : (g : Code)*(u : Code) = (u : Code)*(g : Code) ↔ (u : Code) ∈ four := by
  obtain ⟨b, rfl⟩ := elementary_sixteen_eq U hU
  exact fixed_test b g u ((normalizer_test b g).mp g.property) hg u.property

end MacWilliamsSylow.HallJankoCoordinates
