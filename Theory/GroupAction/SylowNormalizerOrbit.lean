module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card

/-!
# Sylow transitivity in a two-power orbit

A subgroup of index coprime to the cardinality of a finite transitive set
is transitive on that set. Apply the orbit-stabilizer index tower to each
subgroup orbit. In a Sylow normalizer, the prescribed Sylow has odd index;
thus it is transitive on the other points whenever their number is a power
of two and the normalizer is transitive there.

The base-point stabilizer is matched literally with the Sylow normalizer.
The ambient set need not be finite: only its orbit is used. This supplies
the actual root action in DGS, *Groups and Graphs* (1985), 8.4, pp.137--138.
-/

public section
open Subgroup
namespace Theory.GroupAction
private theorem coprime_transitive
    {K X : Type*} [Group K] [Finite K] [MulAction K X] [Finite X]
    [MulAction.IsPretransitive K X] (H : Subgroup K)
    (hcop : Nat.Coprime (Nat.card X) H.index) :
    MulAction.IsPretransitive H X := by
  classical
  constructor
  intro x y
  let L := MulAction.stabilizer K x
  have hindex : L.index = Nat.card X := MulAction.index_stabilizer_of_transitive K x
  have hdvd : Nat.card X ∣ (H ⊓ L).index :=
    hindex ▸ Subgroup.index_dvd_of_le (show H ⊓ L ≤ L from inf_le_right)
  rw [←Subgroup.relIndex_mul_index (show H ⊓ L ≤ H from inf_le_left),
    Subgroup.inf_relIndex_left] at hdvd
  have horbitDvd : Nat.card X ∣ (MulAction.orbit H x).ncard := by
    have hh := hcop.dvd_of_dvd_mul_right hdvd
    change Nat.card X ∣ (MulAction.stabilizer H x).index at hh
    rwa [MulAction.index_stabilizer] at hh
  have hpos : 0 < (MulAction.orbit H x).ncard :=
    (Set.ncard_pos).mpr ⟨x,MulAction.mem_orbit_self x⟩
  have heq : (MulAction.orbit H x).ncard = Nat.card X :=
    le_antisymm (Set.ncard_le_card _) (Nat.le_of_dvd hpos horbitDvd)
  have hfull : MulAction.orbit H x = Set.univ := (Set.eq_univ_iff_ncard _).mpr heq
  have hy : y ∈ MulAction.orbit H x := hfull ▸ Set.mem_univ y
  exact hy

/-- Two-power branching and transitivity of the Sylow normalizer give
transitivity of the prescribed Sylow away from its fixed base point. -/
theorem sylow_transitive_away_from_base
    {L X : Type*} [Group L] [Finite L] [MulAction L X]
    (S : Sylow 2 L) (w : X)
    (hstab : MulAction.stabilizer L w = normalizer (S : Set L))
    (hbranch : ∃ n : ℕ, (normalizer (S : Set L)).index - 1 = 2^n)
    (htrans : ∀ x ∈ MulAction.orbit L w, ∀ y ∈ MulAction.orbit L w,
      x ≠ w → y ≠ w → ∃ g ∈ normalizer (S : Set L), g • x = y)
    {x y : X} (hx : x ∈ MulAction.orbit L w) (hy : y ∈ MulAction.orbit L w)
    (hxw : x ≠ w) (hyw : y ≠ w) : ∃ g ∈ (S : Subgroup L), g • x = y := by
  classical
  let N := normalizer (S : Set L)
  let Y := {z : MulAction.orbit L w // (z : X) ≠ w}
  let : Finite (MulAction.orbit L w) := Finite.of_surjective
    (fun g : L => (⟨g • w,⟨g,rfl⟩⟩ : MulAction.orbit L w)) (by
      rintro ⟨z,g,rfl⟩
      exact ⟨g,rfl⟩)
  have hmem (g : L) (z : MulAction.orbit L w) : g • (z : X) ∈ MulAction.orbit L w := by
    obtain ⟨t,ht⟩ := z.property
    exact ⟨g*t,(SemigroupAction.mul_smul g t w).trans (congrArg (g • ·) ht)⟩
  have hfix (g : N) : (g : L) • w = w := by
    change (g : L) ∈ MulAction.stabilizer L w
    rw [hstab]
    exact g.property
  let : MulAction N Y := {
    smul := fun g z => (show Y from ⟨⟨(g : L) • (z.val : X),
      hmem (g : L) z.val⟩,
      fun he => z.property ((MulAction.injective (g : L)) (he.trans (hfix g).symm))⟩)
    one_smul := fun z => Subtype.ext (Subtype.ext (_root_.one_smul L (z.val : X)))
    mul_smul := fun g k z => Subtype.ext (Subtype.ext (SemigroupAction.mul_smul (g : L) (k : L) (z.val : X))) }
  let : MulAction.IsPretransitive N Y := ⟨by
    intro z t
    obtain ⟨g,hg,he⟩ := htrans z.val z.val.property t.val t.val.property z.property t.property
    exact ⟨⟨g,hg⟩,Subtype.ext (Subtype.ext he)⟩⟩
  have hc : Nat.card Y = N.index - 1 := by
    let : Fintype (MulAction.orbit L w) := Fintype.ofFinite _
    have he : Nat.card {z : MulAction.orbit L w // (z : X) = w} = 1 := by
      let : Unique {z : MulAction.orbit L w // (z : X) = w} :=
        ⟨⟨⟨w,MulAction.mem_orbit_self w⟩,rfl⟩,fun z => Subtype.ext (Subtype.ext z.property)⟩
      exact Nat.card_unique
    rw [show Nat.card Y = Nat.card (MulAction.orbit L w) -
      Nat.card {z : MulAction.orbit L w // (z : X) = w} by
        simp only [Nat.card_eq_fintype_card]; exact Fintype.card_subtype_compl _]
    rw [he]
    change (MulAction.orbit L w).ncard - 1 = N.index - 1
    rw [←MulAction.index_stabilizer,hstab]
  let T := S.subtype (show (S : Subgroup L) ≤ N from le_normalizer)
  have hcop : Nat.Coprime (Nat.card Y) (T : Subgroup N).index := by
    obtain ⟨n,hn⟩ := hbranch
    rw [hc,hn]
    exact (Nat.prime_two.coprime_pow_of_not_dvd T.not_dvd_index).symm
  let : MulAction.IsPretransitive T Y := coprime_transitive (T : Subgroup N) hcop
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq T
    (show Y from ⟨⟨x,hx⟩,hxw⟩) (show Y from ⟨⟨y,hy⟩,hyw⟩)
  exact ⟨g.val.val,g.property,congrArg (fun z : Y => (z.val : X)) hg⟩
end Theory.GroupAction
