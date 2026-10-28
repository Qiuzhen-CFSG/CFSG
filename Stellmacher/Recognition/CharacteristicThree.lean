module

public import ABG.CharacteristicParameters
public import ABG.ChapterII.Section2.SpecialUnitaryEquivSL2
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# Solvable involution centralizers force characteristic power three

If a finite N₂ group has ABG characteristic parameters at an actual involution,
its characteristic power is three. This connects the local solvability
hypothesis to the characteristic-power input for the semidihedral recognition
branch. It uses the parameter definition, without invoking the ABG main
recognition theorems.

The involution centralizer lies in a two-local normalizer and is therefore
solvable. Its prescribed central quotient lifts solvability to GL₂(q) or GU₂(q),
since the central kernel is abelian. The actual inclusions of SL₂(q) and SU₂(q),
and the proved SU₂(q) ≃ SL₂(q), make SL₂(q) solvable in either case. For q > 3,
SL₂(q) is perfect; its nontrivial projective quotient is then both perfect and
solvable, a contradiction. The parameter arithmetic gives odd q > 1, leaving
q = 3.

Source: the characteristic-parameter definition in ABG I, article pages 2–3,
and ABG II.2 Lemma 1(vi), article page 17, in
`refs/latex/alperin-brauer-gorenstein.tex`, together with the N₂ condition in
Stellmacher's introduction, `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.Recognition

universe u v

private theorem solvable_of_centralOddQuotient
    {H : Type u} [Group H] {K : Type v} [Group K] {d : ℕ}
    [Group.IsSolvable H] (h : ABG.IsCentralOddQuotient H K d) :
    Group.IsSolvable K := by
  obtain ⟨Z, hnormal, hcentral, _, _, ⟨e⟩⟩ := h
  let : Z.Normal := hnormal
  have hZ : Group.IsSolvable Z :=
    Group.isSolvable_of_comm fun a b =>
      Subtype.ext ((Subgroup.mem_center_iff.mp (hcentral b.property)) a)
  have hquot : Group.IsSolvable (K ⧸ Z) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact (Group.isSolvable_iff_subgroup_quotient Z).mpr ⟨hZ, hquot⟩

/-- The characteristic power at any involution of a finite N₂ group is three. -/
public theorem characteristicParameters_eq_three_of_nTwo
    {G : Type u} [Group G] [Finite G] {x : G} {q d : ℕ}
    (hN : IsNTwoGroup G) (hx : orderOf x = 2)
    (hparams : ABG.InvolutionCentralizerParameters x q d) : q = 3 := by
  have hodd := hparams.odd
  have hgt := hparams.one_lt
  have hcentral : Group.IsSolvable (Subgroup.centralizer ({x} : Set G)) := by
    by_contra hnot
    obtain ⟨U, hU, hUnot⟩ :=
      Theory.GroupTheory.exists_nonsolvable_twoLocal_of_involution_centralizer hx hnot
    exact hUnot (hN U hU)
  let := hcentral
  suffices hle : q ≤ 3 by
    have := Nat.odd_iff.mp hodd
    omega
  by_contra hle
  have hthree : 3 < q := by omega
  obtain ⟨p, n, hp, hn, hq, hmodel⟩ := hparams
  let : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := (Nat.odd_pow_iff hn).mp (hq ▸ hodd)
  have hfield : 3 < Nat.card (GaloisField p n) := by
    rw [GaloisField.card p n hn, ← hq]
    exact hthree
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p n)) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (GaloisField p n) hfield
  have hsl : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p n)) := by
    rcases hmodel with ⟨_, hGL⟩ | ⟨_, hGU⟩
    · let : Group.IsSolvable (ABG.GL2 p n) := solvable_of_centralOddQuotient hGL
      exact Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective
    · let : Group.IsSolvable (ABG.GU2 p n hn) := solvable_of_centralOddQuotient hGU
      let : Group.IsSolvable (ABG.unitaryForm 2 p n hn).specialSubgroup :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
          (ABG.unitaryForm 2 p n hn).specialSubgroup_le_unitarySubgroup)
      exact Group.isSolvable_of_surjective
        (f := (ABG.specialUnitaryTwo_equiv_sl2 p n hpodd hn).toMonoidHom)
        (ABG.specialUnitaryTwo_equiv_sl2 p n hpodd hn).surjective
  let := hsl
  exact Group.IsPerfect.not_isSolvable
    (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p n)) inferInstance

end Stellmacher.Recognition
