module

public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow.ElementaryPlacement.MatrixQuotient
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedDescent
public import Theory.SpecificGroups.Triality.RadicalCoordinates.ParabolicSplitting
public import Theory.ElementaryAbelian.Basic

/-!
# Elementary subgroups of the binary triality Sylow group lie in a radical

The faithful descent from the original elementary central quotient recovers
the genuine graph-field fixed positive matrices. Their ordered root coordinates
have first parameters a in GF(q³) and b in GF(q). The three-dimensional Geck
section constructed in `MatrixQuotient` shows that square one forces a*b = 0.
If a = 0, Frobenius forces the entire first arm orbit to vanish; if b = 0,
the central simple coordinate vanishes. These are exactly the supported root
products already identified with the two literal parabolic radicals.

An elementary subgroup is therefore contained in the union of the radicals.
The subgroup union lemma places the whole subgroup in one of them. This
proves the covering input of `TwoRank.twoRank_le_of_radical_bounds`, including
q = 2, without importing that downstream assembly module.

Source: GLS3 2.3.6–8, §§2.4–2.6, especially Definition 2.6.4
(`refs/KGroup/GLS3/chapter2.tex`). This is the elementary placement step for
the triality rank calculation used in Aschbacher–Smith G.9, printed p.356
(`refs/quasithin.pdf`); the radical rank bounds are separate results.
-/

public section


open Triality.Standard.PositiveCoordinates
open Triality.Standard.RadicalCoordinates
open Triality.Standard.ConcreteBruhat.FixedDescent
open Triality.Standard.Parabolics
namespace Triality.Standard.TwoRank
noncomputable section

/-- Every element of the actual binary positive subgroup whose square is one
lies in one of the two literal parabolic radicals. -/
theorem unipotent_mem_radical_or_radical_of_square_eq_one (n : ℕ) (hn : 0 < n)
    (u : unipotent (binaryParameters n hn)) (hu : u ^ 2 = 1) :
    u.val ∈ radical (binaryParameters n hn) .arms ∨
      u.val ∈ radical (binaryParameters n hn) .central := by
  let P := binaryParameters n hn
  let g : (positiveSubgroup P).comap (fixedSubgroup P).subtype :=
    ⟨carrierFixedEquiv P rfl u.val,
      (mem_descend_iff P rfl (positiveSubgroup P) u.val).mp u.property⟩
  obtain ⟨v, hv⟩ := (orbitPositiveEquiv_binary n hn).surjective g
  have he : orderedProduct P (expand P v) = carrierToSplit P rfl u.val :=
    congrArg (fun x : (positiveSubgroup P).comap (fixedSubgroup P).subtype => x.val.val) hv
  have hs : orderedProduct P (expand P v) ^ 2 = 1 := by
    rw [he, ← map_pow]
    have hu' : u.val ^ 2 = 1 := congrArg (fun x : unipotent P => x.val) hu
    rw [hu', map_one]
  have hzero := ElementaryPlacement.simple_coordinates_square P rfl (expand P v) hs
  change v.1 0 * (v.2 0 : ExtensionField P) = 0 at hzero
  have place (a : Node) (ha : ∀ i, ¬ rootSupport a i → expand P v i = 0) :
      u.val ∈ radical P a := by
    rw [radical_eq_descendedRootSubgroup P rfl, mem_descend_iff P rfl, ← he]
    exact orderedProduct_mem_rootSubgroup P a ⟨expand P v, ha⟩
  obtain ha | hb := mul_eq_zero.mp hzero
  · left
    apply place .arms
    intro i hi
    fin_cases i <;> simp_all [rootSupport, expand, -fieldFrobenius_apply]
  · right
    apply place .central
    intro i hi
    have hi' : i = 3 := by simpa [rootSupport] using hi
    subst i
    exact hb

/-- The elementary-subgroup covering contract for the triality two-rank
calculation, with no restriction on the positive binary exponent. -/
theorem elementary_unipotent_le_radical (n : ℕ) (hn : 0 < n)
    (E : Subgroup (unipotent (binaryParameters n hn)))
    (hE : IsElementaryAbelian 2 E) :
    E.map (unipotent (binaryParameters n hn)).subtype ≤ radical (binaryParameters n hn) .arms ∨
    E.map (unipotent (binaryParameters n hn)).subtype ≤ radical (binaryParameters n hn) .central := by
  let : IsElementaryAbelian 2 E := hE
  apply SubgroupClass.subset_union.mp
  rintro x ⟨u, hu, rfl⟩
  exact unipotent_mem_radical_or_radical_of_square_eq_one n hn u
    (elemPow_eq_one_of_isElementaryAbelian u hu)

end
end Triality.Standard.TwoRank
