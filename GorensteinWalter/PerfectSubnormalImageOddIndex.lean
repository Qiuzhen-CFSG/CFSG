module

public import GorensteinWalter.Defs
public import Mathlib.GroupTheory.IsPerfect
import FeitThompson.FinalTheorem

/-!
# Perfect subnormal images across solvable kernels

This isolates the quotient step used in the linear constructors of Bender's
`D`-group classification.  A nontrivial perfect subnormal subgroup stays
nontrivial, perfect, and subnormal modulo a solvable normal subgroup.  It then
lies in every normal odd-index subgroup of that quotient, since its image in
the remaining odd-order quotient is both perfect and solvable.
-/

noncomputable section

namespace GorensteinWalter

universe u

/-- The image of a nontrivial perfect subnormal subgroup across a solvable
normal kernel remains nontrivial, perfect, and subnormal.  If the quotient
has a normal odd-index subgroup `L`, that image lies in `L`. -/
public theorem perfect_subnormal_image_le_normal_odd_index
    {H : Type u} [Group H] [Finite H]
    (E : Subgroup H) (hEperf : Group.IsPerfect E) (hEne : E ≠ ⊥)
    (hEsn : E.IsSubnormal)
    (O : Subgroup H) [O.Normal] (hOsolv : Group.IsSolvable O)
    (L : Subgroup (H ⧸ O)) (hLnormal : L.Normal)
    (hLindex : Odd L.index) :
    let q : H →* H ⧸ O := QuotientGroup.mk' O
    let Ebar : Subgroup (H ⧸ O) := E.map q
    Ebar ≠ ⊥ ∧ Group.IsPerfect Ebar ∧ Ebar.IsSubnormal ∧ Ebar ≤ L := by
  dsimp
  let q : H →* H ⧸ O := QuotientGroup.mk' O
  let Ebar : Subgroup (H ⧸ O) := E.map q
  have hEbarperf : Group.IsPerfect Ebar := by
    dsimp [Ebar]
    letI : Group.IsPerfect E := hEperf
    exact Group.IsPerfect.map q
  have hEbarne : Ebar ≠ ⊥ := by
    intro hbot
    have hEleO : E ≤ O := by
      have hker : E ≤ q.ker := (Subgroup.map_eq_bot_iff E).mp hbot
      simpa [q, QuotientGroup.ker_mk'] using hker
    letI : Group.IsSolvable O := hOsolv
    haveI : Group.IsSolvable (E.subgroupOf O) := inferInstance
    have hEsolv : IsSolvable E :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe hEleO).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hEleO).surjective
    letI : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).2 hEne
    letI : Group.IsPerfect E := hEperf
    exact Group.IsPerfect.not_isSolvable E hEsolv
  have hEbarsn : Ebar.IsSubnormal := by
    dsimp [Ebar]
    exact hEsn.map (QuotientGroup.mk'_surjective O)
  letI : L.Normal := hLnormal
  let pi : (H ⧸ O) →* (H ⧸ O) ⧸ L := QuotientGroup.mk' L
  let I : Subgroup ((H ⧸ O) ⧸ L) := Ebar.map pi
  have hIperf : Group.IsPerfect I := by
    dsimp [I]
    letI : Group.IsPerfect Ebar := hEbarperf
    exact Group.IsPerfect.map pi
  have hQodd : Odd (Nat.card ((H ⧸ O) ⧸ L)) := by
    simpa only [Subgroup.index_eq_card] using hLindex
  have hQsolv : Group.IsSolvable ((H ⧸ O) ⧸ L) :=
    odd_order_theorem ((H ⧸ O) ⧸ L) hQodd
  have hIbot : I = ⊥ := by
    by_contra hIne
    letI : Group.IsSolvable ((H ⧸ O) ⧸ L) := hQsolv
    have hIsolv : Group.IsSolvable I := inferInstance
    letI : Nontrivial I := (Subgroup.nontrivial_iff_ne_bot I).2 hIne
    letI : Group.IsPerfect I := hIperf
    exact Group.IsPerfect.not_isSolvable I hIsolv
  have hEbarL : Ebar ≤ L := by
    have hker : Ebar ≤ pi.ker := (Subgroup.map_eq_bot_iff Ebar).mp hIbot
    simpa [pi, QuotientGroup.ker_mk'] using hker
  exact ⟨hEbarne, hEbarperf, hEbarsn, hEbarL⟩

end GorensteinWalter
