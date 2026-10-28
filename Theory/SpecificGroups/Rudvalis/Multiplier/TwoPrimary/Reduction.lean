module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.Definitions
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.Max4Perfect
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.Transfer
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow

/-!
# Restriction and assembly for the Rudvalis two-primary upper bound

The actual max4 subgroup contains an ambient Sylow two-subgroup and is
perfect. Its full preimage in a perfect central cover with two-group kernel
is therefore perfect, by central transfer. Restriction preserves the whole
kernel, including its group structure. The local exponent bound then supplies
the premise of the independent ambient involution-lifting argument, which
in turn supplies the involutory lift required by the sharper local bound.

Both local calculations remain explicit inputs. This module does not claim
the unconditional multiplier bound. Source: Aschbacher--Smith I.1.3(1),
printed p.407.
-/

namespace Rudvalis.Multiplier.TwoPrimary
open SylowOvergroups PerfectCentralCovering Subgroup

/-- The exact max4 subgroup has odd index in the actual Rudvalis model. -/
public theorem max4_index_odd : ¬ 2 ∣ max4.index := by
  obtain ⟨S, hS⟩ := max4ContainsSylow
  exact fun h => S.not_dvd_index (h.trans (index_dvd_of_le hS))

/-- The local exponent bound and ambient fusion bound imply the full kernel
upper bound for a perfect central cover whose kernel is a two-group. -/
public theorem kernel_card_le_two_of_local_bounds
    (hlocal : Max4CoverBounds) (hlift : FirstInvolutionLift)
    {E : Type} [Group E] [Finite E] (f : Cover E Model)
    (hp : IsPGroup 2 f.toMonoidHom.ker) : Nat.card f.toMonoidHom.ker ≤ 2 := by
  let : Group.IsPerfect E := f.isPerfect
  let : Group.IsPerfect max4 := max4_isPerfect
  let R := max4.comap f.toMonoidHom
  let g := f.toMonoidHom.subgroupComap max4
  have hg : Function.Surjective g :=
    f.toMonoidHom.subgroupComap_surjective_of_surjective max4 f.surjective
  have hc : g.ker ≤ center R := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    have hx' : (x : E) ∈ f.toMonoidHom.ker := congrArg Subtype.val hx
    exact Subtype.ext (mem_center_iff.mp (f.ker_le_center hx') y)
  let c : Cover R max4 := {
    toMonoidHom := g
    surjective := hg
    isPerfect := perfect_preimage_of_central_pGroup_kernel f.toMonoidHom f.surjective
      f.ker_le_center hp max4 max4_index_odd
    ker_le_center := hc }
  let e : g.ker ≃* f.toMonoidHom.ker := subgroupComapKernelEquiv f.toMonoidHom max4
  obtain ⟨hexponent, hbound⟩ := hlocal R c (hp.of_equiv e.symm)
  have hker2 (z : f.toMonoidHom.ker) : z ^ 2 = 1 := by
    apply e.symm.injective
    simpa only [map_pow, map_one] using
      (Subtype.ext (hexponent (e.symm z).val (e.symm z).property) : e.symm z ^ 2 = 1)
  have he (z : E) (hz : z ∈ f.toMonoidHom.ker) : z ^ 2 = 1 :=
    congrArg Subtype.val (hker2 ⟨z, hz⟩)
  obtain ⟨x, hx, hx2⟩ := hlift E f he
  let y : R := ⟨x, by
    change f.toMonoidHom x ∈ max4
    rw [hx]
    exact max4First.property⟩
  have hy : c.toMonoidHom y = max4First := Subtype.ext hx
  have hy2 : y ^ 2 = 1 := Subtype.ext hx2
  calc
    Nat.card f.toMonoidHom.ker = Nat.card g.ker := (Nat.card_congr e.toEquiv).symm
    _ ≤ 2 := hbound ⟨y, hy, hy2⟩

end Rudvalis.Multiplier.TwoPrimary
