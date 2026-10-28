module

public import Theory.SpecificGroups.ReeTwo.Core
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Faithfulness detected by the last Ree core root

The polynomial multiplication shows that the core center consists of the
identity and root 12. Every nontrivial normal subgroup of this two-group
meets its center. Consequently a homomorphism from the core is injective
as soon as root 12 survives.

The multiplication is Shinoda's ten-root core at q = 2, (2.3), pp.81–82;
the normal-subgroup argument is the usual center theorem for finite p-groups.
-/

namespace ReeTwo.Core

private theorem mul_eq (g h : Core) : g * h = mul g h := rfl

/-- Only the last root can be a nonidentity central element of the core. -/
public theorem eq_one_or_last_root_of_central (g : Core)
    (hc : ∀ i, g * root i = root i * g) : g = 1 ∨ g = root 9 := by
  have h4 : g.b4 = 0 := by
    simpa [mul_eq, mul, root, ofCoords] using congrArg Core.b7 (hc 0)
  have h3 : g.b3 = 0 := by
    simpa [mul_eq, mul, root, ofCoords, h4] using congrArg Core.b6 (hc 0)
  have h2 : g.b2 = 0 := by
    simpa [mul_eq, mul, root, ofCoords, h3] using congrArg Core.b5 (hc 0)
  have h8 : g.b8 = 0 := by
    simpa [mul_eq, mul, root, ofCoords, h2, h3, h4] using congrArg Core.b9 (hc 0)
  have h7 : g.b7 = 0 := by
    simpa [mul_eq, mul, root, ofCoords, h2, h3, h4] using congrArg Core.b9 (hc 1)
  have h0 : g.b0 = 0 := by
    simpa [mul_eq, mul, root, ofCoords] using (congrArg Core.b5 (hc 2)).symm
  have h1 : g.b1 = 0 := by
    simpa [mul_eq, mul, root, ofCoords] using (congrArg Core.b6 (hc 2)).symm
  have h6 : g.b6 = 0 := by
    simpa [mul_eq, mul, root, ofCoords, h0, h1] using congrArg Core.b9 (hc 3)
  have h5 : g.b5 = 0 := by
    simpa [mul_eq, mul, root, ofCoords, h0, h1] using congrArg Core.b9 (hc 4)
  have h9 : g.b9 = 0 ∨ g.b9 = 1 := (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) g.b9
  rcases h9 with h9 | h9
  · left; apply Core.ext <;> assumption
  · right; apply Core.ext <;> simp_all [root, ofCoords]

/-- A map of the core is faithful if the central involution survives. -/
public theorem hom_injective_of_last_root {H : Type*} [Group H]
    (f : Core →* H) (hz : f (root 9) ≠ 1) : Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  by_contra hne
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 Core) := ⟨IsPGroup.of_card (n := 10) (by simpa using card)⟩
  let _ : Nontrivial f.ker := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨z, hzne, hzcenter⟩ := exists_nontrivial_center_mem_normal f.ker (p := 2)
  have hc : ∀ i, (z : Core) * root i = root i * z := fun i =>
    (Subgroup.mem_center_iff.mp hzcenter (root i)).symm
  rcases eq_one_or_last_root_of_central z hc with h | h
  · exact hzne (Subtype.ext h)
  · exact hz (h ▸ z.property)

end ReeTwo.Core
