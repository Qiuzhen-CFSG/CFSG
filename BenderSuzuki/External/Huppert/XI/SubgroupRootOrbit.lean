module

public import Theory.SpecificGroups.Suzuki.InvolutionOrbit
public import Theory.SpecificGroups.Suzuki.OddSubgroups
public import BenderSuzuki.External.Huppert.XI.SubgroupRecognitionData
public import BenderSuzuki.External.Huppert.XI.SubgroupInvolutionCore

/-!
# Closure of a subgroup root orbit

For a nonsolvable doubly transitive Suzuki subaction, the Frobenius kernel
of a point stabilizer acts regularly on the remaining points. Its embedding
in an ambient Borel puts it in the ambient root group. The root intersection
therefore covers all remaining points, and its orbit together with the
distinguished point is invariant.

The unconditional theorem uses double transitivity of the simple
involution-generated core, proved in `SubgroupInvolutionCore` from the
independent strong-embedding theory. No subgroup classification of the
ambient Suzuki group is assumed.

Source: Huppert--Blackburn, *Finite Groups III*, XI.3.12(e), together with
the point-stabilizer Frobenius argument used in XI.11.15.
-/

namespace BenderSuzuki.External

open BenderSuzuki.MatrixGroups

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Double transitivity of the subgroup action, together with the Borel
Frobenius-kernel theorem, gives closure of the concrete root orbit. -/
public theorem suzukiSubgroup_root_orbit_invariant_of_two_pretransitive
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (hH : ¬ Group.IsSolvable H)
    (htwo : MulAction.IsMultiplyPretransitive H (suzukiInvolutionSubaction H) 2) :
    ∃ (a b : suzukiInvolutionSubaction H) (k : SuzukiMatrixGroup m),
      k • suzukiOvoidInfinity m = a.val ∧
      let R := ((SuzukiRootSubgroup m).map (MulAut.conj k).toMonoidHom).subgroupOf H
      ∀ g : H, ∀ x : SuzukiOvoid m,
        x = a.val ∨ x ∈ MulAction.orbit R b.val →
        g • x = a.val ∨ g • x ∈ MulAction.orbit R b.val := by
  obtain ⟨t, ht⟩ := suzukiSubgroup_exists_involution hm H hH
  let := suzukiInvolutionSubaction_nonempty hm H t ht
  let X := suzukiInvolutionSubaction H
  let a : X := Classical.choice inferInstance
  obtain ⟨b, hab, F, hFrob, _⟩ :=
    suzukiSubaction_frobeniusTwoKernel_exists hm H hH X htwo a
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m)
    (suzukiOvoidInfinity m) a.val
  let S := MulAction.stabilizer H a
  let f₀ : S →* SuzukiMatrixGroup m :=
    (MulAut.conj k⁻¹).toMonoidHom.comp (H.subtype.comp S.subtype)
  have hmem (r : S) : f₀ r ∈ SuzukiBorelSubgroup m := by
    rw [suzukiBorelSubgroup_eq_stabilizer m hm, MulAction.mem_stabilizer_iff]
    change (k⁻¹ * r.val.val * k) • suzukiOvoidInfinity m = suzukiOvoidInfinity m
    have hra : r.val.val • a.val = a.val := congrArg Subtype.val r.property
    rw [mul_smul, mul_smul, hk, hra, ← hk, inv_smul_smul]
  let f : S →* SuzukiBorelSubgroup m := f₀.codRestrict _ hmem
  have hFroot := suzukiBorel_frobeniusKernel_le_root hm hFrob f
  let R := ((SuzukiRootSubgroup m).map (MulAut.conj k).toMonoidHom).subgroupOf H
  have hFR (r : F) : r.val.val ∈ R := by
    refine ⟨f₀ r.val, hFroot r.property, ?_⟩
    change k * (k⁻¹ * r.val.val.val * k) * k⁻¹ = r.val.val.val
    group
  let := htwo
  let := suzukiInvolutionSubaction_isPretransitive hm H
  have htrans : MulAction.IsPretransitive S (SubMulAction.ofStabilizer H a) :=
    MulAction.is_one_pretransitive_iff.mp
      (SubMulAction.ofStabilizer.isMultiplyPretransitive.mp htwo)
  have hregular := huppert_blackburn_XI_regular_of_isComplement_stabilizer
    hFrob.isComplement' htrans
  have hcover (x : X) : x = a ∨ x.val ∈ MulAction.orbit R b.val := by
    by_cases hxa : x = a
    · exact Or.inl hxa
    obtain ⟨r, hr, _⟩ := hregular ⟨b, hab.symm⟩ ⟨x, hxa⟩
    exact Or.inr (MulAction.mem_orbit_iff.mpr
      ⟨⟨r.val.val, hFR r⟩,
        congrArg (fun z : SubMulAction.ofStabilizer H a => z.val.val) hr⟩)
  refine ⟨a, b, k, hk, ?_⟩
  change ∀ g : H, ∀ x : SuzukiOvoid m,
    x = a.val ∨ x ∈ MulAction.orbit R b.val →
      g • x = a.val ∨ g • x ∈ MulAction.orbit R b.val
  intro g x hx
  have hxX : x ∈ X := by
    rcases hx with rfl | hx
    · exact a.property
    · obtain ⟨r, rfl⟩ := MulAction.mem_orbit_iff.mp hx
      exact X.smul_mem (r : H) b.property
  rcases hcover (g • (⟨x, hxX⟩ : X)) with heq | hmem
  · exact Or.inl (congrArg Subtype.val heq)
  · exact Or.inr hmem

/-- The point together with the root-intersection orbit is invariant under
every nonsolvable Suzuki subgroup. This is the root-orbit closure input
consumed by `SubgroupOrbit`. -/
public theorem suzukiSubgroup_root_orbit_invariant
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (hH : ¬ Group.IsSolvable H) :
    ∃ (a b : suzukiInvolutionSubaction H) (k : SuzukiMatrixGroup m),
      k • suzukiOvoidInfinity m = a.val ∧
      let R := ((SuzukiRootSubgroup m).map (MulAut.conj k).toMonoidHom).subgroupOf H
      ∀ g : H, ∀ x : SuzukiOvoid m,
        x = a.val ∨ x ∈ MulAction.orbit R b.val →
        g • x = a.val ∨ g • x ∈ MulAction.orbit R b.val :=
  suzukiSubgroup_root_orbit_invariant_of_two_pretransitive hm H hH
    (suzukiInvolutionSubaction_two_pretransitive hm H hH)

end BenderSuzuki.External
