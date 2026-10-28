module

public import Theory.SpecificGroups.Suzuki.InvolutionOrbit
public import Theory.SpecificGroups.Suzuki.OddSubgroups
public import BenderSuzuki.External.Huppert.XI.SubgroupRootOrbit

/-!
# The orbit construction for nonsolvable Suzuki subgroups

The involution fixed points give a canonical nonempty transitive subaction
for a nonsolvable subgroup. The lower modules prove nonemptiness by
solvability of odd-order subgroups and transitivity by Sylow conjugacy.

The conditional assembly below isolates the additional input needed for
double transitivity: a subgroup fixing one point has an orbit whose union
with that point is invariant under the whole subgroup. Transitivity then
identifies this union with the involution orbit. In the intended application
the point-fixing subgroup is the intersection with an ambient root group.
`SubgroupRootOrbit` proves this invariance using the simple subgroup generated
by the involutions and the independent strong-embedding theory. The final
theorem assembles a nonempty doubly transitive subaction without assuming
subgroup classification or transferring ambient double transitivity.

Source: Huppert--Blackburn, *Finite Groups III*, XI.3.12(e), p. 194, citing
Suzuki, *On a class of doubly transitive groups*, Ann. Math. 75 (1962).
-/

namespace BenderSuzuki.External

open BenderSuzuki.MatrixGroups

private theorem two_pretransitive_of_point_complement_orbit
    {G Y : Type*} [Group G] [MulAction G Y] [MulAction.IsPretransitive G Y]
    (a b : Y) (R : Subgroup G) (hfix : ∀ r : R, (r : G) • a = a)
    (hcover : ∀ x : Y, x ≠ a → ∃ r : R, (r : G) • b = x) :
    MulAction.IsMultiplyPretransitive G Y 2 := by
  apply MulAction.is_two_pretransitive_iff.mpr
  intro x y z w hxy hzw
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x a
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G z a
  have hgy : g • y ≠ a := by
    intro heq
    exact hxy ((MulAction.injective g) (hg.trans heq.symm))
  have hhw : h • w ≠ a := by
    intro heq
    exact hzw ((MulAction.injective h) (hh.trans heq.symm))
  obtain ⟨r, hr⟩ := hcover (g • y) hgy
  obtain ⟨s, hs⟩ := hcover (h • w) hhw
  refine ⟨h⁻¹ * (s : G) * (r : G)⁻¹ * g, ?_, ?_⟩
  · simp only [mul_smul]
    rw [hg, show (r : G)⁻¹ • a = a from hfix r⁻¹, hfix s]
    exact inv_smul_eq_iff.mpr hh.symm
  · simp only [mul_smul]
    rw [← hr, inv_smul_smul, hs, inv_smul_smul]

/-- The canonical involution subaction of a nonsolvable subgroup is nonempty. -/
public theorem suzukiInvolutionSubaction_nonempty_of_not_isSolvable
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (hH : ¬ Group.IsSolvable H) : Nonempty (suzukiInvolutionSubaction H) := by
  obtain ⟨t, ht⟩ := suzukiSubgroup_exists_involution hm H hH
  exact suzukiInvolutionSubaction_nonempty hm H t ht

/-- An invariant union of a fixed point and an orbit of a point-fixing
subgroup supplies the missing double transitivity. The invariance hypothesis
is the genuine subgroup-generation input, not an ambient-action transfer. -/
public theorem suzukiInvolutionSubaction_two_pretransitive_of_orbit_invariant
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (a b : suzukiInvolutionSubaction H) (R : Subgroup H)
    (hfix : ∀ r : R, (r : H) • a = a)
    (hinvariant : ∀ g : H, ∀ x : SuzukiOvoid m,
      x = a.val ∨ x ∈ MulAction.orbit R b.val →
      g • x = a.val ∨ g • x ∈ MulAction.orbit R b.val) :
    MulAction.IsMultiplyPretransitive H (suzukiInvolutionSubaction H) 2 := by
  let := suzukiInvolutionSubaction_isPretransitive hm H
  have hcover (x : suzukiInvolutionSubaction H) (hx : x ≠ a) :
      ∃ r : R, (r : H) • b = x := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H a x
    have hgval : g • a.val = x.val := congrArg Subtype.val hg
    have hmem := hinvariant g a.val (Or.inl rfl)
    rw [hgval] at hmem
    rcases hmem with heq | hmem
    · exact False.elim (hx (Subtype.ext heq))
    · obtain ⟨r, hr⟩ := MulAction.mem_orbit_iff.mp hmem
      exact ⟨r, Subtype.ext hr⟩
  exact two_pretransitive_of_point_complement_orbit a b R hfix hcover

/-- Assembly with the concrete root-group intersection. Only the invariance
of the root orbit union remains to be supplied by subgroup generation. -/
public theorem suzukiSubgroup_exists_two_pretransitive_of_root_orbit_invariant
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (hroot : ∃ (a b : suzukiInvolutionSubaction H) (k : SuzukiMatrixGroup m),
      k • suzukiOvoidInfinity m = a.val ∧
      let R := ((SuzukiRootSubgroup m).map (MulAut.conj k).toMonoidHom).subgroupOf H
      ∀ g : H, ∀ x : SuzukiOvoid m,
        x = a.val ∨ x ∈ MulAction.orbit R b.val →
        g • x = a.val ∨ g • x ∈ MulAction.orbit R b.val) :
    ∃ X : SubMulAction H (SuzukiOvoid m),
      Nonempty X ∧ MulAction.IsMultiplyPretransitive H X 2 := by
  obtain ⟨a, b, k, hk, hinvariant⟩ := hroot
  let R := ((SuzukiRootSubgroup m).map (MulAut.conj k).toMonoidHom).subgroupOf H
  refine ⟨suzukiInvolutionSubaction H, ⟨a⟩,
    suzukiInvolutionSubaction_two_pretransitive_of_orbit_invariant hm H a b R ?_
      hinvariant⟩
  intro r
  apply Subtype.ext
  change (r.val.val : SuzukiMatrixGroup m) • a.val = a.val
  obtain ⟨u, hu, heq⟩ := r.property
  change k * u * k⁻¹ = r.val.val at heq
  rw [← hk, ← heq]
  simp only [mul_smul, inv_smul_smul, suzukiRootSubgroup_fix_infinity m hm u hu]

/-- Every nonsolvable Suzuki subgroup has a nonempty doubly transitive ovoid
subaction. The root-orbit closure comes from the simple involution-generated
core and strong embedding, independently of Suzuki subgroup classification. -/
public theorem suzukiSubgroup_exists_two_pretransitive
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (hH : ¬ Group.IsSolvable H) :
    ∃ X : SubMulAction H (SuzukiOvoid m),
      Nonempty X ∧ MulAction.IsMultiplyPretransitive H X 2 :=
  suzukiSubgroup_exists_two_pretransitive_of_root_orbit_invariant hm H
    (suzukiSubgroup_root_orbit_invariant hm H hH)

end BenderSuzuki.External
