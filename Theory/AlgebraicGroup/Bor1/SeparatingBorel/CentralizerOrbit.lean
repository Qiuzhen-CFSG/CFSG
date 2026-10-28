module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.FiniteFixed
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.TwoBorels
/-!
# The two fixed points on the actual centralizer Borel orbit

Borel self-normalization identifies points of an orbit with their Borel
stabilizers. Torus-fixed orbit points therefore correspond to Borels containing
the torus. The source rank-one quotient construction gives exactly two such
Borels for the original nonsolvable codimension-one subtorus centralizer.

The final theorem is stated for the literal point action of that centralizer
and the inverse image of the original maximal torus. It applies directly to
its Chevalley projective Borel orbit; the orbit is not replaced by an abstract
rank-one model or an assumed fixed-point-count certificate.

Source: Borel, *Linear Algebraic Groups*, IV, 11.18 and 13.11(1),
`refs/KGroup/Bor1/Chapter4.tex`.
-/

public section
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup
variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {X : Type*} [MulAction (Variety.Point G) X]

private theorem exactly_two_fixed_orbit_of_two_borels
    (hG : Variety.IsConnected G) (T B C : ClosedSubgroup G)
    (hB : IsBorelSubgroup B) (hC : IsBorelSubgroup C) (hTB : T ≤ B) (hTC : T ≤ C)
    (hCB : C ≠ B)
    (htwo : ∀ D : ClosedSubgroup G, IsBorelSubgroup D → T ≤ D → D = B ∨ D = C)
    (x : X) (hstab : ∀ g : Variety.Point G, g • x = x ↔ g ∈ B.toSubgroup) :
    (∀ t : Variety.Point G, t ∈ T.toSubgroup → t • x = x) ∧
    ∃ y : X, (∃ g : Variety.Point G, g • x = y) ∧ y ≠ x ∧
      (∀ t : Variety.Point G, t ∈ T.toSubgroup → t • y = y) ∧
      ∀ z : X, (∃ g : Variety.Point G, g • x = z) →
        (∀ t : Variety.Point G, t ∈ T.toSubgroup → t • z = z) → z = x ∨ z = y := by
  have hfix (g a : Variety.Point G) : a • (g • x) = g • x ↔ a ∈ B.conjugate g := by
    rw [B.mem_conjugate_iff, ← hstab]
    constructor
    · intro ha
      have hh := congrArg (fun z : X => g⁻¹ • z) ha
      simpa only [mul_smul, inv_smul_smul] using hh
    · intro ha
      have hh := congrArg (fun z : X => g • z) ha
      simpa only [mul_smul, smul_inv_smul] using hh
  obtain ⟨g, hg⟩ := BorelGeometricConjugacy.conjugacy hB hC
  refine ⟨fun t ht => (hstab t).mpr (hTB ht), g • x, ⟨g, rfl⟩, ?_, ?_, ?_⟩
  · intro he
    apply hCB
    rw [hg]
    apply SetLike.coe_injective
    ext a
    change a ∈ B.conjugate g ↔ a ∈ B.toSubgroup
    rw [← hfix, he]
    exact hstab a
  · intro t ht
    apply (hfix g t).mpr
    rw [← hg]
    exact hTC ht
  · rintro z ⟨a, rfl⟩ hz
    have hTa : T ≤ B.conjugate a := fun t ht => (hfix a t).mp (hz t ht)
    rcases htwo (B.conjugate a) (hB.conjugate a) hTa with ha | ha
    · left
      have he := orbit_points_eq_of_conjugate_borels_eq hG B hB x hstab a 1
        (by rwa [ClosedSubgroup.conjugate_one])
      simpa only [one_smul] using he
    · right
      exact orbit_points_eq_of_conjugate_borels_eq hG B hB x hstab a g (ha.trans hg)

theorem centralizer_orbit_exactly_two_fixed_points
    (hG : Variety.IsConnected G) (S T : ClosedSubgroup G)
    (hS : IsSubtorus S) (hT : IsMaximalTorus T) (hST : S ≤ T)
    (hcodim : Variety.dimension S.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (hns : ¬ Group.IsSolvable (Variety.Point S.centralizer.carrierVariety))
    (B : ClosedSubgroup S.centralizer.carrierVariety) (hB : IsBorelSubgroup B)
    (hTB : S.centralizer.inclusion.closedSubgroupPreimage T ≤ B)
    {Y : Type*} [MulAction (Variety.Point S.centralizer.carrierVariety) Y]
    (x : Y) (hstab : ∀ g : Variety.Point S.centralizer.carrierVariety,
      g • x = x ↔ g ∈ B.toSubgroup) :
    (∀ t : Variety.Point S.centralizer.carrierVariety,
      t ∈ (S.centralizer.inclusion.closedSubgroupPreimage T).toSubgroup → t • x = x) ∧
    ∃ y : Y, (∃ g : Variety.Point S.centralizer.carrierVariety, g • x = y) ∧ y ≠ x ∧
      (∀ t : Variety.Point S.centralizer.carrierVariety,
        t ∈ (S.centralizer.inclusion.closedSubgroupPreimage T).toSubgroup → t • y = y) ∧
      ∀ z : Y, (∃ g : Variety.Point S.centralizer.carrierVariety, g • x = z) →
        (∀ t : Variety.Point S.centralizer.carrierVariety,
          t ∈ (S.centralizer.inclusion.closedSubgroupPreimage T).toSubgroup → t • z = z) →
        z = x ∨ z = y := by
  obtain ⟨C, hC, hTC, hCB, htwo⟩ :=
    centralizer_borels_exactly_two hG S T hS hT hST hcodim hns B hB hTB
  exact exactly_two_fixed_orbit_of_two_borels
    (SemisimpleCenterContainment.CartanGeometry.subtorus_centralizer_isConnected hG hS)
    _ B C hB hC hTB hTC hCB htwo x hstab

end Theory.AlgebraicGroup.Bor1.SeparatingBorel
