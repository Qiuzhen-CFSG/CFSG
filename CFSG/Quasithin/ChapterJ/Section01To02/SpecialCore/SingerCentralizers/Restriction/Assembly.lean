module

public import Theory.Representation.PSL3Two.SingerRestriction.Assembly
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Restriction.Orbits
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Restriction.FiveSpace
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Restriction.CoprimeConsequences
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Suzuki

/-!
# The assembled Singer restriction in the original Ru1 coordinates

The fixed four-group, its cubic commutator and orbit, and the natural Singer
orbit are proved for the literal source subgroups. The exact Steinberg
stabilizer is also expressed through the original common quotient map.
`SingerChoice.fiveSpace` supplies the displacement decomposition and cubic
preservation for the actual Singer and cubic images.

The final application discharges the fixed-core and natural-orbit premises
of the Suzuki argument. Transport of the five-space calculation to C_S(s),
the full centralizer and Sylow conclusions belong to the centralizer assembly.
The explicit cubic order is supplied by the Singer-choice construction;
the independent full-commutator premise is J.2.3(6).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma J.2.3(1),(3)–(5), printed pp.433–434 (PDF pp.444–445).
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterJ.SpecialCore
variable {G : Type*} [Group G] [Finite G]

/-- The fixed-four-group conclusions of J.2.3(1), together with both literal
conjugation orbits needed by its centralizer argument. -/
theorem SingerChoice.restriction (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) (hB : Nat.card (cubicSubgroup d B) = 3) :
    Nonempty (fixedCore d c.B7 ≃* Multiplicative (ZMod 2 × ZMod 2)) ∧
    ⁅fixedCore d c.B7, cubicSubgroup d B⁆ = fixedCore d c.B7 ∧
    Disjoint (fixedCore d c.B7) d.V ∧
    (∀ u v : G, u ∈ fixedCore d c.B7 → v ∈ fixedCore d c.B7 →
      u ≠ 1 → v ≠ 1 → ∃ b ∈ cubicSubgroup d B, b * u * b⁻¹ = v) ∧
    (∀ v w : G, v ∈ d.V → w ∈ d.V →
      v ≠ 1 → w ≠ 1 → ∃ b ∈ c.B7, b * v * b⁻¹ = w) :=
  ⟨⟨c.fixedCoreEquivFour d B⟩, c.fixedCore_commutator_cubic d B hB,
    c.fixedCore_disjoint_V d B, c.transitive_fixedCore d B hB, c.transitive_V d B⟩

/-- The exact model stabilizer at a source fixed-core element, using its
original Steinberg coordinates and the original Ru1 quotient map. -/
theorem SingerChoice.steinberg_stabilizer_fixedCore
    (d : TypeRuSetup G) (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1) (l : d.L) :
    BinaryLinearThree.S (d.ru1.quotientMap l)
        (d.ru1.steinberg.coordinates ⟨s, hs.1⟩).toAdd =
      (d.ru1.steinberg.coordinates ⟨s, hs.1⟩).toAdd ↔
        d.ru1.quotientMap l ∈ singerImage d B c := by
  have hfixed : (d.ru1.steinberg.coordinates ⟨s, hs.1⟩).toAdd ∈
      fixedSpace BinaryLinearThree.S (singerImage d B c) := by
    rw [← c.fixedCoreEquiv_apply d B ⟨s, hs⟩]
    exact (c.fixedCoreEquiv d B ⟨s, hs⟩).toAdd.property
  have hzero : (d.ru1.steinberg.coordinates ⟨s, hs.1⟩).toAdd ≠ 0 := by
    intro he
    have hV : s ∈ d.V :=
      (d.ru1.steinberg.coordinates_eq_one_iff ⟨s, hs.1⟩).mp he
    exact hs1 ((c.fixedCore_disjoint_V d B).le_bot ⟨hs, hV⟩)
  exact BinaryLinearThree.SingerRestriction.stabilizer_order_seven
    (singerImage d B c) (singerImage_card d B c) _ hfixed hzero _

/-- Application to the existing full Suzuki conclusion. Only the independent
full-commutator theorem and the parent's transport of the moving five-space
remain explicit; all fixed-core and natural-orbit premises are discharged. -/
theorem SingerChoice.movingCore_suzuki_from_restriction
    (d : TypeRuSetup G) (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (hB : Nat.card (cubicSubgroup d B) = 3)
    (hfull : ∀ t : d.S, (t : G) ∉ d.V → ⁅zpowers (t : G), d.S⁆ = d.V)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1)
    (hn : cubicSubgroup d B ≤ normalizer (movingCore d c.B7 s))
    (hMtrans : ∀ x ∈ movingCore d c.B7 s, ∀ y ∈ movingCore d c.B7 s,
      x ∉ d.V → y ∉ d.V → ∃ a ∈ c.B7, (a * x * a⁻¹)⁻¹ * y ∈ d.V) :
    IsPGroup 2 (movingCore d c.B7 s) ∧
    ¬ IsMulCommutative (movingCore d c.B7 s) ∧
    _root_.commutator (movingCore d c.B7 s) = center (movingCore d c.B7 s) ∧
    ∃ A : Subgroup (MulAut (movingCore d c.B7 s)), IsCyclic A ∧
      ∀ x y : movingCore d c.B7 s, orderOf x = 2 → orderOf y = 2 →
        ∃ a ∈ A, a x = y := by
  apply c.movingCore_suzuki_of_orbits d B hfull (c.fixedCore_commutative d B)
    (c.fixedCore_disjoint_V d B) s hs hs1 hn
  · intro x hx hx1
    exact c.transitive_fixedCore d B hB s x hs hx hs1 hx1
  · intro x hx y hy hx1 hy1
    exact c.transitive_V d B x y hx hy hx1 hy1
  · exact hMtrans

end CFSG.Quasithin.ChapterJ.SpecialCore
