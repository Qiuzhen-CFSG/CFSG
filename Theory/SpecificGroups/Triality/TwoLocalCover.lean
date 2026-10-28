module

public import Theory.SpecificGroups.Triality.TwoLocalCover.Geometry
public import Theory.SpecificGroups.Triality.TwoLocalCover.ApartmentStabilizer
public import Theory.SpecificGroups.Triality.TwoLocalCover.Hexagon
public import Theory.Quasithin

/-!
# Triality normalizers from the parabolic hexagon

Every two-subgroup fixes an edge of the genuine parabolic coset graph. The
proved hexagon geometry and odd apartment fixers make the fixed subgraph of
every nonidentity two-subgroup a finite tree. The full normalizer fixes a
vertex of that tree and therefore conjugates into one of the two full root
parabolics.

This proves the normalizer-containment conclusion of finite Borel–Tits for
arbitrary nonidentity two-subgroups, hence for all maximal two-locals, at every
positive binary exponent, including q = 2. The conditional assembly lemmas
are retained; the final three theorems discharge all geometric premises using
the concrete BN-pair and opposition calculations. No simplicity, quasithinness
or even-characteristic assumption is needed. The additional radical-containment
clause of Borel–Tits is not asserted here.

Sources: GLS3 Theorem 3.1.3 and §§2.6.4–8; Aschbacher–Smith Theorem 0.1.2(1),
printed pp.3–4 (`refs/quasithin.pdf`). The elementary fixed-point subgroup and
quotient by its own center are exactly those of `Triality.Standard.Carrier`.
-/

public section
namespace Triality.Standard.TwoLocalCover

open Subgroup Parabolics TwoLocalGeometry GroupAction.EvenPolygon

/-- Conditional finite-building proof for all nonidentity two-subgroup
normalizers, not just normalizers of characteristic Sylow subgroups. -/
theorem normalizer_cover_of_hexagon (f : ℕ) (hf : 0 < f)
    (hgeometry : HexagonGeometry f hf) (htrans : ApartmentTranslates f hf)
    (hodd : Odd (Nat.card (fixingSubgroup (Carrier (binaryParameters f hf))
      (standardApartment f hf))))
    (R : Subgroup (Carrier (binaryParameters f hf)))
    (hR : R ≠ ⊥) (hRtwo : IsPGroup 2 R) :
    ∃ (g : Carrier (binaryParameters f hf)) (a : Node),
      (normalizer (R : Set (Carrier (binaryParameters f hf)))).map
        (MulAut.conj g).toMonoidHom ≤ parabolic (binaryParameters f hf) a := by
  obtain ⟨v, hv⟩ := normalizer_fixed_vertex_of_fixed_edge
    (hgeometry.toEvenPolygonAction htrans hodd) R hR hRtwo
    (exists_fixed_edge f hf R hRtwo)
  obtain ⟨g, hg⟩ := CosetGeometry.conjugate_le_of_fixed_vertex
    (parabolic (binaryParameters f hf)) (normalizer (R : Set _)) v hv
  exact ⟨g, v.type, hg⟩

/-- All two-locals are covered once the two independent geometric inputs
(hexagon incidence and odd apartment fixers) are discharged. -/
theorem twoLocal_cover_of_hexagon (f : ℕ) (hf : 0 < f)
    (hgeometry : HexagonGeometry f hf) (htrans : ApartmentTranslates f hf)
    (hodd : Odd (Nat.card (fixingSubgroup (Carrier (binaryParameters f hf))
      (standardApartment f hf))))
    (M : Subgroup (Carrier (binaryParameters f hf))) (hM : IsTwoLocal M) :
    ∃ (g : Carrier (binaryParameters f hf)) (a : Node),
      M.map (MulAut.conj g).toMonoidHom ≤ parabolic (binaryParameters f hf) a := by
  obtain ⟨R, hR, hRtwo, rfl⟩ := hM
  exact normalizer_cover_of_hexagon f hf hgeometry htrans hodd R hR hRtwo

/-- The exact coverage premise consumed by the triality quasithin assembly,
conditional only on the explicit hexagon and apartment-fixer calculations. -/
theorem maximalTwoLocal_cover_of_hexagon (f : ℕ) (hf : 0 < f)
    (hgeometry : HexagonGeometry f hf) (htrans : ApartmentTranslates f hf)
    (hodd : Odd (Nat.card (fixingSubgroup (Carrier (binaryParameters f hf))
      (standardApartment f hf))))
    (M : Subgroup (Carrier (binaryParameters f hf))) (hM : IsMaximalTwoLocal M) :
    ∃ (g : Carrier (binaryParameters f hf)) (a : Node),
      M.map (MulAut.conj g).toMonoidHom ≤ parabolic (binaryParameters f hf) a :=
  twoLocal_cover_of_hexagon f hf hgeometry htrans hodd M hM.1

/-- Every nonidentity two-subgroup normalizer in the genuine binary triality
carrier conjugates into a full root parabolic. All geometric premises are
discharged, including at q = 2. -/
theorem normalizer_cover (f : ℕ) (hf : 0 < f)
    (R : Subgroup (Carrier (binaryParameters f hf)))
    (hR : R ≠ ⊥) (hRtwo : IsPGroup 2 R) :
    ∃ (g : Carrier (binaryParameters f hf)) (a : Node),
      (normalizer (R : Set (Carrier (binaryParameters f hf)))).map
        (MulAut.conj g).toMonoidHom ≤ parabolic (binaryParameters f hf) a :=
  normalizer_cover_of_hexagon f hf (hexagonGeometry f hf) (apartmentTranslates f hf)
    (standardApartment_fixer_odd f hf) R hR hRtwo

/-- Every two-local in the genuine binary triality carrier conjugates into
one of its two full root parabolics. -/
theorem twoLocal_cover (f : ℕ) (hf : 0 < f)
    (M : Subgroup (Carrier (binaryParameters f hf))) (hM : IsTwoLocal M) :
    ∃ (g : Carrier (binaryParameters f hf)) (a : Node),
      M.map (MulAut.conj g).toMonoidHom ≤ parabolic (binaryParameters f hf) a := by
  obtain ⟨R, hR, hRtwo, rfl⟩ := hM
  exact normalizer_cover f hf R hR hRtwo

/-- Unconditional coverage of arbitrary maximal two-locals by genuine full
parabolics, in the exact form consumed by the triality quasithin assembly. -/
theorem maximalTwoLocal_cover (f : ℕ) (hf : 0 < f)
    (M : Subgroup (Carrier (binaryParameters f hf))) (hM : IsMaximalTwoLocal M) :
    ∃ (g : Carrier (binaryParameters f hf)) (a : Node),
      M.map (MulAut.conj g).toMonoidHom ≤ parabolic (binaryParameters f hf) a :=
  twoLocal_cover f hf M hM.1

end Triality.Standard.TwoLocalCover
