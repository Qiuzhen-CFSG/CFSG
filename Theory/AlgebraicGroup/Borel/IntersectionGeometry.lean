module

public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.Transport

/-!
Borel-intersection geometry for GLS3, Theorem 1.11.4.

The conditional assembly below reduces the requested conclusions to three
geometric inputs: conjugacy of Borels, B-N-B coverage for an actual Borel and
ambient maximal torus, and intersection/opposite geometry for Borels containing
a fixed maximal torus. Conjugacy transports an initial Borel/torus pair into
an arbitrary Borel. In a Bruhat factorization `b * n * c`, the right factor
fixes the Borel, and conjugation by `b` transports the common torus and the
connected intersection from normalizer position.

These inputs remain explicit hypotheses: this module does not yet assert the
unrestricted source theorem. In particular, it does not use the unresolved
numbered Borel-conjugacy or root-structure theorems as proofs of the inputs.

Sources: GLS3, Theorem 1.11.4 and the proof of Theorem 3.1.1(b);
Borel, *Linear Algebraic Groups*, §§11.1 and 14.13.
-/

universe u

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : Variety k} [AlgebraicGroup G]

/-- Borel conjugacy carries the initial ambient maximal torus into any Borel. -/
public theorem exists_maximalTorus_le_borel_of_conjugacy
    (hconj : ∀ B C : ClosedSubgroup G,
      IsBorelSubgroup B → IsBorelSubgroup C →
        ∃ g : Variety.Point G, C = B.conjugate g)
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B) :
    ∃ T : ClosedSubgroup G, IsMaximalTorus T ∧ T ≤ B := by
  obtain ⟨C, T, hC, hT, hTC⟩ := exists_borel_maximalTorus_pair (G := G)
  obtain ⟨g, rfl⟩ := hconj C B hC hB
  exact ⟨T.conjugate g, conjugate_isMaximalTorus hT g, conjugate_le hTC g⟩

/-- Conditional assembly of the common-torus and connected-intersection
conclusions. The geometric inputs are Borel conjugacy, actual B-N-B coverage,
and connectedness in normalizer position. -/
public theorem intersection_geometry_of_conjugacy_bruhat_and_fixedTorus
    (hconj : ∀ B C : ClosedSubgroup G,
      IsBorelSubgroup B → IsBorelSubgroup C →
        ∃ g : Variety.Point G, C = B.conjugate g)
    (hbruhat : ∀ B T : ClosedSubgroup G,
      IsBorelSubgroup B → IsMaximalTorus T → T ≤ B →
        ∀ g : Variety.Point G, ∃ b n c : Variety.Point G,
          b ∈ B.toSubgroup ∧ n ∈ T.normalizer.toSubgroup ∧
            c ∈ B.toSubgroup ∧ g = b * n * c)
    (hfixed : ∀ B T : ClosedSubgroup G,
      IsBorelSubgroup B → IsMaximalTorus T → T ≤ B →
        ∀ n : Variety.Point G, n ∈ T.normalizer.toSubgroup →
          _root_.IsConnected (B.inter (B.conjugate n) : Set (Variety.Point G)))
    (B₀ B₁ : ClosedSubgroup G)
    (hB₀ : IsBorelSubgroup B₀) (hB₁ : IsBorelSubgroup B₁) :
    _root_.IsConnected (B₀.inter B₁ : Set (Variety.Point G)) ∧
      ∃ T : ClosedSubgroup G, IsMaximalTorus T ∧ T ≤ B₀ ∧ T ≤ B₁ := by
  obtain ⟨T, hT, hTB⟩ := exists_maximalTorus_le_borel_of_conjugacy hconj B₀ hB₀
  obtain ⟨g, rfl⟩ := hconj B₀ B₁ hB₀ hB₁
  obtain ⟨b, n, c, hb, hn, hc, rfl⟩ := hbruhat B₀ T hB₀ hT hTB g
  rw [conjugate_of_double_coset B₀ b n c hc]
  exact ⟨inter_connected_of_normal_form B₀ b n hb (hfixed B₀ T hB₀ hT hTB n hn),
    T.conjugate b, common_maximalTorus_of_normal_form B₀ T hT hTB b n hb hn⟩

/-- Conditional assembly of opposite-Borel existence from geometry at a fixed
ambient maximal torus. -/
public theorem exists_opposite_of_conjugacy_and_fixedTorus
    (hconj : ∀ B C : ClosedSubgroup G,
      IsBorelSubgroup B → IsBorelSubgroup C →
        ∃ g : Variety.Point G, C = B.conjugate g)
    (hopposite : ∀ B T : ClosedSubgroup G,
      IsBorelSubgroup B → IsMaximalTorus T → T ≤ B →
        ∃ C : ClosedSubgroup G, IsBorelSubgroup C ∧ B.inter C = T)
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B) :
    ∃ C : ClosedSubgroup G, IsBorelSubgroup C ∧ IsMaximalTorus (B.inter C) := by
  obtain ⟨T, hT, hTB⟩ := exists_maximalTorus_le_borel_of_conjugacy hconj B hB
  obtain ⟨C, hC, hBC⟩ := hopposite B T hB hT hTB
  exact ⟨C, hC, hBC.symm ▸ hT⟩

end Theory.AlgebraicGroup.BorelIntersectionGeometry
