module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.Elementary
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic

/-!+# Contracts for the marked normalizer construction

These contracts separate three source arguments so that their proofs can
proceed with earlier witnesses explicit. `SymmetricNormalizerData` requires
an actual isomorphism with Aut(A₆), compatible on the whole marked S₆.
`M10NormalizerGeometry` records the marked subgroup and its literal
nine-group normalizer, together with the semidihedral complement and the
involution used in the double-coset calculation. In particular its quaternion
intersection distinguishes the required extension from the other extensions
of A₆. `NormalizerCubeData` is the local input before the adjustment r ↦ br;
it asserts neither the braid relation nor the existence of the final subgroup.

No existence theorem for these contracts is asserted here. Their producers
must discharge all their fields from the earlier source hypotheses. The final
assembly remains in `MarkedNormalizers`.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemmas 4.8–4.9 and the local calculation in 4.10, pp.41–42.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup

open Subgroup DoubleCoset

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h}

/-- The full normalizer, with the original embedding of the symmetric group. -/
public structure SymmetricNormalizerData (s : SymmetricSixData h a) where
  equiv : normalizer (s.S : Set G) ≃* AlternatingSix.ShadowLocal.AutA6
  on_s : ∀ x : s.S,
    equiv ⟨x, s.S.le_normalizer x.property⟩ =
      AlternatingSix.ShadowLocal.permutationAction (s.equiv x)

/-- The marked M₁₀ geometry inside the full automorphism normalizer.
The subgroup K is defined as L ∩ N_G(D), never an unrelated group of order 72.
The complement P contains the distinguished involution z. -/
public structure M10NormalizerGeometry (s : SymmetricSixData h a) where
  L : Subgroup G
  L_le : L ≤ normalizer (s.S : Set G)
  D_le : s.markedNine ≤ L
  card_L : Nat.card L = 720
  card_K : Nat.card (s.markedK L) = 72
  transitive : MulAction.IsMultiplyPretransitive L (L ⧸ (s.markedK L).subgroupOf L) 3
  z_normalizes : z ∈ normalizer (L : Set G)
  z_not_mem : z ∉ L
  P : Subgroup G
  card_P : Nat.card P = 16
  semidihedral : ∃ p q : P, orderOf p = 8 ∧ orderOf q = 2 ∧
    q * p * q⁻¹ = p ^ 3 ∧ zpowers p ⊔ zpowers q = ⊤
  intersection : normalizer (s.S : Set G) ⊓ normalizer (s.markedNine : Set G) =
    s.markedNine ⊔ P
  disjoint : Disjoint s.markedNine P
  z_mem_P : z ∈ P
  center_P : (center P).map P.subtype = zpowers (s.u * z)
  quaternion : Nonempty (↥(P ⊓ L) ≃* QuaternionGroup 2)
  b_mem_K : s.u * z ∈ s.markedK L
  r : G
  r_mem : r ∈ L
  r_sq : r * r = 1
  r_not_mem_P : r ∉ P
  r_normalizes_P : r ∈ normalizer (P : Set G)
  cover : ∀ l ∈ L, l ∈ s.markedK L ∨ l ∈ doubleCoset r (s.markedK L) (s.markedK L)

/-- The exact local obstruction to the braid relation, before choosing r or br.
The cube alternative is stronger than merely knowing that vr has order six:
the involution in that case must be the marked b = uz. -/
public structure NormalizerCubeData (s : SymmetricSixData h a)
    (m : M10NormalizerGeometry s) where
  v : G
  v_mem : v ∈ normalizer (s.markedNine : Set G)
  v_sq : v * v = 1
  v_normalizes : v ∈ normalizer (s.markedK m.L : Set G)
  v_commutes_b : Commute (s.u * z) v
  vz_cube : (v * z) ^ 3 = 1
  vr_cube : (v * m.r) ^ 3 = 1 ∨ (v * m.r) ^ 3 = s.u * z

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
