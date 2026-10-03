module
public import Stellmacher.MainDefs
public import Stellmacher.Recognition.Sylow32SelfNormalizer
public import Theory.SpecificGroups.AffineEight.SylowTransfer

/-!
# Excluding the order32 maximal C₂ × S₄ branch

A finite nonsolvable simple N₂ group cannot have a Sylow two-subgroup of
order32 and a maximal two-local subgroup isomorphic to C₂ × S₄. The proof
uses finiteness, simplicity, nonsolvability and the stated local data;
the N₂ parameter is retained in the incoming classification interface.

The actual local embedding and its proved index-two extension comparison
identify the supplied Sylow with the affine group of the cyclic group of
order eight. The mapped elementary eight core and its full normalizer make
this Sylow self-normalizing. The affine transfer theorem then makes the
ambient derived subgroup proper, contrary to simplicity and nonsolvability.
All group identifications and action maps are constructed by the imported
proofs; no table of groups of order32 or global classification is assumed.

This excludes case(c) of Stellmacher's Theorem2. The global transfer argument
is Andersen–Oliver–Ventura, Fusion systems and amalgams, Math. Z.274 (2013),
Proposition2.3(b), in its proved ordinary-group form. It replaces the two
extra-Z steps in Kurzweil–Stellmacher, Chapter12, printed p367.
-/

namespace Stellmacher.Recognition
open scoped IsMulCommutative

/-- The remaining order32 maximal C₂ × S₄ alternative is impossible in a
finite nonsolvable simple N₂ group. -/
public theorem not_sylow32_maximal_c2s4
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (_hN : IsNTwoGroup G)
    (S : Sylow 2 G) (hOrder : Nat.card S = 2 ^ 5) (P : Subgroup G)
    (hP : IsMaximalTwoLocal P)
    (hModel : Nonempty (P ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) : False := by
  obtain ⟨i, hi, hindex, hC, hN, _⟩ := sylow32_c2s4_embedding S hOrder P hP hModel
  obtain ⟨e, _⟩ :=
    CyclicTwoDihedralFour.exists_mulEquiv_affineEight i hi hindex hC.symm hN
  have hproper := AffineEight.not_perfect_of_sylow S
    (sylow32_normalizer_eq_self S hOrder P hP hModel) e
  rcases (inferInstance : (commutator G).Normal).eq_bot_or_eq_top with hbot | htop
  · let : IsMulCommutative G := (commutator_eq_bot_iff G).mp hbot
    exact hns inferInstance
  · exact hproper htop

end Stellmacher.Recognition
