module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.Exchange

/-!+# The marked root configuration for the quaternion exchange

These intermediate contracts separate the geometry inside the marked S₆
from the quaternion calculation in the centralizer of the pivot b. Neither
contract asserts the existence of its witnesses. The root w has square b,
lies in Q_b, and is inverted by the selected involution u outside Q_b.
The involution z lies in Q_b, commutes with w, and is different from b.

The marked geometry identifies the literal even fusion subgroups with
⟨b, uwz⟩ and ⟨b, uz⟩ at z and zb, respectively. These are the identifications
in the first paragraph of source 4.8; its last paragraph reverses their
labels. Using uw instead of wu does not change the generated subgroup,
since w² = b and u inverts w. Generation of S remains an obligation of the
geometry producer. The relative normalizer identities are derived by the
consumer from the core commutator calculation and conjugation.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemmas 4.6 and 4.8, pp.40–41.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h}

/-- The local placement of the square root used in source 4.8. The normality
of quaternion factors is supplied separately to its eventual producer. -/
public structure RootData (s : SymmetricSixData h a) where
  b : G
  b_mem : b ∈ fusionCore z
  b_ne_one : b ≠ 1
  w : G
  w_sq : w ^ 2 = b
  w_mem : w ∈ fusionCore z ⊔ zpowers s.u
  w_mem_core : w ∈ coreInG b
  z_mem_core : z ∈ coreInG b
  z_ne_b : z ≠ b
  u_not_core : s.u ∉ coreInG b
  z_commutes_w : Commute z w
  u_inverts_w : s.u * w * s.u⁻¹ = w⁻¹

/-- The two actual marked four-groups and centralizer generation. The
element that exchanges them is constructed separately in Q_b. -/
public structure MarkedGeometry (s : SymmetricSixData h a) extends RootData s where
  t_mem : z * b ∈ s.S
  t_cycleType : (s.equiv ⟨z * b, t_mem⟩).cycleType = {2, 2, 2}
  even_z : s.evenFusion z = zpowers b ⊔ zpowers (s.u * w * z)
  even_t : s.evenFusion (z * b) = zpowers b ⊔ zpowers (s.u * z)
  generated : (s.S ⊓ Centralizer z) ⊔ (s.S ⊓ Centralizer (z * b)) = s.S

/-- The primitive left-conjugation calculation in the quaternion factor
containing w. The two possible images of u differ by the central pivot b. -/
public structure RootConjugator {s : SymmetricSixData h a} (r : RootData s) where
  y : G
  y_mem : y ∈ coreInG r.b
  y_sq : y ^ 2 = r.b
  conjugates_z : y * z * y⁻¹ = z * r.b
  inverts_w : y * r.w * y⁻¹ = r.w⁻¹
  conjugates_u : y * s.u * y⁻¹ = s.u * r.w ∨
    y * s.u * y⁻¹ = s.u * r.w * r.b

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange
