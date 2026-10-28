module

public import Theory.Representation.BinaryOffender.FixedSpaceSpan
public import Theory.Representation.MathieuCodeRestriction
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Trio
public import Theory.PGroupCore

/-!
# Native markings for the Mathieu code and cocode calculations

These definitions retain the literal Witt-design subgroups and the native
point-stabilizer embedding of M₂₃ in M₂₄. Each kernel is the two-core of
its own stabilizer, mapped into the ambient group. In particular no ambient
normality is required or implied. The marked common subgroup is the inverse
image of `K_O ∩ K_S` for the incident standard octad and sextet.

The module constructions are the actual Golay quotients from H.13.1.
Their irreducibility, the orders of the marked kernels, and the fixed-space
calculations remain theorem obligations, not fields of these definitions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.1.2, printed p.68; H.13.1 and the setup of H.14, printed pp.395–396;
the common four-subgroup in the proof of H.16.8, printed p.405.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterH.Section13To16

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Representation.BinaryOffender

/-- The source `(F − 1)` condition, including nontrivial elementary abelian actors. -/
def IsFMinusOneOffender {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) : Prop :=
  IsElementaryTwo A ∧ fixedCodim ρ A ≤ rank A + 1

/-- `K_O = O₂(M_O)`, placed in the actual M₂₄. -/
noncomputable def octadKernel (O : Octad) : Subgroup M24 :=
  (pCore 2 (octadStabilizer O)).map (octadStabilizer O).subtype

/-- `K_S = O₂(M_S)`, placed in the actual M₂₄. -/
noncomputable def sextetKernel (S : Sextet) : Subgroup M24 :=
  (pCore 2 (sextetStabilizer S)).map (sextetStabilizer S).subtype

/-- `K_T = O₂(M_T)`, placed in the actual M₂₄. -/
noncomputable def trioKernel (T : Trio) : Subgroup M24 :=
  (pCore 2 (trioStabilizer T)).map (trioStabilizer T).subtype

/-- Restriction of the octad kernel to the native point stabilizer. -/
noncomputable def m23OctadKernel (O : Octad) : Subgroup M23 :=
  (octadKernel O).comap MathieuCode.pointEmbedding

/-- The sextet stabilizer inside the native point stabilizer also fixes the
tetrad containing the distinguished point, hence stabilizes its complementary quintet. -/
noncomputable def m23QuintetStabilizer (S : Sextet) : Subgroup M23 :=
  (sextetStabilizer S).comap MathieuCode.pointEmbedding

/-- The intrinsic two-core of the quintet stabilizer. -/
noncomputable def m23QuintetKernel (S : Sextet) : Subgroup M23 :=
  (pCore 2 (m23QuintetStabilizer S)).map (m23QuintetStabilizer S).subtype

/-- The common subgroup in the marked H.16.8 configuration.
Its elementary structure and order four must be proved from these definitions. -/
noncomputable def m23CommonKernel : Subgroup M23 :=
  (octadKernel standardOctad ⊓ sextetKernel standardSextet).comap
    MathieuCode.pointEmbedding

theorem m23CommonKernel_le_octad : m23CommonKernel ≤ m23OctadKernel standardOctad :=
  fun _ h => h.1

theorem m23CommonKernel_le_sextet :
    m23CommonKernel ≤ (sextetKernel standardSextet).comap MathieuCode.pointEmbedding :=
  fun _ h => h.2

theorem standardOctad_contains_distinguished_point : (0 : Fin 24) ∈ standardOctad.val := by
  decide +kernel

end CFSG.Quasithin.ChapterH.Section13To16
