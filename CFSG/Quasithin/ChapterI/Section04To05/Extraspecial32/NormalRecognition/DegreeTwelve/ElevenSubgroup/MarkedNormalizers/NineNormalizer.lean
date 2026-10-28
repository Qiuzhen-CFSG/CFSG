module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.CubeDescent
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.AmbientExtension
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.MarkedCore

/-!
# Combining the ambient normalizer and the marked core calculation

Relative normality of K in N_G(D) makes the ambient involution normalize K.
Its product with z has order three. The separate Q_b calculation identifies
the quotient images of r and z, and the fixed-point argument then identifies
the cube of vr with either 1 or the actual marked b = uz.

The final theorem constructs both inputs from the original local hypotheses
and the explicit symmetric and M₁₀ normalizer geometry. It proves the cube
contract for the original marked r, before the subsequent adjustment r ↦ br.
Existence of the symmetric and M₁₀ normalizer geometry belongs to the parent
marked-normalizer construction.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.9 and the local calculation in 4.10, pp.41–42.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h}

/-- Complete the exact cube contract from the two independent source
calculations. Their producers, rather than this conditional theorem,
must establish existence under the original local hypotheses. -/
public theorem nonempty_normalizerCubeData_of_ambientData_of_coreData
    {s : SymmetricSixData h a} {m : M10NormalizerGeometry s}
    (c : NineNormalizer.AmbientData s m) (q : NineNormalizer.CoreData s m) :
    Nonempty (NormalizerCubeData s m) := by
  exact ⟨{
    v := c.v
    v_mem := c.v_mem
    v_sq := c.v_sq
    v_normalizes := c.v_normalizes
    v_commutes_b := c.v_commutes_b
    vz_cube := c.vz_order ▸ pow_orderOf_eq_one (c.v * z)
    vr_cube := q.vr_cube c.v c.v_commutes_b c.vz_order }⟩

/-- The ambient nine-group analysis and the intrinsic Q_b calculation give
the exact local cube alternative for the unchanged marked r. The normalizer
geometry is explicit; no further fusion, splitting or coset premise remains. -/
public theorem nonempty_normalizerCubeData (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z) (a : SourceGeometry h)
    (s : SymmetricSixData h a) (n : SymmetricNormalizerData s) (m : M10NormalizerGeometry s) :
    Nonempty (NormalizerCubeData s m) := by
  obtain ⟨c⟩ := nonempty_nineNormalizerAmbientData h hn d a s n m
  obtain ⟨q⟩ := NineNormalizer.MarkedCore.nonempty_coreData h hn d a s n m
  exact nonempty_normalizerCubeData_of_ambientData_of_coreData c q

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
