module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.AmbientExtension.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.AmbientExtension.CentralizerObstruction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.AmbientExtension.FaithfulAction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.CommutingCubic.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.LocalData
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.Orbits

/-!
# The ambient nine-group extension and its marked involution

The reduction module proves the Sylow placement, the centralizer alternative,
and the numerical normalizer bound for the original marked subgroups. The
proved local outside-core orbit supplies fusion of b = uz with z for either
allowed choice of u. The order-four obstruction then excludes the order-27
centralizer, leaving C_G(D) = D.

The faithful action construction identifies C_{N_G(D)}(b) with GL₂(3),
proves normality of the literal K relative to N_G(D), and constructs v in
this complement with v² = 1 and |vz| = 3. The assembly discharges both the
fusion and self-centralization premises, providing `NineNormalizer.AmbientData`
from the original explicit symmetric and M₁₀ normalizer geometry.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemmas 2.3, 4.5, 4.9 and the following paragraph, pp.41–42.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h}

/-- The local orbit theorem discharges the precise fusion premise needed by
the centralizer obstruction, including the permitted change of u. -/
public theorem uz_fused_of_orbitData (s : SymmetricSixData h a)
    (o : Census.OrbitData z a.u) : IsConj z (s.u * z) := by
  rcases s.u_choice with hu | hu
  · simpa only [hu] using
      CommutingCubic.uz_fused_of_outside_transitive a o.outside_transitive
  · have hz : z * z = 1 := by
      simpa only [h.involution, pow_two] using pow_orderOf_eq_one z
    simpa only [hu, mul_assoc, hz, mul_one] using a.u_fused

/-- The proved local orbit theorem supplies the marked fusion for either
choice of `s.u`, retaining the original selected configuration. -/
public theorem uz_fused_of_quaternion_normal (hn : QuaternionSubgroupsNormal z)
    (d : FusionEightData z) (s : SymmetricSixData h a) : IsConj z (s.u * z) := by
  let selected : SelectedFusionData h := {
    g := a.g
    fused_mem := a.fused_mem
    fused_ne := a.fused_ne
    intersection_elementary := a.intersection_elementary
    intersection_card := a.intersection_card
    intersection_ne_fusion := a.intersection_ne_fusion
    u := a.u
    u_order := a.u_order
    u_centralizes := a.u_centralizes
    u_conjugate_core := a.u_conjugate_core
    u_not_core := a.u_not_core
    u_fused := a.u_fused
    u_inverts_X := a.u_inverts_X }
  exact uz_fused_of_orbitData s (Census.orbitData_of_quaternion_normal h hn d selected)

/-- The literal marked nine-group is self-centralizing: the local fusion
theorem discharges the premise of the order-four obstruction in Lemma 4.9. -/
public theorem centralizer_markedNine_eq (hn : QuaternionSubgroupsNormal z)
    (d : FusionEightData z) (s : SymmetricSixData h a) (m : M10NormalizerGeometry s) :
    Subgroup.centralizer (s.markedNine : Set G) = s.markedNine := by
  exact centralizer_markedNine_eq_of_isConj s m (uz_fused_of_quaternion_normal hn d s)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The ambient normalizer supplies the relative normality of K and the
marked involution of the paragraph following Lemma 4.9. The symmetric and
M₁₀ normalizer witnesses are explicit inputs; no fusion, self-centralization,
splitting or involution-existence premise remains. -/
public theorem nonempty_nineNormalizerAmbientData (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z) (a : SourceGeometry h)
    (s : SymmetricSixData h a) (n : SymmetricNormalizerData s) (m : M10NormalizerGeometry s) :
    Nonempty (NineNormalizer.AmbientData s m) := by
  exact NineNormalizer.nonempty_ambientData_of_self_centralizing s n m
    (NineNormalizer.centralizer_markedNine_eq hn d s m)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
