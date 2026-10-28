module

public import CFSG.Quasithin.Chapter10.SourceA5PointLinearAlternative
public import CFSG.Quasithin.Chapter10.SourceA5PointG2
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerMathieu
public import CFSG.Quasithin.Chapter10.SourceA5PointSymplecticTorus

/-!
# Completed quasisimple rows in the original A5 point-centralizer argument

The original conjugate moved module is elementary, so it centralizes the
chosen vector. The point-centralizer hypothesis therefore supplies its
normalization of the containing component. The proved G₂ and M₂₃ component
fixer calculations then give the common centralizer alternative. The imported
linear theorem supplies the same alternative, and the imported symplectic
theorem supplies the moving torus alternative.

Every model equivalence is on the literal quotient I/Z(I), and the G₂ and
symplectic parabolic markings retain the actual image of L.subgroupOf I.
These wrappers discharge the completed rows; they do not produce the source
embedding catalogue. Source: Aschbacher–Smith, proof of 10.2.9, pp.750–751,
combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem conjugate_moved_le_point_centralizer
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (t : G)
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer ({v} : Set G) := by
  let := source_original_full_moved_elementary D
  let U := (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  intro u hu y hy
  have he : y = v := Set.mem_singleton_iff.mp hy
  rw [he]
  exact U.le_centralizer hu v hv

/-- Both literal G₂(4) local markings feed the common alternative for the
actual original conjugate moved module. -/
theorem source_a5_point_g2_alternative
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (t : G)
    (I : Subgroup G) [Group.IsPerfect I] (hLI : L ≤ I)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (eI : (I ⧸ center I) ≃* Atlas.G2.Model F)
    (hmark : (L.subgroupOf I).map
      (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
        Atlas.G2.LieParabolicSetup.local₁ ∨
      (L.subgroupOf I).map (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
        Atlas.G2.LieParabolicSetup.local₂)
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G)) :
    SourceA5PointComponentAlternative D e t I := by
  exact .common (source_a5_g2_component_centralized D e hLI hF eI hmark
    ((conjugate_moved_le_point_centralizer D t hv).trans hNI) hcross)

/-- The concrete M₂₃ central quotient feeds the common alternative for the
actual original conjugate moved module, with no embedding marking premise. -/
theorem source_a5_point_m23_alternative
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (t : G)
    (I : Subgroup G) [Group.IsPerfect I] (hLI : L ≤ I)
    (eI : (I ⧸ center I) ≃* Sporadic.Mathieu.M23)
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G)) :
    SourceA5PointComponentAlternative D e t I := by
  let := source_original_full_moved_elementary D
  let U := (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  exact .common (source_a5_m23_component_centralized e hLI eI
    ((conjugate_moved_le_point_centralizer D t hv).trans hNI) hcross)

end CFSG.Quasithin.Chapter10
