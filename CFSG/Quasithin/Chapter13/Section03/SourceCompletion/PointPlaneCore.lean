module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.PointCrossPlanes
public import Theory.Representation.G2BinaryPlaneHyperplaneSpan

/-!
# Generating the original module inside the plane two-core

The native plane-parabolic cubic lifts through the original automizer.
Its two hyperplanes span V, so any subgroup containing V₅ and normalized
by the plane actors contains V. Applied to O₂(N_G(V₂)), the preceding
13.3.15 core-centralizer bound gives the literal V≤O₂(G₂).

Source: Aschbacher–Smith, Lemma 13.3.18, printed p.895.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] {V:Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual plane-parabolic cubic and the original hyperplane generate
all of V inside any subgroup normalized by the original plane actors. -/
theorem point_hyperplane_generates_le (C J K:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hc:pointCoordinateSubspace E C=hyperplane) (hCK:C≤K)
    (hJK:J≤normalizer (K:Set G))
    (hP:Atlas.G2.BinaryParabolicPair.derivedFirstAmbient≤(inducedAutomizer V J).map rho) :
    V≤K := by
  have hact:Atlas.G2.BinaryParabolicPair.cubicActor∈
      Atlas.G2.BinaryParabolicPair.derivedFirstAmbient:=
    ⟨Atlas.G2.BinaryParabolicPair.cubicActor_mem,
      Atlas.G2.BinaryParabolicPair.cubicActor_mem_derived⟩
  obtain ⟨i,⟨n,hnJ,rfl⟩,hnative⟩:=hP hact
  have hlow:hyperplane≤pointCoordinateSubspace E K := hc ▸ pointCoordinateSubspace_mono E hCK
  have hupper:hyperplane.map (Atlas.G2.Restricted.NaturalCoordinates.action F
      Atlas.G2.BinaryParabolicPair.cubicActor)≤pointCoordinateSubspace E K := by
    rw [←hnative]
    have hh:=pointCoordinateSubspace_map_actor K rho E he n
    have hk:K.map (MulAut.conj n.val).toMonoidHom=K:=
      mem_normalizer_iff_map_conj_eq.mp (hJK hnJ)
    rw [hk] at hh
    exact (Submodule.map_mono hlow).trans hh
  have hall:(⊤:Submodule F W)≤pointCoordinateSubspace E K :=
    hyperplane_plane_cubic_span ▸ sup_le hlow hupper
  intro v hv
  let w:Additive V:=Additive.ofMul ⟨v,hv⟩
  exact (mem_pointCoordinateSubspace E K w).mp (hall (by trivial))

/-- The preceding source core-centralizer bound, together with the literal
plane action, places the whole original module in O₂(G₂). -/
theorem source_module_le_plane_core (B C Q J:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hBV:B≤V) (hCV:C≤V) (hCQ:C≤Q)
    (hc:pointCoordinateSubspace E C=hyperplane)
    (hJ:J≤normalizer (B:Set G))
    (hP:Atlas.G2.BinaryParabolicPair.derivedFirstAmbient≤(inducedAutomizer V J).map rho)
    (hbound:Q⊓centralizer (B:Set G)≤(normalizer (B:Set G)).pCoreIn 2) :
    V≤(normalizer (B:Set G)).pCoreIn 2 := by
  apply point_hyperplane_generates_le C J _ rho E he hc
    ((le_inf hCQ (hCV.trans ((le_centralizer V).trans (centralizer_le hBV)))).trans hbound)
  · exact hJ.trans ((normalizer (B:Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  · exact hP
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
