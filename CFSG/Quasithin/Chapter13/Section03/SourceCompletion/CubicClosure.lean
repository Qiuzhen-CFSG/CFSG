module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.ParabolicLifts

/-!
# The unitary closure using the actual plane-residual cubic

A single cubic actor sends the point hyperplane to a second hyperplane
spanning the module. This is exactly what the plane-core and subsequent
cross-displacement argument require. The plane residual is not required
to contain the full plane parabolic. The original component supplies this
cubic through `source_plane_residual_cubic`, with the same module marking.

Source: Aschbacher–Smith 13.3.18(2), printed p.895.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] {V:Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual plane-parabolic cubic and the original hyperplane generate
all of V inside any subgroup normalized by the original plane actors. -/
theorem point_hyperplane_generates_le_of_cubic (C J K:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hc:pointCoordinateSubspace E C=hyperplane) (hCK:C≤K)
    (hJK:J≤normalizer (K:Set G))
    (hP:Atlas.G2.BinaryParabolicPair.cubicActor∈(inducedAutomizer V J).map rho) :
    V≤K := by
  obtain ⟨i,⟨n,hnJ,rfl⟩,hnative⟩:=hP
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
theorem source_module_le_plane_core_of_cubic (B C Q J:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hBV:B≤V) (hCV:C≤V) (hCQ:C≤Q)
    (hc:pointCoordinateSubspace E C=hyperplane)
    (hJ:J≤normalizer (B:Set G))
    (hP:Atlas.G2.BinaryParabolicPair.cubicActor∈(inducedAutomizer V J).map rho)
    (hbound:Q⊓centralizer (B:Set G)≤(normalizer (B:Set G)).pCoreIn 2) :
    V≤(normalizer (B:Set G)).pCoreIn 2 := by
  apply point_hyperplane_generates_le_of_cubic C J _ rho E he hc
    ((le_inf hCQ (hCV.trans ((le_centralizer V).trans (centralizer_le hBV)))).trans hbound)
  · exact hJ.trans ((normalizer (B:Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  · exact hP

variable [Finite G]

open scoped IsKleinFour
/-- The original unitary F.9 closure is abelian. Both hyperplane bounds,
both cross-displacements, and the plane-core containment are proved from
the original point/plane action and the earlier noncentrality theorem. -/
theorem source_closure_abelian_of_point_plane_cubic
    {D:ChapterF.Section09.Setup G} (h:D.Hypothesis) :
    let :=h.elementary
    ∀ (rho:Automizer D.V→*Atlas.G2.Model F) (E:Additive D.V≃ₗ[F]W),
    (∀a v,E (automizerRepresentation D.V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) →
    ∀ (B X:Subgroup G), ∀ [IsKleinFour B], B≤D.V → D.V₁≤B →
    pointCoordinateSubspace E D.Vplus=seed →
    pointCoordinateSubspace E B=plane →
    (inducedAutomizer D.V (D.T:Subgroup G)).map rho≤Atlas.G2.unipotent →
    Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤
      (inducedAutomizer D.V (D.L₁⊔(D.T:Subgroup G))).map rho →
    Atlas.G2.BinaryParabolicPair.cubicActor∈(inducedAutomizer D.V X).map rho →
    (∀g∈D.H,⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆≤
      D.V⊓D.V.map (MulAut.conj g).toMonoidHom →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥) →
    (3:ℕ∞)<globalR D.V →
    D.H=normalizer (D.V₁:Set G) →
    (D.T:Subgroup G)≤normalizer (B:Set G) →
    X≤normalizer (B:Set G) → (D.T:Subgroup G)≤normalizer (X:Set G) →
    IsPPerfect 2 X →
    Nat.card ((X.subgroupOf (normalizer (B:Set G))).map
      (Chapter13.Section05.AmbientSource.planeAction B))=3 →
    IsPGroup 2 (X⊓centralizer (B:Set G):Subgroup G) →
    ⁅D.QH,B⁆≠⊥ → IsMulCommutative D.VH := by
  let :=h.elementary
  dsimp only
  intro rho E he B X _ hBV hPB hs hp hT hP hXimage hcomm hr hH hTB hXB hTX hX hx hkX hm
  have hBp:B≤D.Vplus := by
    intro b hb
    let v:Additive D.V:=Additive.ofMul ⟨b,hBV hb⟩
    have hw:E v∈seed := by
      have hplane:plane≤seed := plane_le_seed
      exact hplane (hp ▸ (mem_pointCoordinateSubspace E B v).mpr hb)
    exact (mem_pointCoordinateSubspace E D.Vplus v).mp (hs.symm ▸ hw)
  have hnoncentral:¬D.Vplus≤centralizer (D.QH:Set G) := by
    intro hc
    apply hm
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hBp.trans hc)
  apply source_closure_abelian_of_plane_core h rho E he B hBV hs hp hT hP hcomm hnoncentral hr
  intro hc
  have hQ:D.QH=(normalizer (D.V₁:Set G)).pCoreIn 2 := congrArg (fun K:Subgroup G=>K.pCoreIn 2) hH
  obtain ⟨hbound,hcore⟩:=Chapter13.Section05.AmbientSource.point_core_centralizer_le_plane_cores
    D.T D.V₁ B X h.point_card hPB h.normalizes_point hTB hXB hTX hX hx hkX (hQ ▸ hm)
  apply source_module_le_plane_core_of_cubic B (D.V⊓D.QH) D.QH X rho E he hBV inf_le_left inf_le_right
    hc hXB hXimage
  rw [hQ]
  exact hbound.trans hcore


end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
