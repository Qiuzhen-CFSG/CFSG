module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.Quotient
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.Diagram
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExtensionCores
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Radical representatives from the common plane residual

Map the literal R₂=O₂(BT) into IT/O₂(IT). The marked component is Sp₄,
and T normalizes its plane residual. Diagram control and the extension-core
calculation identify the image of R₂ with the plane radical. Lifting each
image element to I gives a=i*q with q in O₂(IT), retaining the original
ambient element and quotient map. The application to `ofFlag` preserves
its literal second radical.

The remaining geometric premise is the marked common-plane equality.
No radical lifts, R₂ action, or action-image bound are assumed by the final
two theorems. Source: Aschbacher--Smith 11.1.2(3), p.764, and 11.4.1(2), p.776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {I U : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T I U) {F : BinaryField}

/-- Exact core images give representatives in a faithful marked extension.
The later theorem supplies this extension from the actual IT quotient. -/
theorem planeRadicalLifts_of_core_quotient
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))
    (hn : 1 < F.degree) (B : Subgroup G) (hBI : B ≤ I)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hB : (B.subgroupOf I).map
      (m.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) = planeLocal)
    {H : Type*} [Group H] [Finite H]
    (π : (I ⊔ (T : Subgroup G) : Subgroup G) →* H)
    (hker : π.ker = pCore 2 (I ⊔ (T : Subgroup G) : Subgroup G))
    (N : Subgroup H) [N.Normal] (e : Sp F.Carrier ≃* N)
    (he : ∀ i : I, π (inclusion le_sup_left i) =
      (e (m.groupEquiv (QuotientGroup.mk' (pCore 2 I) i))).val)
    (hC : centralizer (N : Set H) = ⊥)
    (hdiagram : ∀ h : H,
      DiagramAutomorphisms.PreservesDiagram (DiagramAutomorphisms.extensionAction N e h)) :
    HasPlaneRadicalLifts D m ((B ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let J := I ⊔ (T : Subgroup G)
  let R := (B ⊔ (T : Subgroup G)).pCoreIn 2
  let μ := m.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  let j := N.subtype.comp e.toMonoidHom
  have hj : Function.Injective j := N.subtype_injective.comp e.injective
  have hBJ : B ≤ J := hBI.trans le_sup_left
  have hBTJ : B ⊔ (T : Subgroup G) ≤ J := sup_le hBJ le_sup_right
  have hRJ : R ≤ J := (pCoreIn_le 2 _).trans hBTJ
  have hsub : (B.subgroupOf I).map (inclusion (show I ≤ J from le_sup_left)) =
      B.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le hBJ]
    exact map_subgroupOf_eq_of_le hBI
  have hbmap : (B.subgroupOf J).map π = planeLocal.map j := by
    rw [← hsub, map_map, ← hB, map_map]
    congr 1
    exact MonoidHom.ext he
  have hnorm : (T : Subgroup G).subgroupOf J ≤
      normalizer (B.subgroupOf J : Set J) := by
    intro t ht b
    exact hTB ht b.val
  have hnorm' : ((T : Subgroup G).subgroupOf J).map π ≤
      normalizer (planeLocal.map j : Set H) := by
    rw [← hbmap]
    exact (map_mono hnorm).trans ((B.subgroupOf J).le_normalizer_map π)
  have him : (R.subgroupOf J).map π =
      (Plane.radical.map planeLocal.subtype).map j := by
    rw [← pCoreIn_subgroupOf 2 _ J hBTJ,
      map_pCoreIn_of_ker_isPGroup π (hker ▸ pCore_isPGroup),
      subgroupOf_sup hBJ le_sup_right, Subgroup.map_sup, hbmap]
    change (planeLocal.map j ⊔ ((T : Subgroup G).subgroupOf J).map π).pCoreIn 2 = _
    rw [show (planeLocal.map j ⊔ ((T : Subgroup G).subgroupOf J).map π).pCoreIn 2 =
        (planeLocal.map j).pCoreIn 2 from
      DiagramAutomorphisms.planeLocal_join_core_eq N e F.card_eq hn hC hdiagram _ hnorm',
      ← map_pCoreIn_of_injective 2 _ j hj, pCoreIn, planeLocal_core_eq F.card_eq hn]
  intro a
  have ha : π ⟨a.val, hRJ a.property⟩ ∈ (Plane.radical.map planeLocal.subtype).map j := by
    rw [← him]
    exact mem_map_of_mem π a.property
  obtain ⟨b, hb, hba⟩ := ha
  obtain ⟨i, hi⟩ := (m.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)) b
  change m.groupEquiv (QuotientGroup.mk' (pCore 2 I) i) = b at hi
  let q₀ : J := (inclusion le_sup_left i)⁻¹ * ⟨a.val, hRJ a.property⟩
  have hq₀ : q₀ ∈ pCore 2 J := by
    rw [← hker]
    change π q₀ = 1
    dsimp only [q₀]
    rw [map_mul, map_inv, he i, hi]
    exact inv_mul_eq_one.mpr hba
  refine ⟨i, ⟨q₀.val, mem_map_of_mem J.subtype hq₀⟩, ?_, ?_⟩
  · change a.val = i.val * (i.val⁻¹ * a.val)
    group
  · rw [hi]
    exact hb

/-- The actual quotient of IT supplies the representatives; the sole model
placement input is that B is the marked plane residual. -/
theorem planeRadicalLifts_of_plane_residual
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))
    (hn : 1 < F.degree) (B : Subgroup G) (hBI : B ≤ I)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hB : (B.subgroupOf I).map
      (m.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) = planeLocal) :
    HasPlaneRadicalLifts D m ((B ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let J := I ⊔ (T : Subgroup G)
  let N := quotientComponent (I := I) (T := T)
  let e := quotientComponentEquiv D m
  let j := N.subtype.comp e.toMonoidHom
  let := quotientComponent_normal D
  have he (i : I) : joinProjection (inclusion le_sup_left i) =
      (e (m.groupEquiv (QuotientGroup.mk' (pCore 2 I) i))).val :=
    (quotientComponentEquiv_mk D m i).symm
  have hbmap : (B.subgroupOf J).map joinProjection = planeLocal.map j := by
    have hsub : (B.subgroupOf I).map (inclusion (show I ≤ J from le_sup_left)) =
        B.subgroupOf J := by
      apply map_injective J.subtype_injective
      rw [map_map, map_subgroupOf_eq_of_le (hBI.trans le_sup_left)]
      exact map_subgroupOf_eq_of_le hBI
    rw [← hsub, map_map, ← hB, map_map]
    congr 1
    exact MonoidHom.ext he
  have hnorm : (T : Subgroup G).subgroupOf J ≤
      normalizer (B.subgroupOf J : Set J) := by
    intro t ht b
    exact hTB ht b.val
  have hnorm' : ((T : Subgroup G).subgroupOf J).map joinProjection ≤
      normalizer (planeLocal.map j : Set (joinQuotient (I := I) (T := T))) := by
    rw [← hbmap]
    exact (map_mono hnorm).trans ((B.subgroupOf J).le_normalizer_map joinProjection)
  exact planeRadicalLifts_of_core_quotient D m hn B hBI hTB hB
    joinProjection (QuotientGroup.ker_mk' _) N e he
    (quotientComponent_centralizer D m)
    (extension_preservesDiagram_of_plane_normalizer F.card_eq hn N e _
      quotientComponent_sup_sylow hnorm')

/-- The common plane residual gives representatives for the literal original R₂. -/
theorem ofFlag_planeRadicalLifts {L V : Subgroup G}
    (D₀ : Chapter12.Section02.ChosenModule T L V) (S : D₀.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D₀ S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H₀ : Subgroup G)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))
    (hn : 1 < F.degree) (hLI : f.Li 1 ≤ I)
    (hplane : ((f.Li 1).subgroupOf I).map
      (m.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) = planeLocal) :
    HasPlaneRadicalLifts D m (ofFlag S f X z H₀).R₂ :=
  planeRadicalLifts_of_plane_residual D m hn (f.Li 1) hLI
    (f.sylow_normalizes_Li 1) hplane

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
