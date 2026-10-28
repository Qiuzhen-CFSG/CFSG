module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.PositiveKernel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.Residual

/-!
# The perfect residual in the binary-three point omega-centralizer

The checked original point-centralizer theorem gives L as its solvable
residual. The actual binary-three quotient also makes L its own cubic
residual. Monotonicity then identifies the cubic perfect core of every
intermediate subgroup containing L. Since the original point belongs to
its Sylow centralizer's omega-center, this applies to that omega-center's
centralizer as soon as L centralizes it. The final theorem feeds this
identity into the actual positive-kernel point-control consumer.
Source: Aschbacher--Smith, 10.1.3 and 10.2.8--9, pp.742,749--750.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- A component with the literal binary-three quotient is its own cubic residual. -/
theorem component_primeToResidual_eq_top
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    primeToResidual 3 L = ⊤ := by
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := e.isSimpleGroup
  let := Chapter1.mem_L_isPerfect D.maximal.1
  have hperfect : IsPPerfect 2 L := by
    intro N hN hquot
    let := hN
    have hs : Subsingleton (L ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hquot.isNilpotent
    apply eq_top_iff.mpr
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  apply primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 L) pCore_isPGroup hperfect
  rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL]
  decide

/-- Every subgroup between L and its original nonfixed point centralizer
has cubic perfect core exactly L. The solvable opposite stabilizer is removed
only after taking the cubic residual. -/
theorem cubicPerfectCore_eq_of_le_point_centralizer
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hv : v ∈ D.fullModule) (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    {X : Subgroup G} (hLX : L ≤ X)
    (hXC : X ≤ localOrbit T L ⊓ centralizer ({v} : Set G)) :
    cubicPerfectCore X = L := by
  have hres := SourceLinearThreeReplacement.Geometry.FixedSpaceTI.point_centralizer_residual
    D e hn hv hvL hv0
  let R := (primeToResidual 3 X).map X.subtype
  have hLR : L ≤ R := by
    have hh := embedded_primeToResidual_mono 3 hLX
    rw [component_primeToResidual_eq_top D e,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  let := Chapter1.mem_L_isPerfect D.maximal.1
  apply le_antisymm
  · exact (map_solvableResidual_mono ((map_subtype_le (primeToResidual 3 X)).trans hXC)).trans_eq hres
  · exact le_map_solvableResidual_of_isPerfect L R hLR

/-- The actual point lies in the omega-center of its own Sylow centralizer. -/
theorem point_mem_point_sylow_omega_center
    {v : G} (hv : v ∈ D.fullModule) :
    v ∈ omegaCenterIn ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨⟨D.fullModule_le_sylow hu hv,mem_centralizer_singleton_iff.mpr rfl⟩,?_,
    elemPow_eq_one_of_isElementaryAbelian v hv⟩
  intro x hx
  exact mem_centralizer_singleton_iff.mp hx.2

/-- Component centralization of the actual point omega-center discharges the
entire exceptional cubic perfect-residual identity. -/
theorem point_omega_residual_of_component_centralizes
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hv : v ∈ D.fullModule) (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hLZ : L ≤ centralizer
      (omegaCenterIn ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G)) :
    cubicPerfectCore (localOrbit T L ⊓ centralizer
      (omegaCenterIn ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G)) = L := by
  apply cubicPerfectCore_eq_of_le_point_centralizer D e hn hv hvL hv0
    (le_inf (le_componentOrbit L T) hLZ)
  apply inf_le_inf_left
  exact centralizer_le (Set.singleton_subset_iff.mpr (point_mem_point_sylow_omega_center D hv))

/-- The original positive-kernel point-control consumer now needs only the two
omega-center centralization assertions of 10.2.8. Point indices and all residual
identifications are proved here; the selection owner retains both assertions. -/
theorem pointSylowControl_of_positive_kernel_centralizes_omega
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (hhalf : HalfSylowUnique D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hZ : localOrbit T L ≤ centralizer (omegaCenterIn (T : Subgroup G) : Set G))
    (hpoints : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom,
      v ≠ 1 → v ∉ centralizer (localOrbit T L : Set G) →
      ¬ centralizer ({v} : Set G) ≤ D.maximalLocal →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (D.maximalLocal ⊓ centralizer ({v} : Set G)) →
      ((T : Subgroup G) ⊓ centralizer ({v} : Set G)).relIndex
        ((T : Subgroup G) ⊓ normalizer (L : Set G)) = 2 →
      L ≤ centralizer (omegaCenterIn ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G)) :
    PointSylowControl D t := by
  apply pointSylowControl_of_positive_kernel_omega_geometry D hmodel hne hhalf ht htn hcross hZ
  intro v hv hvne hv0 hout hs hi
  obtain ⟨e,_⟩ := hmodel
  exact point_omega_residual_of_component_centralizes D e (fun hn => htn (hn ht))
    (partner_le_fullModule D ht hv) (hcross hv) hv0 (hpoints v hv hvne hv0 hout hs hi)

end CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
