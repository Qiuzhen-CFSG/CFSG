module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections.DualSection
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.Representation.BinaryConjugationSection.CentralDuality

/-!
# Constructing the source central commutator duality

From the original Data and its SectionCentralizer, QH acts trivially on U/V₁,
so [QH,U] ≤ V₁. The elementary abelian normal subgroup U lies in QH, and
V₁ has order two and is centralized by H. The ambient binary commutator
constructor therefore produces both original centralizer sections and their
H-equivariant duality, including the functional-kernel condition.

The second space is chosen to be the literal linear dual of the first.
No nontrivial commutator identity is used in this construction. The final
projection-kernel application retains the independent identity [U,QH]=V₁,
which is 14.5.21(2), and discharges its former SourceDuality premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.7,
printed p.321; 14.5.15(4) and 14.5.21(1), printed pp.1017–1019;
application in the proof of 14.7.69, printed p.1072.
-/

open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace CriticalIntersections
private theorem core_U_commutator_le_point (d : Data T L V F W)
    (hc : d.SectionCentralizer) : ⁅F.H.pCoreIn 2, F.U⁆ ≤ F.Vi 1 := by
  apply commutator_le.mpr
  intro q hq u hu
  let h : F.H := ⟨q, pCoreIn_le 2 F.H hq⟩
  let v : F.U := ⟨u, hu⟩
  have hh : d.action h = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hc]
    exact hq
  let c : F.U := (⟨h * v * (h : G)⁻¹,
    (mem_normalizer_iff.mp (d.conjugationSection.normalized h.property) v).mp v.property⟩ : F.U) * v⁻¹
  change (c : G) ∈ F.Vi 1
  apply (d.conjugationSection.coordinates_eq_one_iff c).mp
  apply Multiplicative.toAdd.injective
  dsimp only [c]
  rw [map_mul, map_inv]
  change (d.conjugationSection.coordinates _).toAdd +
    -(d.conjugationSection.coordinates v).toAdd = 0
  rw [d.conjugationSection.equivariant, hh]
  exact add_neg_cancel _

private theorem point_centralizes_H (d : Data T L V F W) :
    F.Vi 1 ≤ centralizer (F.H : Set G) := by
  rw [d.point]
  apply zpowers_le.mpr
  intro h hh
  exact (show d.z * h = h * d.z from
    (show h ∈ centralizer ({d.z} : Set G) from d.centralizer_eq ▸ hh)
      d.z (Set.mem_singleton d.z)).symm

/-- The genuine source duality, constructed from the original action kernel.
The second space is the literal linear dual of the first. -/
public theorem exists_sourceDuality (d : Data T L V F W) (hc : d.SectionCentralizer) :
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module (ZMod 2) X),
      Nonempty (SourceDuality F X (Module.Dual (ZMod 2) X)) := by
  let := d.U_elementary
  have hUQ : F.U ≤ F.H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 F.U)
      d.conjugationSection.section_le d.conjugationSection.normalized
  have hNQ : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (le_normalizer_map (H := pCore 2 F.H) F.H.subtype)
  have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨ρ, sU, sQ, hpair, _⟩ := BinaryConjugationSection.exists_central_duality
    F.H (F.H.pCoreIn 2) F.U (F.Vi 1) (pCoreIn_le 2 F.H)
    d.conjugationSection.section_le hNQ d.conjugationSection.normalized
    (d.conjugationSection.kernel_le.trans hUQ) (point_centralizes_H d)
    (core_U_commutator_le_point d hc) hcard
  refine ⟨_, inferInstance, inferInstance, ⟨{
    uAction := ρ
    qAction := ρ.dual
    uSection := sU
    qSection := sQ
    duality := Representation.Equiv.refl ρ.dual
    functional_kernel := hpair }⟩⟩

/-- The original centralizer image is killed by the natural projection,
with the duality premise discharged. The independent source identity
14.5.21(2) remains explicit. -/
public theorem centralizer_image_le_projection_ker_of_sectionCentralizer
    (d : Data T L V F W) (hc : d.SectionCentralizer)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    d.conjugationSection.imageSpace (F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G)) ≤
      d.projection.toLinearMap.ker := by
  obtain ⟨X, aX, mX, hs⟩ := exists_sourceDuality d hc
  let := aX
  let := mX
  obtain ⟨s⟩ := hs
  exact DualSection.centralizer_image_le_projection_ker d hc s hcomm

end CriticalIntersections
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
