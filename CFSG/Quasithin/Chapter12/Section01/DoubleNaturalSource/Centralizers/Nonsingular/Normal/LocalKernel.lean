module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.PointAction
public import CFSG.Quasithin.Chapter4.Section01.Maximality
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer

/-!
# The local nonsingular section-centralizer kernel

The faithful point stabilizer has trivial two-core, so its residual
centralizer lies in the residual. The actual H.9 residual is centerless,
hence this centralizer is trivial. Transport through the literal point
action identifies C_{M_w}(L_w/O₂(L_w)) with C_{M_w}(W).

`NaturalBlocks` uses this to fix W under the source Cartan actor, while
`CubicKernel` supplies the order restriction needed for the A₅ branch.
Source: Aschbacher--Smith, 12.1.1, printed p.788, using H.9.1(4).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement IsMulCommutative
open BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits.AutomorphismModel
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

/-- The actual source stabilizer has trivial centralizer of its two-residual. -/
theorem nonsingular_stabilizer_residual_centralizer_eq_bot (w : componentOrbit V (T : Subgroup G))
    (hw : B.quadratic (Additive.ofMul w) = 1) :
    centralizer (pResidual 2 (S.setup.stabilizer (Additive.ofMul w)) :
      Set (S.setup.stabilizer (Additive.ofMul w))) = ⊥ := by
  let J := S.setup.stabilizer (Additive.ofMul w)
  let R := S.setup.residual (Additive.ofMul w)
  have hres : (pResidual 2 J).map J.subtype = R := S.nonsingular_stabilizer_residual w hw
  obtain ⟨e₀⟩ := (ChapterH.NaturalDual.SourceSetup.nonsingular_structure S.setup
    (show S.setup.quadratic (Additive.ofMul w) = 1 by rwa [S.quadratic_eq])).2.1
  have hn : 0 < n-1 := by have := B.degree; omega
  let e := e₀.trans (projectiveEquivLinear hn)
  apply bot_unique
  intro a ha
  have har : a ∈ pResidual 2 J :=
    centralizer_pResidual_le_of_pCore_eq_bot (S.nonsingular_stabilizer_twoCore w hw) ha
  have haR : (a : B.ActionQuotient) ∈ R := hres ▸ mem_map_of_mem J.subtype har
  let b : R := ⟨a,haR⟩
  have hb : e b ∈ center (LinearGroup (n-1)) := by
    apply mem_center_iff.mpr
    intro x
    obtain ⟨r,rfl⟩ := e.surjective x
    have hr : (r : B.ActionQuotient) ∈ (pResidual 2 J).map J.subtype := hres.symm ▸ r.property
    obtain ⟨s,hs,he⟩ := hr
    have hh : r * b = b * r := by
      apply Subtype.ext
      change (r : B.ActionQuotient) * a = (a : B.ActionQuotient) * r
      rw [←he]
      exact congrArg Subtype.val (ha s hs)
    simpa only [map_mul] using congrArg e hh
  rw [linear_center_eq_bot hn,mem_bot] at hb
  have he : b = 1 := e.injective (hb.trans e.map_one.symm)
  exact mem_bot.mpr (Subtype.ext (congrArg (fun r : R => (r : B.ActionQuotient)) he))

include S
/-- Local centralizers of the residual section fix the entire original doubled orbit. -/
theorem nonsingular_local_sectionCentralizer_le_orbitCentralizer (w : componentOrbit V (T : Subgroup G))
    (hw : B.quadratic (Additive.ofMul w) = 1) :
    sectionCentralizerIn (B.localPointCentralizer w) (B.pointResidual w) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
  let M := B.localPointCentralizer w
  let R := B.pointResidual w
  let C := sectionCentralizerIn M R
  let f := S.localPointAction w
  have hRM : R ≤ M := le_inf (B.pointResidual_le_normalizer w)
    ((B.pointResidual_le w).trans inf_le_right)
  have hcomm : ⁅C,R⁆ ≤ R.pCoreIn 2 :=
    ((le_sectionCentralizer_iff C R).mp inf_le_right).2
  have hm : (C.subgroupOf M).map f ≤
      centralizer (pResidual 2 (S.setup.stabilizer (Additive.ofMul w)) : Set _) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←S.residual_localPointAction w hw,←map_commutator]
    apply (map_eq_bot_iff (f := f) _).mpr
    apply commutator_le.mpr
    intro c hc r hr
    have hh : ⁅(c : G),(r : G)⁆ ∈ R.pCoreIn 2 := hcomm (commutator_mem_commutator hc hr)
    obtain ⟨u,hu,he⟩ := hh
    have hk : (B.actionProjection.comp (inclusion (B.pointResidual_le_normalizer w))) u = 1 := by
      apply (S.nonsingular_residual_kernel_and_quotient w hw).1.symm ▸ hu
    apply Subtype.ext
    change B.actionProjection ⟨⁅(c : G),(r : G)⁆,_⟩ = 1
    exact (congrArg B.actionProjection (show
      inclusion (B.pointResidual_le_normalizer w) u = ⟨⁅(c : G),(r : G)⁆,_⟩
      from Subtype.ext he)).symm.trans hk
  rw [S.nonsingular_stabilizer_residual_centralizer_eq_bot w hw] at hm
  intro c hc
  have hh : f ⟨c,hc.1⟩ = 1 := mem_bot.mp (hm (mem_map_of_mem f hc))
  have hproj : B.actionProjection ⟨c,hc.1.1⟩ = 1 := congrArg Subtype.val hh
  have hk := (QuotientGroup.eq_one_iff (⟨c,hc.1.1⟩ : normalizer (L : Set G))).mp hproj
  rw [normalizerAction_ker] at hk
  exact hk

/-- The full local section centralizer is exactly the kernel on the doubled orbit. -/
theorem nonsingular_local_sectionCentralizer_eq (w : componentOrbit V (T : Subgroup G))
    (hw : B.quadratic (Additive.ofMul w) = 1) :
    sectionCentralizerIn (B.localPointCentralizer w) (B.pointResidual w) =
      B.localPointCentralizer w ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
  apply le_antisymm (le_inf inf_le_left (S.nonsingular_local_sectionCentralizer_le_orbitCentralizer w hw))
  let M := B.localPointCentralizer w
  let R := B.pointResidual w
  let C := M ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G)
  have hRM : R ≤ M := le_inf (B.pointResidual_le_normalizer w)
    ((B.pointResidual_le w).trans inf_le_right)
  have hNR := B.localPointCentralizer_normalizes_residual w
  apply le_inf inf_le_left
  apply (le_sectionCentralizer_iff C R).mpr
  refine ⟨inf_le_left.trans hNR,?_⟩
  apply commutator_le.mpr
  intro c hc r hr
  let cm : M := ⟨c,hc.1⟩
  let rm : M := ⟨r,hRM hr⟩
  let f := B.actionProjection.comp (inclusion (show M ≤ normalizer (L : Set G) from inf_le_left))
  have hfc : f cm = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [normalizerAction_ker]
    exact hc.2
  have hcomm := le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hNR)
    (commutator_mem_commutator hc hr)
  let u : R := ⟨⁅c,r⁆,hcomm⟩
  have hfu : (B.actionProjection.comp (inclusion (B.pointResidual_le_normalizer w))) u = 1 := by
    change f ⁅cm,rm⁆ = 1
    rw [map_commutatorElement,hfc,commutatorElement_one_left]
  refine ⟨u,?_,rfl⟩
  exact (S.nonsingular_residual_kernel_and_quotient w hw).1 ▸ hfu

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
