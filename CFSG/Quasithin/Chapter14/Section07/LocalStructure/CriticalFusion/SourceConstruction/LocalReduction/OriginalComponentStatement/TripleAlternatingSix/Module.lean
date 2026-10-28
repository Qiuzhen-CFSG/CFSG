module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.TripleAlternatingSix.Structure
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.LargePrimeGeometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.CubicGeometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.NativeSource
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion

/-!
# The actual hexacode actor in the original triple-six branch

The normal point cubic is fixed-free on the literal U_I/V₁. Its extraspecial
three-subgroup forces dimension divisible by six. The original selected
critical denominator and its single displacement line force dimension six
and irreducibility on the component. Native recognition then gives the whole
faithful hexacode actor with the actual component mapped to the even subgroup.

Source: Aschbacher--Smith 14.7.47, printed p.1064, using F.9.13--18 and
B.4.5; refs/quasithin.pdf. No homogeneous-selection premise is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction
open Chapter14.Section06.OddCriticalPair.Selection
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original reduced local admits the faithful marked hexacode actor. -/
theorem reduced_triple_alternatingSix_actor_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hgen : C ⊔ (T : Subgroup G).subgroupOf I = ⊤) :
    ∃ φ : HStar I →* Atlas.Codes.HexAutomorphisms, Function.Injective φ ∧
      (C.map (QuotientGroup.mk' (pCore 2 I))).map φ = Atlas.Codes.hexSign.ker := by
  classical
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  let X := ((F.Li L 1).subgroupOf I).map q
  obtain ⟨hnB,⟨eB⟩,hfit,hg,hpn,hz⟩ := reduced_triple_alternatingSix_structure_at
    d h hab structural previous faithful earlier I hI C hC e hgen
  let := hnB
  have hc : centralizer (B : Set (HStar I)) ≤ B := by
    change generalizedFitting (HStar I) = B at hfit
    rw [←hfit]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := HStar I)
  obtain ⟨hU,a,hq,_⟩ := WholeResidualAssembly.GuardedSource.local_prime_supplement_quadratic_actor
    h hab structural previous I hI B hg
  let := hU
  let W := Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I))
  let z : HStar I := (eB.symm Atlas.Codes.hexEvenZ).val
  have hzc : zpowers z = (center B).map B.subtype :=
    (ModuleRecognition.embedded_center_eq_zpowers B eB).symm
  have hzx : zpowers z = X := hzc.trans hz.symm
  have ho : orderOf z = 3 := by
    rw [show orderOf z = orderOf (eB.symm Atlas.Codes.hexEvenZ) from
      orderOf_injective B.subtype B.subtype_injective _]
    rw [eB.symm.orderOf_eq,Atlas.Codes.hexEvenZ_order]
  have hfree : ∀ v, a.representation z v = v → v = 0 := by
    intro v hv
    have hf : v ∈ fixedSpace a.representation (zpowers z) :=
      (mem_fixedSpace_zpowers_iff _ _ _).mpr hv
    rw [hzx,WholeResidualAssembly.GuardedSource.local_point_fixedSpace_eq_bot
      h structural I (F.Li_one_le_of_mem_Hz hI) hpn a] at hf
    exact hf
  have hpolynomial := Representation.RankTwo.quadratic_of_cubic_fixed_free
    (a.representation z) (show a.representation z ^ 3 = 1 by
      rw [←map_pow,show z ^ 3 = 1 from by simpa only [ho] using pow_orderOf_eq_one z,map_one])
    hfree
  have hp : CubicPolynomial a.representation z := by
    intro v
    exact LinearMap.congr_fun hpolynomial v
  have hpos : 0 < Module.finrank (ZMod 2) W := by
    by_contra hzero
    let : Subsingleton W := (Module.finrank_zero_iff (R := ZMod 2) (M := W)).mp (by omega)
    have he : z = 1 := a.faithful (Subsingleton.elim _ _)
    rw [he,orderOf_one] at ho
    omega
  let : Nontrivial W := Module.nontrivial_of_finrank_pos hpos
  have hdiv := CubicGeometry.six_dvd_finrank a.representation B eB z
    (eB.symm Atlas.Codes.hexEvenZ).property hzc hp
  change 6 ∣ Module.finrank (ZMod 2) W at hdiv
  have hdim : 2 < Module.finrank (ZMod 2) W := by omega
  let D := Chapter12.Section09.NaturalSource.naturalF9Setup F L I
  let hf := WholeResidualAssembly.GuardedSource.local_f9_hypothesis h hab structural previous I hI
  let : IsElementaryAbelian 2 D.UH := inferInstanceAs (IsElementaryAbelian 2 (F.UH I))
  obtain ⟨c⟩ := WholeResidualAssembly.GuardedSource.local_normal_point_selected_endpoint
    h hab structural previous I hI hpn a hdim
  have hb := (WholeResidualAssembly.GuardedSource.local_f9_critical_bounds
    h hab structural previous I hI).1
  let s := ModuleBound.OriginalF916.conjugationSection a hf.H_centralizes
  have hUV : D.UH ≤ D.VH := conjugateSpanBy_mono hf.plus_le le_rfl
  have hBH : c.endpoint.conjugate D.UH ≤ I :=
    (map_mono hUV).trans (c.endpoint.large_le hb)
  have hreverse : D.UH ≤ I.map (MulAut.conj c.endpoint.representative).toMonoidHom :=
    hUV.trans (c.endpoint.reverse_le hb)
  have hline := s.critical_line_displacement_of_conjugate (c.endpoint.conjugate D.UH)
    c.endpoint.representative hreverse hf.point_card
  have hcodim : Module.finrank (ZMod 2) (W ⧸ s.image
      (commutatorPreimage D.UH (c.endpoint.conjugate D.UH) (c.endpoint.conjugate D.V₁))) ≤
      rank (actorImage I (c.endpoint.conjugate D.UH)) := by
    have hdq := s.quotient_finrank
      (commutatorPreimage D.UH (c.endpoint.conjugate D.UH) (c.endpoint.conjugate D.V₁))
      (s.line_le_DH (c.endpoint.conjugate D.UH) (c.endpoint.conjugate D.V₁) hBH)
    exact hdq.le.trans c.comparison
  have hd := CubicGeometry.degree_six_of_critical a.representation B eB z
    (eB.symm Atlas.Codes.hexEvenZ).property hzc hp a.faithful hc ho
    _ c.quadratic.1 c.quadratic.2.1 c.quadratic.2.2 _ _ hcodim hline.1 hline.2
  have hi := CubicGeometry.component_irreducible_of_degree_six a.representation B eB z
    (eB.symm Atlas.Codes.hexEvenZ).property hzc hp hd
  obtain ⟨m⟩ := LocalGeometry.DynkinExclusion.Recognition.model_of_irreducible
    a.representation B
    (LocalGeometry.DynkinExclusion.Recognition.smallInput_of_irreducibleInputs B
      (ModuleRecognition.NativeSource.irreducibleInputs B
        (WholeResidualAssembly.GuardedSource.local_star_sqtk h I hI) eB hc)) a.faithful hi hq
  exact ⟨m.actor,m.faithful,m.component_image⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
