module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCore
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Max2Bridge
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl

/-!
# Centralizer control for the literal J₄ local two-core

The second ATLAS local subgroup has been conjugated into the literal
centralizer of `matrixUnitA`. `Generation` proves that the two certified
generators generate the entire centralizer. `NormalClosureControl` proves
that their seed normal closure is a normal two-subgroup whose relative
centralizer has exponent two. Transporting this subgroup along the generation
equality supplies unconditional control of the literal two-core centralizer.

The reduction uses two elementary facts. A normal two-subgroup lies in O₂,
so centralizing O₂ implies centralizing that subgroup. Further, an
exponent-two centralizer of O₂ is itself a normal two-subgroup, and therefore
lies in O₂. Neither full identification of O₂ nor an ambient matrix
centralizer calculation is needed.

Source motivation: GLS3, Table 5.3i, printed p.270,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. The concrete bridge is proved in
`Max2Bridge`; the final theorem discharges full local generation and the
two-subgroup calculation using the concrete certificates, without assuming
the table's local structure.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares

/-- The exponent assertion alone implies containment, since this centralizer
is normal in the actual local group. -/
theorem localTwoCoreCentralizerControl_of_exponent_two
    (hpow : ∀ z ∈ Subgroup.centralizer (involutionTwoCore : Set involutionCentralizer),
      z ^ 2 = 1) : LocalTwoCoreCentralizerControl := by
  refine ⟨?_, hpow⟩
  let D := Subgroup.centralizer (involutionTwoCore : Set involutionCentralizer)
  have hp : IsPGroup 2 D := by
    intro z
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, pow_one] using hpow z z.property
  exact le_sSup (show D.Normal ∧ IsPGroup 2 D from ⟨inferInstance, hp⟩)

/-- Any normal two-subgroup with exponent-two centralizer supplies the
control statement for the full two-core. -/
theorem localTwoCoreCentralizerControl_of_normal_twoSubgroup
    (N : Subgroup involutionCentralizer) (hn : N.Normal) (hp : IsPGroup 2 N)
    (hpow : ∀ z ∈ Subgroup.centralizer (N : Set involutionCentralizer), z ^ 2 = 1) :
    LocalTwoCoreCentralizerControl := by
  have hN : N ≤ involutionTwoCore := le_sSup ⟨hn, hp⟩
  apply localTwoCoreCentralizerControl_of_exponent_two
  intro z hz
  exact hpow z (Subgroup.centralizer_le hN hz)

/-- Final assembly from generation by the certified local words and a
normal two-subgroup calculation inside the subgroup they generate.
The unconditional theorem below supplies all these premises. -/
theorem localTwoCoreCentralizerControl_of_localSubgroup
    (hgen : TwoCoreCentralizerData.localSubgroup = ⊤)
    (N : Subgroup TwoCoreCentralizerData.localSubgroup)
    (hn : N.Normal) (hp : IsPGroup 2 N)
    (hpow : ∀ z ∈ Subgroup.centralizer
      (N : Set TwoCoreCentralizerData.localSubgroup), z ^ 2 = 1) :
    LocalTwoCoreCentralizerControl := by
  let e : TwoCoreCentralizerData.localSubgroup ≃* involutionCentralizer :=
    (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  let L := N.map e.toMonoidHom
  have hL : L.Normal := hn.map e.toMonoidHom e.surjective
  apply localTwoCoreCentralizerControl_of_normal_twoSubgroup L hL
    (hp.map e.toMonoidHom)
  intro z hz
  have hz' : e.symm z ∈ Subgroup.centralizer
      (N : Set TwoCoreCentralizerData.localSubgroup) := by
    intro n hn
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      hz (e n) (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
  simpa only [map_pow, map_one, e.apply_symm_apply] using
    congrArg e (hpow (e.symm z) hz')

/-- Inside the literal involution centralizer, the centralizer of its
two-core lies in the two-core and every element of that centralizer has
square one. All concrete generation and normal-closure premises are proved. -/
theorem localTwoCoreCentralizerControl : LocalTwoCoreCentralizerControl :=
  localTwoCoreCentralizerControl_of_localSubgroup
    TwoCoreCentralizerData.localSubgroup_eq_top
    TwoCoreCentralizerData.localNormalClosure
    TwoCoreCentralizerData.localNormalClosure_normal
    TwoCoreCentralizerData.localNormalClosure_isPGroup
    TwoCoreCentralizerData.localNormalClosure_centralizer_pow_two

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares
