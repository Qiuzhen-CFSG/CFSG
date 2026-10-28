module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.EvenCovers.Setup
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Overgroups
public import Theory.Representation.SL2FourNaturalOrbits.SelfDual

/-!
# The original natural section inside the fixed residual

The restriction of H → S₅ to K has kernel O₂(K). Its given A₅ marking
therefore yields a literal map K → SL₂(4), with the same kernel.
Composing the original U/V₁ coordinates with the given natural projection
constructs U/U₀ as a binary natural SL₂(4) section for this map.
Its kernel is exactly the original U₀, not a chosen isomorphic subgroup.
The generation identity U = [U,K] places U inside O₂(K).

The final application transports the section to the ambient image of
O²(C_J(α)) using the already proved equality with K. This supplies actual
source inputs for the remaining G₂(4) model-action comparison; no assertion
about that model's chief factors or its exclusion is assumed or proved here.
The earlier generation identity remains an explicit input, as in Basic.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.63 and 14.7.68(2), printed pp.1068–1071.
-/

@[expose] public section
noncomputable section

open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

noncomputable def KSL2FourMap : K F →* SL2FourNatural.SL :=
  d.naturalQuotient.marking.symm.toMonoidHom.comp
    (d.K_quotient_equiv_A5.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (K F))))

theorem KSL2FourMap_apply (k : K F) :
    (d.naturalQuotient.marking (d.KSL2FourMap k) : ChapterJ.S5) =
      d.qH ⟨(k : G), K_le_H F k.property⟩ := by
  change (d.naturalQuotient.marking (d.naturalQuotient.marking.symm
    (d.K_quotient_equiv_A5 (QuotientGroup.mk' _ k))) : ChapterJ.S5) = _
  rw [d.naturalQuotient.marking.apply_symm_apply, d.K_quotient_equiv_A5_mk]

theorem KSL2FourMap_surjective : Function.Surjective d.KSL2FourMap :=
  d.naturalQuotient.marking.symm.surjective.comp
    (d.K_quotient_equiv_A5.surjective.comp (QuotientGroup.mk'_surjective _))

theorem KSL2FourMap_ker : d.KSL2FourMap.ker = pCore 2 (K F) := by
  rw [KSL2FourMap, MonoidHom.ker_comp_of_injective _ _ d.naturalQuotient.marking.symm.injective,
    MonoidHom.ker_comp_of_injective _ _ d.K_quotient_equiv_A5.injective,
    QuotientGroup.ker_mk']

noncomputable def KNaturalSection (hgen : F.U = ⁅F.U, K F⁆) :
    BinaryConjugationSection (K F) F.U d.U₀
      (SL2FourNatural.naturalRepresentation.comp d.KSL2FourMap) where
  section_le := by rw [hgen]; exact d.U_commutator_K_le
  kernel_le := d.U₀_le_U
  normalized := (K_le_H F).trans d.conjugationSection.normalized
  coordinates := d.projection.toLinearMap.toAddMonoidHom.toMultiplicative.comp
    d.conjugationSection.coordinates
  onto := (show Function.Surjective d.projection.toLinearMap.toAddMonoidHom.toMultiplicative
    from d.projection_onto).comp d.conjugationSection.onto
  kernel_eq := by
    ext x
    change d.projection (d.conjugationSection.coordinates x).toAdd = 0 ↔ (x : G) ∈ d.U₀
    exact (d.mem_U₀ x).symm
  equivariant k x := by
    let kh : F.H := ⟨k, K_le_H F k.property⟩
    change d.projection (d.conjugationSection.coordinates
      ⟨(k : G) * x * (k : G)⁻¹, _⟩).toAdd =
      SL2FourNatural.action (d.KSL2FourMap k)
        (d.projection (d.conjugationSection.coordinates x).toAdd)
    rw [d.conjugationSection.equivariant kh x]
    have hp := LinearMap.congr_fun (d.projection.isIntertwining' kh)
      (d.conjugationSection.coordinates x).toAdd
    change d.projection (d.action kh (d.conjugationSection.coordinates x).toAdd) =
      d.naturalQuotient.action (d.qH kh)
        (d.projection (d.conjugationSection.coordinates x).toAdd) at hp
    rw [hp, ← d.KSL2FourMap_apply k]
    exact d.naturalQuotient.restriction _ _

include d in
theorem KNaturalSection_core (hgen : F.U = ⁅F.U, K F⁆) :
    F.U ≤ (K F).pCoreIn 2 := by
  let := d.U_elementary
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _)
    (d.KNaturalSection hgen).section_le (d.KNaturalSection hgen).normalized

theorem KNaturalSection_coordinates (hgen : F.U = ⁅F.U, K F⁆) (x : F.U) :
    ((d.KNaturalSection hgen).coordinates x).toAdd =
      d.projection (d.conjugationSection.coordinates x).toAdd := rfl

end Data

namespace EvenCoverSieve

/-- The literal ambient image of the model residual has the original natural
section U/U₀, with a surjective actor whose kernel is its own two-core. -/
theorem Case.fixedResidual_has_naturalSection {d : Data T L V F W} {u : F.U}
    {Lu : Subgroup G} {α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))}
    (c : Case d u Lu α) :
    let R := (MulAut.embeddedFixedResidual 2 α).map (d.fixedComponentInclusion u Lu)
    ∃ q : R →* SL2FourNatural.SL,
      Function.Surjective q ∧ q.ker = pCore 2 R ∧ F.U ≤ R.pCoreIn 2 ∧
      Nonempty (BinaryConjugationSection R F.U d.U₀
        (SL2FourNatural.naturalRepresentation.comp q)) := by
  dsimp only
  rw [d.fixedComponent_fixedResidual_image u c.le_centralizer c.contains.le α c.conjugation]
  exact ⟨d.KSL2FourMap, d.KSL2FourMap_surjective, d.KSL2FourMap_ker,
    d.KNaturalSection_core c.generation, ⟨d.KNaturalSection c.generation⟩⟩

end EvenCoverSieve
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
