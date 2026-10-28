module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticBlock
public import Theory.Representation.OrthogonalFourPlusMatrix.SingularPlaneQuotient

/-!
# The original full-module natural quotient in the symplectic branch

The tensor-coordinate quotient by the original Sylow-generated plane gives
an actual surjection from the original full module to the natural SL₂(4)
module, with exactly that plane as kernel and the original first-factor
marking. The plane is contained in the overgroup two-core and is fully moved
by L. Since L lies in the residual, the plane lies in the whole intrinsic
block core. This places the quotient kernel without any block-recognition
or plane-parabolic assumption.

Source: Aschbacher--Smith 9.3.6 and the final paragraph of 9.3, printed
pp.734--735. GenerationTwoSymplecticPlane applies these maps to the literal
plane-local surjection; its construction and non-Frattini block recognition
remain with qt-d-tensor-sp4-plane.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
open ChapterC.MSCentralOrbit
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The literal full module modulo its original tensor plane is natural
for the original A5 quotient marking, with exact conjugation equivariance. -/
theorem exists_fullModule_natural_quotient :
    ∃ p : D.fullModule.subgroupOf L →* Multiplicative (Fin 2 → Binary.F),
      Function.Surjective p ∧
      p.ker = (m.tensorPlane.subgroupOf L).comap (D.fullModule.subgroupOf L).subtype ∧
      (letI := fullModule_component_normal (D := D)
       ∀ (l : L) (v : D.fullModule.subgroupOf L),
         p (MulAut.conjNormal l v) = Multiplicative.ofAdd
           ((m.firstMarking (e (QuotientGroup.mk' (pCore 2 L) l))).val.mulVec (p v).toAdd)) := by
  obtain ⟨Q,hQ⟩ := m.exists_tensorLine_coordinates_sylow
  obtain ⟨f,hf,hker,heq⟩ := Binary.sylow_plane_natural_quotient Q
  have hplane : m.sectionData.imageSpace m.tensorPlane =
      Binary.firstOrbit (BinaryOffender.fixedSpace Binary.action (Q : Subgroup Binary.G)) := by
    rw [m.tensorPlane_coordinates_firstOrbit,hQ]
  let i := subgroupOfEquivOfLe m.fullModule_le_component
  let p : D.fullModule.subgroupOf L →* Multiplicative (Fin 2 → Binary.F) :=
    f.toAddMonoidHom.toMultiplicative.comp (m.sectionData.coordinates.comp i.toMonoidHom)
  have hp (v : D.fullModule.subgroupOf L) :
      (p v).toAdd = f (m.sectionData.coordinates (i v)).toAdd := rfl
  refine ⟨p,?_,?_,?_⟩
  · intro w
    obtain ⟨v,hv⟩ := hf w.toAdd
    obtain ⟨u,hu⟩ := m.sectionData.onto (Multiplicative.ofAdd v)
    refine ⟨i.symm u,?_⟩
    apply Multiplicative.toAdd.injective
    rw [hp,i.apply_symm_apply,hu]
    exact hv
  · ext v
    change p v = 1 ↔ (v.val.val : G) ∈ m.tensorPlane
    have hone : p v = 1 ↔ (p v).toAdd = 0 :=
      ⟨fun h => congrArg Multiplicative.toAdd h,
        fun h => Multiplicative.toAdd.injective h⟩
    rw [hone, hp]
    change f (m.sectionData.coordinates (i v)).toAdd = 0 ↔ _
    rw [hker,←hplane,m.sectionData.mem_imageSpace_iff]
    constructor
    · rintro ⟨w,hw,he⟩
      have hh := m.coordinates_injective (Multiplicative.toAdd.injective he)
      rw [hh] at hw
      exact hw
    · intro hv
      exact ⟨i v,hv,rfl⟩
  · let := fullModule_component_normal (D := D)
    intro l v
    apply Multiplicative.toAdd.injective
    rw [hp,hp]
    have he := m.sectionData.equivariant
      (⟨l,le_componentOrbit L T l.property⟩ : localOrbit T L) (i v)
    change (m.sectionData.coordinates (i (MulAut.conjNormal l v))).toAdd =
      Binary.action (m.quotient ⟨l,le_componentOrbit L T l.property⟩)
        (m.sectionData.coordinates (i v)).toAdd at he
    rw [m.first_factor l] at he
    rw [he,heq]
    rfl

namespace GenerationTwoOvergroup
variable {m} (c : m.GenerationTwoOvergroup)

/-- The natural quotient kernel lies in the whole original intrinsic core. -/
theorem tensorPlane_le_blockU : m.tensorPlane ≤
    ((ChapterC.blockU (pResidual 2 c.M)).map (pResidual 2 c.M).subtype).map c.M.subtype := by
  have hLH : L ≤ c.M := c.generated ▸ le_sup_of_le_left le_sup_left
  have hline : m.tensorLine ≤ c.M.pCoreIn 2 := (c.fourField_models c.hasMaximalOutside).1
  have hnormal : c.M ≤ normalizer (c.M.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (pCore 2 c.M).le_normalizer_map c.M.subtype
  have hplane : m.tensorPlane ≤ c.M.pCoreIn 2 := by
    exact iSup_conjugates_le_of_le_normalizer m.tensorLine L _ hline (hLH.trans hnormal)
  have hL : L ≤ (pResidual 2 c.M).map c.M.subtype := by
    have hm := map_mono (f := c.M.subtype) c.component_product.2.1
    simpa only [map_subgroupOf_eq_of_le hLH] using hm
  rw [←m.tensorPlane_component_commutator]
  have h := map_mono (f := c.M.subtype)
    (commutatorCore_eq_intrinsic (pResidual 2 c.M) (isPPerfect_pResidual 2)).le
  rw [map_commutator] at h
  exact (commutator_mono hplane hL).trans h

end GenerationTwoOvergroup
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
