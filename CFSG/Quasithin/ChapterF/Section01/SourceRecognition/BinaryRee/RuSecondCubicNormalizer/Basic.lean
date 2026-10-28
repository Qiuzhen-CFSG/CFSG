module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondCubicGeometry
public import Theory.GroupTheory.SylowThreeNormalizerSection

/-!
# The literal source cubic normalizer and its marked action

Retain the selected original X, its generator, and the proved coordinates on
A. Restrict the existing parabolic conjugation action to F₂∩N_G(X). The
marking identifies the generator with the specified native cubic and its
fixed elements with the original centralizer in A. The data record is
constructed from the preceding source theorem; it contains no image-order
or extension-recognition premise.

Source: Aschbacher–Smith J.4.4–5 and F.1.12.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
open ReeTwo.SylowModel
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

/-- The original cubic normalizer inside the selected second endpoint. -/
def secondCubicNormalizer (B5:Sylow 5 d.toTypeRuSetup.H) (X:Sylow 3 p.parabolic) : Subgroup G :=
  p.F₂ B5 X⊓normalizer (p.cubicSubgroup X:Set G)

def secondCubicNormalizerAction (B5:Sylow 5 d.toTypeRuSetup.H) (X:Sylow 3 p.parabolic)
    (e:p.A B5≃*firstParabolicCore) : secondCubicNormalizer B5 X→*MulAut firstParabolicCore :=
  (secondCoreAction B5 e).comp (inclusion (inf_le_left.trans (p.F₂_le_parabolic B5 X)))

/-- Data supplied by the proved source cubic-marking theorem. -/
structure SecondCubicMarking (B5:Sylow 5 d.toTypeRuSetup.H) where
  X:Sylow 3 p.parabolic
  coordinates:p.A B5≃*firstParabolicCore
  generator:X
  quotient:Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3))
  generator_order:orderOf generator=3
  conjugation:∀a:firstParabolicCore,
    (coordinates.symm (CubicAction.cubic a):G)=
      ((generator:p.parabolic):G)*(coordinates.symm a:G)*((generator:p.parabolic):G)⁻¹

theorem SourceChoice.secondCubicMarking_nonempty (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Nonempty (SecondCubicMarking (p:=p) B5) := by
  obtain ⟨X,e,x,hm,hx,hact⟩:=s.exists_A_native_cubic_marking B5 hi
  exact ⟨⟨X,e,x,hm,hx,hact⟩⟩

namespace SecondCubicMarking
variable {B5:Sylow 5 d.toTypeRuSetup.H} (m:SecondCubicMarking (p:=p) B5)

theorem generator_ambient_order : orderOf ((m.generator:p.parabolic):G)=3 := by
  simpa only [orderOf_coe] using m.generator_order

theorem cubicSubgroup_eq_zpowers : p.cubicSubgroup m.X=zpowers ((m.generator:p.parabolic):G) := by
  symm
  apply eq_of_le_of_card_ge (zpowers_le.mpr (mem_map_of_mem p.parabolic.subtype m.generator.property))
  have hc:=p.card_cubicSubgroup m.X
  have hc' : Nat.card ((m.X : Subgroup p.parabolic).map p.parabolic.subtype)=3 := by
    simpa [Plane.cubicSubgroup] using hc
  have ho:=m.generator_ambient_order
  change orderOf (p.parabolic.subtype (m.generator:p.parabolic))=3 at ho
  rw [hc',Nat.card_zpowers,ho]

theorem action_generator : secondCoreAction B5 m.coordinates (m.generator:p.parabolic)=CubicAction.cubic := by
  apply MulEquiv.ext
  intro a
  apply m.coordinates.symm.injective
  apply Subtype.ext
  have hh:=secondCoreAction_apply B5 m.coordinates (m.generator:p.parabolic) (m.coordinates.symm a)
  rw [m.coordinates.apply_symm_apply] at hh
  exact hh.trans (m.conjugation a).symm

theorem fixed_iff_commute (a:p.A B5) :
    CubicAction.cubic (m.coordinates a)=m.coordinates a ↔
      Commute (a:G) ((m.generator:p.parabolic):G) := by
  constructor
  · intro hf
    have hh:=m.conjugation (m.coordinates a)
    rw [hf,m.coordinates.symm_apply_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  · intro hc
    apply m.coordinates.symm.injective
    apply Subtype.ext
    rw [m.conjugation,m.coordinates.symm_apply_apply]
    exact mul_inv_eq_iff_eq_mul.mpr hc.symm.eq

theorem fixed_iff_mem_centralizer (a:p.A B5) :
    CubicAction.cubic (m.coordinates a)=m.coordinates a ↔
      (a:G)∈centralizer (p.cubicSubgroup m.X:Set G) := by
  rw [m.cubicSubgroup_eq_zpowers,zpowers_eq_closure,centralizer_closure,mem_centralizer_singleton_iff]
  exact m.fixed_iff_commute a

end SecondCubicMarking
end CFSG.Quasithin.ChapterJ.RuSubgroup
