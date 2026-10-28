module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.MSReduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup

/-!
# Native symplectic data for the MS93 holomorph graph

The source retains its actual component, edge group and binary natural module.
One map into S6 marks both the component image A6 and the conjugation action;
it need not be onto S6 after characteristic replacement. The edge group is a
two-group containing the two-core and satisfies MS3. Its marked fixed vector
makes it nontrivial, so the generic free-holomorph tree geometry applies.

This interface has no weak-BN classification, critical-distance bound or
whole-core conclusion. Its actual original and reduced realizations preserve
all subgroup inclusions and the specified natural coordinates.

Source: Meierfrankenfeld--Stellmacher (1993), Sections 3.0 and 7,
printed pp.859 and 932--933; Aschbacher--Smith C.1.32 and C.1.37.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
variable {M : Type*} [Group M]

/-- The actual symplectic source before critical-distance analysis. The
projection retains the original S6 coordinates and may have image A6 or S6. -/
structure Source (L R W : Subgroup M) [L.Normal] [W.Normal] where
  two_group : IsPGroup 2 R
  core_le : pCore 2 M ≤ R
  characteristic : MSCharacteristicCondition R
  product : ∀ m : M, ∃ l ∈ L, ∃ r ∈ R, l * r = m
  residual : pResidual 2 M = L
  projection : M →* Equiv.Perm (Fin 6)
  projection_kernel : projection.ker = pCore 2 M
  component_image : L.map projection = alternatingGroup (Fin 6)
  module_le_core : W ≤ pCore 2 M
  module_le_component : W ≤ L
  coordinates : W ≃* Multiplicative (BinaryPermutation.natural (Fin 6))
  action : ∀ g w, (coordinates (MulAut.conjNormal g w)).toAdd =
    BinaryPermutation.naturalRepresentation (Fin 6) (projection g) (coordinates w).toAdd
  w : W
  w_ne : w ≠ 1
  radical_fixes : ∀ r ∈ R, r * (w : M) = (w : M) * r

namespace Source
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

theorem sup_eq_top : L ⊔ R = ⊤ := by
  apply top_unique
  intro m _
  obtain ⟨l,hl,r,hr,rfl⟩ := s.product m
  exact mul_mem (mem_sup_left hl) (mem_sup_right hr)

theorem radical_ne_bot : R ≠ ⊥ := by
  intro hz
  have hw : (s.w : M) ∈ R := s.core_le (s.module_le_core s.w.property)
  have hw0 : (s.w : M) ∈ (⊥ : Subgroup M) := hz ▸ hw
  exact s.w_ne (Subtype.ext (mem_bot.mp hw0))

theorem image_contains_alternating : alternatingGroup (Fin 6) ≤ s.projection.range := by
  rw [← s.component_image]
  rintro _ ⟨l,_,rfl⟩
  exact ⟨l,rfl⟩

/-- The generic holomorph graph uses the finite source groups, with no
finiteness hypothesis on the free amalgam or its vertex set. -/
theorem geometry [Finite M] : Geometry R :=
  CFSG.Quasithin.ChapterC.BinaryMS.MS93.geometry R s.two_group s.radical_ne_bot s.characteristic

theorem component_twoPerfect [Finite M] : IsPPerfect 2 L := by
  rw [← s.residual]
  exact isPPerfect_pResidual 2

/-- The ambient commutator core is the literal intrinsic component core. -/
theorem commutatorCore_eq_internal [Finite M] :
    ⁅pCore 2 M,L⁆ = (⁅pCore 2 L,(⊤ : Subgroup L)⁆).map L.subtype := by
  apply le_antisymm
  · exact commutator_le_core_commutator_of_isSubnormal L (pCore 2 M)
      (inferInstance : L.Normal).isSubnormal s.component_twoPerfect pCore_isPGroup
      (by rw [normalizer_eq_top]; exact le_top)
  · rw [map_commutator,← MonoidHom.range_eq_map,range_subtype]
    apply commutator_mono _ le_rfl
    rw [pCore_subnormal_eq_comap 2 (inferInstance : L.Normal).isSubnormal,
      map_comap_eq,range_subtype]
    exact inf_le_right

end Source
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
