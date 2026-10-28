module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.Rows
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentDescent

/-!
# The first factor's quotient module in B.5.12

The centralizer product identifies fixed vectors of the first factor on its
moved space with globally fixed vectors there. This identifies the original
moved-section quotient with its literal image in V/C_V(G). The five B.5.9
rows consequently give the natural or doubled source factor cases. In the
symmetric-five row, its fixed supplement proves that [V,L]=[V,LA]. The
four-dimensional moved cover has a natural three-dimensional quotient; it
is kept distinct from the four-dimensional upper extension in B.4.8(3).

All action equivalences use the original inclusions and quotient maps.
The consumer is the source factor case for B.5.12's first component.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9–12,
printed pp.107–109, and B.4.8(2), printed p.91.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.FactorExtraction
open QuasisimpleSource QuasisimpleSource.ExtensionConsequences
open ComponentReduction ComponentReduction.ProductGeometry
universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

noncomputable def imageActionOfDisjoint (U : Subrepresentation ρ) (A : Subgroup G)
    (hd : Disjoint U.toSubmodule ρ.invariants) :
    ActionEquiv (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype)
      (U.toRepresentation.comp A.subtype) :=
  actionSymm ⟨MulEquiv.refl A, imageEquivOfDisjoint U hd,
    fun g v => imageEquivOfDisjoint_equivariant U hd g v⟩

noncomputable def sectionImageAction {L B : Subgroup G} (s : MovedSection ρ L)
    (hp : InternalProduct L B) (hw : s.space.toSubmodule ≤ fixedSpace ρ B) :
    ActionEquiv (s.action.comp L.subtype)
      (((fixed ρ).quotientImage s.space).toRepresentation.comp L.subtype) := by
  let f : s.space.toSubmodule →ₗ[ZMod 2]
      ((fixed ρ).quotientImage s.space).toSubmodule := {
    toFun := fun v => ⟨ρ.invariants.mkQ v, ⟨v, v.property, rfl⟩⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have hk : s.central.toSubmodule = f.ker := by
    ext v
    rw [s.central_eq]
    change (∀ g : L, s.space.toRepresentation g v = v) ↔ f v = 0
    constructor
    · intro hv
      apply Subtype.ext
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      intro g
      obtain ⟨a,b,rfl⟩ := hp.exists_mul g
      rw [map_mul, Module.End.mul_apply, show ρ (b : G) v = v from hw v.property b]
      exact congrArg Subtype.val (hv a)
    · intro hv g
      apply Subtype.ext
      have hx : (v : V) ∈ ρ.invariants :=
        (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hv)
      exact hx g
  let q := s.central.toSubmodule.liftQ f hk.le
  have hq : Function.Bijective q := by
    constructor
    · apply (injective_iff_map_eq_zero _).mpr
      intro v hv
      induction v using Submodule.Quotient.induction_on with
      | _ v => exact (Submodule.Quotient.mk_eq_zero _).mpr (hk.symm ▸ hv)
    · rintro ⟨q, v, hv, rfl⟩
      exact ⟨s.central.toSubmodule.mkQ ⟨v, hv⟩, rfl⟩
  refine ⟨MulEquiv.refl _, LinearEquiv.ofBijective q hq, ?_⟩
  intro g v
  induction v using Submodule.Quotient.induction_on with | _ v => rfl

private theorem global_disjoint {L : Subgroup G} (s : MovedSection ρ L)
    (hz : Representation.invariants (s.space.toRepresentation.comp L.subtype) = ⊥) :
    Disjoint s.space.toSubmodule ρ.invariants := by
  have hi : ρ.invariants ≤ fixedSpace ρ L := fun _ hv g => hv g
  exact (moved_disjoint_fixed s hz).mono_right hi

private theorem moved_eq_of_fixed_supplement {L H : Subgroup G}
    (s : MovedSection ρ L) (hLH : L ≤ H)
    (hs : s.space.toSubmodule ⊔ fixedSpace ρ H = ⊤) :
    s.space.toSubmodule = moved ρ H := by
  apply le_antisymm
  · rw [s.space_eq]
    apply Submodule.span_mono
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact ⟨g,hLH hg,v,hv,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp
      (hs.symm ▸ Submodule.mem_top (x := v))
    rw [map_add, show ρ g z = z from hz ⟨g,hg⟩, add_sub_add_right_eq_sub]
    exact s.space.toSubmodule.sub_mem (s.space.apply_mem_toSubmodule g hw) hw

/-- Every one of B.5.9's five cases gives the first factor's source row on
its actual image modulo the global fixed space. -/
theorem first_factor_case [Finite G] [Module.Finite (ZMod 2) V]
    {A L H : Subgroup G} [L.Normal] (s : MovedSection ρ L)
    (hc : ComponentActionCase ρ A L s H)
    (hp : ProductConfiguration ρ H s.space) : SourceFactorCase ρ H s.space := by
  have hw : s.space.toSubmodule ≤ fixedSpace ρ (centralizer (H : Set G)) := by
    rw [hp.centralizer_eq]
    exact le_fixedSpace_subspaceKernel ρ s.space.toSubmodule ⊤
  cases hc with
  | linearTwo F hn _ _ =>
    exact .natural s.space_eq (.linearTwo F
      ⟨transAction (actionSymm (sectionImageAction s hp.product hw)) hn.some⟩)
  | symmetricFive e _ hs =>
    have hi : ρ.invariants ≤ fixedSpace ρ L := fun _ hv g => hv g
    have hd : Disjoint s.space.toSubmodule ρ.invariants :=
      (symmetricFive_isCompl s e).disjoint.mono_right hi
    have hsup : s.space.toSubmodule ⊔ fixedSpace ρ (L ⊔ A) = ⊤ := by
      rw [symmetricFive_fixed_eq s e hs]
      exact (symmetricFive_isCompl s e).sup_eq_top
    exact .natural (moved_eq_of_fixed_supplement s le_sup_left hsup)
      (.symmetricFive ⟨transAction (imageActionOfDisjoint s.space (L ⊔ A) hd) e.action⟩)
  | doubleThree F ho hn _ _ =>
    have hd := global_disjoint s (invariants_of_equiv hn.some
      (repeated_invariants 2 (linearNatural_invariants F (by decide : 2 ≤ 3))))
    exact .doubleNatural F ho s.space_eq
      ⟨transAction (imageActionOfDisjoint s.space L hd) hn.some⟩
  | naturalThree F ho hn _ =>
    have hd := global_disjoint s (invariants_of_equiv hn.some
      (linearNatural_invariants F (by decide : 2 ≤ 3)))
    exact .natural s.space_eq (.linearThree F ho
      ⟨transAction (imageActionOfDisjoint s.space L hd) hn.some⟩)
  | fourCover cover _ _ _ =>
    let e := Localization.central_natural_of_reduced s BinaryField.two 3 cover.natural
    exact .natural s.space_eq (.linearThree BinaryField.two (by decide)
      ⟨transAction (actionSymm (sectionImageAction s hp.product hw)) e⟩)

end CFSG.Quasithin.ChapterB.SourceInduction.FactorExtraction
