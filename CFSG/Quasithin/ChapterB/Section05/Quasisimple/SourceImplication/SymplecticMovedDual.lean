module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import Theory.Representation.SymplecticFourOrthogonalCover.DualFixed

/-!
# Fixed vectors in a recognized symplectic moved section

When the full module has zero fixed space, its literal moved section has
zero central kernel. The retained action equivalence then embeds the natural
module in the full module as a dual cover. An actor preserving no quadratic
refinement in those same coordinates fixes only vectors in that moved space.
Source: MS93 (1.5)(ii), as applied in (5.12)(2), printed p.926.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
open Representation.SymplecticFourOrthogonalCover
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The original full module is a dual cover in the retained natural marking;
the actor's fixed space therefore lies in the literal full moved space. -/
theorem fixedSpace_le_moved_of_symplectic_no_refinement
    (ρ : Representation (ZMod 2) G V) (E : BinaryField)
    (hE : 2 < Nat.card E.Carrier)
    (e : ActionEquiv ((MovedSection.ofNormal ρ ⊤).action.comp
      (⊤ : Subgroup G).subtype) (binarySymplectic E))
    (hzero : fixedSpace ρ ⊤ = ⊥) (A : Subgroup G)
    (hno : ¬ ∃ c : Vector E.Carrier,
      ∀ x : A.map (topEquiv.symm.trans e.groupEquiv).toMonoidHom,
        ∀ v, refinement c (x.val • v) = refinement c v) :
    fixedSpace ρ A ≤ subspaceCommutator ρ ⊤ ⊤ := by
  let s := MovedSection.ofNormal ρ (⊤ : Subgroup G)
  let α : G ≃* Sp E.Carrier := topEquiv.symm.trans e.groupEquiv
  let p := s.coverProjection e
  have hp : Function.Bijective p := by
    refine ⟨?_,e.linearEquiv.surjective.comp (Submodule.mkQ_surjective _)⟩
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    have hz : s.central.toSubmodule.mkQ v = 0 :=
      e.linearEquiv.injective (hv.trans e.linearEquiv.map_zero.symm)
    have hmem := (Submodule.Quotient.mk_eq_zero s.central.toSubmodule).mp hz
    rw [s.central_eq] at hmem
    have hvfix : v.val ∈ fixedSpace ρ ⊤ := fun g => congrArg Subtype.val (hmem g)
    have hvzero : v.val = 0 := by simpa only [hzero,Submodule.mem_bot] using hvfix
    exact Subtype.ext hvzero
  let pe : s.space.toSubmodule ≃ₗ[ZMod 2] Vector E.Carrier :=
    LinearEquiv.ofBijective p.toLinearMap hp
  let τ := ρ.comp (α.symm.toMonoidHom.comp (_root_.commutator (Sp E.Carrier)).subtype)
  let i : (binaryNatural (K := E.Carrier)).IntertwiningMap τ :=
    (s.space.toSubmodule.subtype.comp pe.symm.toLinearMap).intertwiningMap_of_isIntertwiningMap
      _ _ (by
        intro g v
        change (pe.symm (binaryNatural g v)).val = ρ (α.symm g.val) (pe.symm v).val
        have he : pe.symm (binaryNatural g v) =
            s.coverAction e g.val (pe.symm v) := by
          apply pe.injective
          rw [pe.apply_symm_apply]
          change binaryNatural g v = p (s.coverAction e g.val (pe.symm v))
          rw [p.isIntertwining]
          change binaryNatural g v = binaryNatural g (pe (pe.symm v))
          rw [pe.apply_symm_apply]
        exact congrArg Subtype.val he)
  have hi : Function.Injective i := Subtype.val_injective.comp pe.symm.injective
  have hrange : i.toLinearMap.range = s.space.toSubmodule := by
    apply le_antisymm
    · rintro _ ⟨v,rfl⟩
      exact (pe.symm v).property
    · intro v hv
      refine ⟨pe ⟨v,hv⟩,?_⟩
      change (pe.symm (pe ⟨v,hv⟩)).val = v
      rw [pe.symm_apply_apply]
  have hderived : _root_.commutator (Sp E.Carrier) = ⊤ :=
    OneCohomology.SymplecticFour.LargeField.commutator_eq_top hE
  have hdual : IsDualCover i.range := by
    constructor
    · intro g v
      change τ g v - v ∈ i.toLinearMap.range
      rw [hrange,s.space_eq]
      exact Submodule.subset_span ⟨α.symm g.val,mem_top _,v,Submodule.mem_top,rfl⟩
    · apply bot_unique
      intro v hv
      have hv' : v ∈ fixedSpace ρ ⊤ := by
        intro g
        let x : _root_.commutator (Sp E.Carrier) := ⟨α g.val,by rw [hderived]; trivial⟩
        have hx := hv x
        change ρ (α.symm (α g.val)) v = v at hx
        change ρ g.val v = v
        simpa only [α.symm_apply_apply] using hx
      simpa only [hzero] using hv'
  let A' := (A.map α.toMonoidHom).subgroupOf (_root_.commutator (Sp E.Carrier))
  have hn : ¬ ∃ c : Vector E.Carrier, ∀ g : A', ∀ v,
      refinement c (binaryNatural g.val v) = refinement c v := by
    rintro ⟨c,hc⟩
    apply hno
    refine ⟨c,?_⟩
    intro x v
    let g : _root_.commutator (Sp E.Carrier) := ⟨x.val,by rw [hderived]; trivial⟩
    exact hc ⟨g,x.property⟩ v
  have hfix := dualCover_fixed_le_natural_of_no_refinement i hi hdual A' hn
  intro v hv
  change v ∈ moved ρ ⊤
  rw [←s.space_eq,←hrange]
  apply hfix
  intro g
  obtain ⟨a,ha,he⟩ := g.property
  change α a = g.val.val at he
  change ρ (α.symm g.val.val) v = v
  rw [←he,α.symm_apply_apply]
  exact hv ⟨a,ha⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource
