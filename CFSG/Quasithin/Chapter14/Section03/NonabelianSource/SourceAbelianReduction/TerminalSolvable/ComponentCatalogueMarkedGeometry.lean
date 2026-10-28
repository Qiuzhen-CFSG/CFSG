module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernelTwoCopies

/-!
# Genuine G.9 input for the original marked constituent

The normal component orbit has at most two components. Original homogeneity
identifies their actions on the same selected constituent. This geometry
descends through the actual action kernel, preserving the selected moved
component, the whole component orbit and its SQTK cover.

The faithful-actor case uses the original actor rank. The two-copy case uses
the proved order-two kernel and its exact quotient rank dim(I)-2. Both exports
supply every field of G.9.3; no model-exhaustion premise is assumed here.
Source: Aschbacher–Smith G.11.7–8, printed pp.366–369, and 14.3.15, p.994.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
section
variable {G : Type*} [Group G] [Finite G]
private theorem marked_orbit_pair (L : Subgroup G) (hi : (normalizer (L : Set G)).index ≤ 2) :
    componentOrbit L ⊤ = L ∨ ∃ g : G,
      componentOrbit L ⊤ = L ⊔ L.map (MulAut.conj g).toMonoidHom := by
  classical
  by_cases hn : L.Normal
  · let := hn
    left
    apply le_antisymm ?_ (le_componentOrbit L ⊤)
    exact iSup_conjugates_le_of_le_normalizer L ⊤ L le_rfl (by rw [normalizer_eq_top_iff.mpr hn])
  have hidx : (normalizer (L : Set G)).index = 2 := by
    have hp := (normalizer (L : Set G)).index_ne_zero_of_finite
    have h1 : (normalizer (L : Set G)).index ≠ 1 := by
      intro he
      exact hn (normalizer_eq_top_iff.mp (index_eq_one.mp he))
    omega
  have hN : normalizer (L : Set G) ≠ ⊤ := fun he => hn (normalizer_eq_top_iff.mp he)
  have hex : ∃ g : G, g ∉ normalizer (L : Set G) := by
    by_contra! hall
    exact hN (eq_top_iff.mpr (fun g _ => hall g))
  obtain ⟨g,hg⟩ := hex
  right
  refine ⟨g,le_antisymm ?_ (sup_le (le_componentOrbit L ⊤) ?_)⟩
  · refine iSup_le fun a => ?_
    by_cases ha : (a : G) ∈ normalizer (L : Set G)
    · have he : L.map (MulAut.conj (a : G)).toMonoidHom = L :=
        mem_normalizer_iff_map_conj_eq.mp ha
      rw [he]
      exact le_sup_left
    have hga : g⁻¹ * (a : G) ∈ normalizer (L : Set G) :=
      (mul_mem_iff_of_index_two hidx).mpr (iff_of_false (by simpa using hg) ha)
    have he : L.map (MulAut.conj (a : G)).toMonoidHom = L.map (MulAut.conj g).toMonoidHom := by
      calc
        _ = (L.map (MulAut.conj (g⁻¹ * (a : G))).toMonoidHom).map
            (MulAut.conj g).toMonoidHom := by
          rw [map_map]
          congr 1
          ext x
          simp [MulAut.conj_apply,mul_assoc]
        _ = _ := congrArg (map (MulAut.conj g).toMonoidHom)
          (mem_normalizer_iff_map_conj_eq.mp hga)
    rw [he]
    exact le_sup_right
  · exact le_iSup (fun a : (⊤ : Subgroup G) => L.map (MulAut.conj (a : G)).toMonoidHom)
      ⟨g,mem_top g⟩

end

private theorem components_to_image
    {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L H : Subgroup D)
    (hfH : Function.Injective (ρ.comp H.subtype))
    (hc : H = L ∨ ∃ L₂ : Subgroup D, IsComponent D L₂ ∧ H = L ⊔ L₂ ∧
      ChapterG.Section09.Quasiequivalent (ρ.comp L.subtype) (ρ.comp L₂.subtype)) :
    let q := QuotientGroup.mk' ρ.ker
    H.map q = L.map q ∨ ∃ L₂ : Subgroup (D ⧸ ρ.ker), IsComponent _ L₂ ∧
      H.map q = L.map q ⊔ L₂ ∧
      (ChapterG.Section09.Quasiequivalent ((kerRepresentation ρ).comp (L.map q).subtype)
        ((kerRepresentation ρ).comp L₂.subtype) ∨
       ChapterG.Section09.Quasiequivalent ((kerRepresentation ρ).comp (L.map q).subtype)
        (Representation.dual ((kerRepresentation ρ).comp L₂.subtype))) := by
  let q := QuotientGroup.mk' ρ.ker
  have hfaith (J : Subgroup D) (hJ : J ≤ H) : Function.Injective (ρ.comp J.subtype) := by
    intro a b he
    exact Subtype.ext (congrArg (fun z : H => (z : D))
      (hfH (a₁ := ⟨a,hJ a.property⟩) (a₂ := ⟨b,hJ b.property⟩) he))
  rcases hc with he | ⟨L₂,h₂,he,hmodel⟩
  · exact Or.inl (congrArg (Subgroup.map q) he)
  have hLH : L ≤ H := he ▸ le_sup_left
  have h₂H : L₂ ≤ H := he ▸ le_sup_right
  let eL := ChapterG.Section09.actionImageEquiv ρ (kerRepresentation ρ) q rfl L (hfaith L hLH)
  let e₂ := ChapterG.Section09.actionImageEquiv ρ (kerRepresentation ρ) q rfl L₂ (hfaith L₂ h₂H)
  have h₂0 : L₂.map q ≠ ⊥ := by
    intro hz
    have hbot : L₂ = ⊥ := by
      apply _root_.eq_bot_iff.mpr
      intro l hl
      have hh : e₂ ⟨l,hl⟩ = 1 := Subtype.ext (hz.le (e₂ ⟨l,hl⟩).property)
      exact congrArg Subtype.val (e₂.injective (hh.trans e₂.map_one.symm))
    let := h₂.2
    let : IsSimpleGroup (L₂ ⧸ center L₂) := IsQuasisimple.simple
    let : Nontrivial L₂ := (QuotientGroup.mk'_surjective (center L₂)).nontrivial
    exact (nontrivial_iff_ne_bot L₂).mp inferInstance hbot
  refine Or.inr ⟨_,(h₂.map_surjective q (QuotientGroup.mk'_surjective _)).resolve_left h₂0,?_,Or.inl ?_⟩
  · rw [he,Subgroup.map_sup]
  · obtain ⟨e,c,hc⟩ := hmodel
    refine ⟨eL.symm.trans (e.trans e₂),c,?_⟩
    intro l w
    obtain ⟨a,rfl⟩ := eL.surjective l
    simp only [MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
    exact hc a w

private theorem constituent_components_to_image
    {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L H A : Subgroup D)
    (I : Submodule (ZMod 2) V)
    (hH : H ≤ subspaceStabilizer ρ I) (hA : A ≤ subspaceStabilizer ρ I)
    (hLH : L ≤ H)
    (hfH : Function.Injective (invariantSubspace ρ H I hH).toRepresentation)
    (hc : H = L ∨ ∃ L₂ : Subgroup D, ∃ h₂H : L₂ ≤ H,
      IsComponent D L₂ ∧ H = L ⊔ L₂ ∧
      ChapterG.Section09.Quasiequivalent
        (invariantSubspace ρ L I (hLH.trans hH)).toRepresentation
        (invariantSubspace ρ L₂ I (h₂H.trans hH)).toRepresentation) :
    let P := H ⊔ A
    let σ := ChapterG.Section09.constituentAction ρ H A I hH hA
    let q := QuotientGroup.mk' σ.ker
    (H.subgroupOf P).map q = (L.subgroupOf P).map q ∨
      ∃ L₂ : Subgroup (P ⧸ σ.ker), IsComponent _ L₂ ∧
        (H.subgroupOf P).map q = (L.subgroupOf P).map q ⊔ L₂ ∧
        (ChapterG.Section09.Quasiequivalent
          ((kerRepresentation σ).comp ((L.subgroupOf P).map q).subtype)
          ((kerRepresentation σ).comp L₂.subtype) ∨
         ChapterG.Section09.Quasiequivalent
          ((kerRepresentation σ).comp ((L.subgroupOf P).map q).subtype)
          (Representation.dual ((kerRepresentation σ).comp L₂.subtype))) := by
  let P := H ⊔ A
  let σ := ChapterG.Section09.constituentAction ρ H A I hH hA
  have hHP : H ≤ P := le_sup_left
  have hLP : L ≤ P := hLH.trans hHP
  have hf : Function.Injective (σ.comp (H.subgroupOf P).subtype) :=
    hfH.comp (subgroupOfEquivOfLe hHP).injective
  apply components_to_image σ (L.subgroupOf P) (H.subgroupOf P) hf
  rcases hc with he | ⟨L₂,h₂H,h₂,he,hmodel⟩
  · exact Or.inl (congrArg (fun J => J.subgroupOf P) he)
  have h₂P := h₂H.trans hHP
  refine Or.inr ⟨L₂.subgroupOf P,h₂.subgroupOf h₂P,?_,?_⟩
  · exact (congrArg (fun J : Subgroup D => J.subgroupOf P) he).trans
      (subgroupOf_sup hLP h₂P)
  · obtain ⟨e,c,hc⟩ := hmodel
    let eL := subgroupOfEquivOfLe hLP
    let e₂ := subgroupOfEquivOfLe h₂P
    refine ⟨eL.trans (e.trans e₂.symm),c,?_⟩
    intro a w
    exact hc (eL a) w

open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

/-- The actual normal orbit consists of one or two components, with the
same constituent actions quasiequivalent by original homogeneity. -/
theorem constituent_components :
    componentOrbit L ⊤ = L ∨ ∃ L₂ : Subgroup F.TerminalHdot,
      ∃ h₂H : L₂ ≤ componentOrbit L ⊤,
      IsComponent F.TerminalHdot L₂ ∧ componentOrbit L ⊤ = L ⊔ L₂ ∧
      ChapterG.Section09.Quasiequivalent
        (invariantSubspace F.terminalRepresentation L I
          ((le_componentOrbit L ⊤).trans s.selected.invariant)).toRepresentation
        (invariantSubspace F.terminalRepresentation L₂ I
          (h₂H.trans s.selected.invariant)).toRepresentation := by
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  have hind := Recognition.terminal_component_normalizer_index_le_two
    s.simple F (by decide) L s.component
  rcases marked_orbit_pair L hind with he | ⟨a,he⟩
  · exact Or.inl he
  have h₂H : L.map (MulAut.conj a).toMonoidHom ≤ componentOrbit L ⊤ := by
    rw [he]
    exact le_sup_right
  refine Or.inr ⟨_,h₂H,s.component.map_equiv (MulAut.conj a),he,?_⟩
  exact ChapterG.Section09.constituent_quasiequivalent_conjugate
    F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
    s.irreducible (fun J hJ => s.constituents_sameModule J hJ)
    L (le_componentOrbit L ⊤) a _ _

/-- G.9.3 on the original marked action quotient when the original actor
acts faithfully, retaining the originally moved component and its whole orbit. -/
theorem componentHypothesis_of_actorFaithful
    (hf : ActorFaithful (F := F) (g := g) (I := I)) :
    let H := componentOrbit L ⊤
    let X := F.terminalDot (F.X g)
    let σ := MarkedAction.action F.terminalRepresentation H X I
      s.selected.invariant s.actor_stabilizes
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple (kerRepresentation σ)
      (MarkedAction.image F.terminalRepresentation H X I
        s.selected.invariant s.actor_stabilizes X)
      (MarkedAction.image F.terminalRepresentation H X I
        s.selected.invariant s.actor_stabilizes L)
      (MarkedAction.image F.terminalRepresentation H X I
        s.selected.invariant s.actor_stabilizes H)
      (finrank (ZMod 2) (Additive X)) := by
  let H := componentOrbit L ⊤
  let X := F.terminalDot (F.X g)
  let : H.Normal := componentOrbit_top_normal L
  let R := invariantSubspace F.terminalRepresentation H I s.selected.invariant
  have hfX : Function.Injective
      (invariantSubspace F.terminalRepresentation X I s.actor_stabilizes).toRepresentation := by
    intro a b he
    apply hf
    apply LinearMap.ext
    intro w
    exact congrArg Subtype.val (LinearMap.congr_fun he w)
  apply ChapterG.Section09.componentHypothesis_constituent F.terminalRepresentation
    ⟨Recognition.terminal_sqtkCover s.simple F (by decide)⟩ X L H I
    s.selected.invariant s.actor_stabilizes (s.constituent_faithful R s.irreducible)
    hfX s.irreducible _ _ _ s.component s.moved (le_componentOrbit L ⊤)
    s.constituent_components
  · exact (Nat.card_congr Additive.toMul).symm.trans (by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X)))
  · have hi := I.finrank_le
    have hd := s.actor_dimension
    omega

/-- Component pair geometry descends through the actual constituent quotient. -/
theorem image_constituent_components :
    let H := componentOrbit L ⊤
    let X := F.terminalDot (F.X g)
    let σ := MarkedAction.action F.terminalRepresentation H X I
      s.selected.invariant s.actor_stabilizes
    let q := QuotientGroup.mk' σ.ker
    (H.subgroupOf (H ⊔ X)).map q = (L.subgroupOf (H ⊔ X)).map q ∨
      ∃ L₂ : Subgroup (↥(H ⊔ X) ⧸ σ.ker), IsComponent _ L₂ ∧
        (H.subgroupOf (H ⊔ X)).map q = (L.subgroupOf (H ⊔ X)).map q ⊔ L₂ ∧
        (ChapterG.Section09.Quasiequivalent
          ((kerRepresentation σ).comp ((L.subgroupOf (H ⊔ X)).map q).subtype)
          ((kerRepresentation σ).comp L₂.subtype) ∨
         ChapterG.Section09.Quasiequivalent
          ((kerRepresentation σ).comp ((L.subgroupOf (H ⊔ X)).map q).subtype)
          (Representation.dual ((kerRepresentation σ).comp L₂.subtype))) := by
  exact constituent_components_to_image F.terminalRepresentation L (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
    (le_componentOrbit L ⊤)
    (s.constituent_faithful (invariantSubspace F.terminalRepresentation
      (componentOrbit L ⊤) I s.selected.invariant) s.irreducible) s.constituent_components

/-- G.9.3 on the original two-copy constituent quotient, retaining both
actual components when the whole orbit is not a single component. -/
theorem componentHypothesis_of_double_dimension
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I) :
    let H := componentOrbit L ⊤
    let X := F.terminalDot (F.X g)
    let σ := MarkedAction.action F.terminalRepresentation H X I
      s.selected.invariant s.actor_stabilizes
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple (kerRepresentation σ)
      (MarkedAction.image F.terminalRepresentation H X I
        s.selected.invariant s.actor_stabilizes X)
      (MarkedAction.image F.terminalRepresentation H X I
        s.selected.invariant s.actor_stabilizes L)
      (MarkedAction.image F.terminalRepresentation H X I
        s.selected.invariant s.actor_stabilizes H) (Module.finrank (ZMod 2) I - 2) := by
  let H := componentOrbit L ⊤
  let X := F.terminalDot (F.X g)
  let P := H ⊔ X
  let σ := MarkedAction.action F.terminalRepresentation H X I
    s.selected.invariant s.actor_stabilizes
  let q := QuotientGroup.mk' σ.ker
  let : H.Normal := componentOrbit_top_normal L
  have hHP : H ≤ P := le_sup_left
  have hLP : L ≤ P := (le_componentOrbit L ⊤).trans hHP
  have hXP : X ≤ P := le_sup_right
  let R := invariantSubspace F.terminalRepresentation H I s.selected.invariant
  have hfH := s.constituent_faithful R s.irreducible
  let eL := MarkedAction.subgroupEquiv F.terminalRepresentation H X I
    s.selected.invariant s.actor_stabilizes hfH L (le_componentOrbit L ⊤)
  have hL0 : (L.subgroupOf P).map q ≠ ⊥ := by
    intro hz
    have hbot : L = ⊥ := by
      apply _root_.eq_bot_iff.mpr
      intro l hl
      have he : eL ⟨l, hl⟩ = 1 := Subtype.ext (hz.le (eL ⟨l, hl⟩).property)
      exact congrArg Subtype.val (eL.injective (he.trans eL.map_one.symm))
    exact s.moved (by rw [hbot, commutator_bot_left])
  refine { s.actorImage_setup_of_double_dimension hk hd with
    quotient := ⟨s.constituentSQTKCover⟩
    component := ((s.component.subgroupOf hLP).map_surjective q
      (QuotientGroup.mk'_surjective _)).resolve_left hL0
    noncentral := ?_
    normal_H := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    irreducible := ?_
    components := s.image_constituent_components }
  · intro hz
    apply s.moved
    have hP : ⁅L.subgroupOf P, X.subgroupOf P⁆ = ⊥ := by
      apply _root_.eq_bot_iff.mpr
      intro x hx
      have hxH : x ∈ H.subgroupOf P :=
        ((commutator_mono (subgroupOf_mono P (le_componentOrbit L ⊤)) le_rfl).trans
          (commutator_le_left (H.subgroupOf P) (X.subgroupOf P))) hx
      have hqx : q x = 1 := by
        have hm : q x ∈ (⁅L.subgroupOf P, X.subgroupOf P⁆).map q := mem_map.mpr ⟨x, hx, rfl⟩
        rw [map_commutator, hz] at hm
        exact hm
      have heH : (⟨x, hxH⟩ : H) = 1 :=
        MarkedAction.projection_injective_on_orbit F.terminalRepresentation H X I
          s.selected.invariant s.actor_stabilizes hfH _ _ (hqx.trans q.map_one.symm)
      exact Subtype.ext (congrArg (fun z : H => (z : F.TerminalHdot)) heH)
    have he := congrArg (Subgroup.map P.subtype) hP
    rw [map_commutator, map_subgroupOf_eq_of_le hLP, map_subgroupOf_eq_of_le hXP,
      Subgroup.map_bot] at he
    exact he
  · apply (irreducible_comp_surjective_iff (q.subgroupMap (H.subgroupOf P))
      (q.subgroupMap_surjective _) _).mp
    change IsIrreducible (σ.comp (H.subgroupOf P).subtype)
    let eH := subgroupOfEquivOfLe hHP
    have hh : σ.comp (H.subgroupOf P).subtype =
        R.toRepresentation.comp eH.toMonoidHom := rfl
    rw [hh]
    exact (irreducible_comp_surjective_iff eH.toMonoidHom eH.surjective
      R.toRepresentation).mpr s.irreducible

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
