module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulAction
public import CFSG.Quasithin.ChapterG.Section09.ConstituentActionDual
public import CFSG.Quasithin.ChapterG.Section09.ConstituentConjugateDual

/-!
# The component geometry of the exchanged constituent

The exchanged pair bounds the whole degree by twice the constituent degree.
An ambient translate is therefore either the original constituent or a
complement, by the retained disjointness theorem. The invariant alternating
form turns a complementary translate into its dual. The component-normalizer
index bound supplies at most two conjugate components, and the comparison
survives restriction to HY and its literal faithful action quotient.

Source: Aschbacher--Smith G.10.15 and G.11.6, printed pp.361--366.
-/
@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
section
variable {G : Type*} [Group G] [Finite G]
private theorem orbit_pair (L : Subgroup G) (hi : (normalizer (L : Set G)).index ≤ 2) :
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

open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace ExchangedFaithfulSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedFaithfulSource T M Mc F g B v L I)

include s

/-- Every actual ambient conjugate is equal or complementary to I. The
inverse in the translate agrees with `conjugateSubrepresentation`. -/
theorem conjugate_eq_or_spans (a : F.TerminalHdot) :
    I.map (F.terminalRepresentation a⁻¹) = I ∨
    I ⊔ I.map (F.terminalRepresentation a⁻¹) = ⊤ := by
  rcases s.conjugate_disjoint a⁻¹ with he | hd
  · exact Or.inl he
  right
  obtain ⟨x,_,hop,_⟩ := s.completion.1
  have hspan : I ⊔ I.map (F.terminalRepresentation x) = ⊤ :=
    hop.symm.trans s.completion.2.1
  apply Submodule.eq_top_of_disjoint _ _ ?_ hd.symm
  have hn := Submodule.finrank_add_le_finrank_add_finrank I
    (I.map (F.terminalRepresentation x))
  rw [hspan,finrank_top,finrank_map_action] at hn
  simpa only [finrank_map_action] using hn

/-- The normal orbit has at most two actual components, and their actions
on I are quasiequivalent or dual-quasiequivalent, as G.9.3 requires. -/
theorem constituent_components :
    componentOrbit L ⊤ = L ∨ ∃ L₂ : Subgroup F.TerminalHdot,
      ∃ h₂H : L₂ ≤ componentOrbit L ⊤,
      IsComponent F.TerminalHdot L₂ ∧ componentOrbit L ⊤ = L ⊔ L₂ ∧
      (ChapterG.Section09.Quasiequivalent
        (invariantSubspace F.terminalRepresentation L I
          ((le_componentOrbit L ⊤).trans s.selected.invariant)).toRepresentation
        (invariantSubspace F.terminalRepresentation L₂ I
          (h₂H.trans s.selected.invariant)).toRepresentation ∨
       ChapterG.Section09.Quasiequivalent
        (invariantSubspace F.terminalRepresentation L I
          ((le_componentOrbit L ⊤).trans s.selected.invariant)).toRepresentation
        (invariantSubspace F.terminalRepresentation L₂ I
          (h₂H.trans s.selected.invariant)).toRepresentation.dual) := by
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  have hind := Recognition.terminal_component_normalizer_index_le_two
    s.simple F (by decide) L s.component
  rcases orbit_pair L hind with he | ⟨a,he⟩
  · exact Or.inl he
  have h₂H : L.map (MulAut.conj a).toMonoidHom ≤ componentOrbit L ⊤ := by
    rw [he]
    exact le_sup_right
  refine Or.inr ⟨_,h₂H,s.component.map_equiv (MulAut.conj a),he,?_⟩
  exact ChapterG.Section09.constituent_quasiequivalent_or_dual_conjugate
    F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
    B s.hypothesis.nondegenerate s.hypothesis.preserves s.irreducible
    s.faithful_data.2.2.1 L (le_componentOrbit L ⊤) a (s.conjugate_eq_or_spans a) _ _

/-- All G.9.3 fields on the actual action quotient, once movement by the
literal stabilizer is established. Movement by all of X does not suffice. -/
theorem componentInput_of_actor_moved
    (hm : ⁅L,actor (F := F) (g := g) (I := I)⁆ ≠ ⊥) : s.ComponentInput := by
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  let : IsElementaryAbelian 2 (actor (F := F) (g := g) (I := I)) := actor_elementary
  exact ChapterG.Section09.componentHypothesis_constituent_or_dual
    F.terminalRepresentation ⟨Recognition.terminal_sqtkCover s.simple F (by decide)⟩
    (actor (F := F) (g := g) (I := I)) L (componentOrbit L ⊤) I
    s.selected.invariant inf_le_left s.orbit_faithful s.actor_faithful s.irreducible
    (finrank (ZMod 2) I - 2) s.actor_card s.image_setup.degree_le
    s.component hm (le_componentOrbit L ⊤) s.constituent_components

end ExchangedFaithfulSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
