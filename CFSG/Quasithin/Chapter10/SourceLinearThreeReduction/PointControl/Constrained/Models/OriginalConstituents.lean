module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalSteinberg
public import Theory.Representation.CliffordDegree

/-!
# Constituents of the original binary moved module

The binary containing-action exclusion applies to any irreducible subsection
of the original moved subgroup lying in VI. In particular the local moved
subgroup has no constituent of degree at least eight. Its nonzero constituents
therefore have degree three, by the actual SL₃(2) catalogue.

The original component normalizer acts irreducibly on the full moved subgroup.
Clifford restriction gives equal degrees for all component constituents, so
every constituent of the full original action is natural or dual-natural.
No irreducibility or full/local equality is assumed for a larger original
module. The original quotient, zero kernel and literal local containment in VI
are retained. Multiplicities and the Suzuki branch remain source obligations.

Source: Aschbacher--Smith H.6.1 and 10.2.9, printed pp.386,751--753;
Isaacs, Character Theory of Finite Groups, 6.5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

private theorem moved_normalizer_le :
    D.maximalLocal ⊓ normalizer (L : Set G) ≤
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp
    (D.maximalLocal_normalizes_fullModule hg.1),mem_normalizer_iff_map_conj_eq.mp hg.2]

private theorem normalizer_irreducible (c : Context D t v I) :
    IsIrreducible (BinaryConjugationSection.originalNormalizerAction
      (moved_normalizer_le (D := D))) := by
  let : Nontrivial (⁅D.fullModule,L⁆ : Subgroup G) :=
    (nontrivial_iff_ne_bot _).mpr (source_full_moved_ne_bot D)
  let s : BinaryConjugationSection (D.maximalLocal ⊓ normalizer (L : Set G))
      ⁅D.fullModule,L⁆ ⊥ (BinaryConjugationSection.originalNormalizerAction
        (moved_normalizer_le (D := D))) := {
    section_le := (source_full_moved_le_component D).trans
      (le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer)
    kernel_le := bot_le
    normalized := moved_normalizer_le
    coordinates := { toFun w := Multiplicative.ofAdd (Additive.ofMul w)
                     map_one' := rfl
                     map_mul' _ _ := rfl }
    onto := fun w => ⟨w.toAdd.toMul,rfl⟩
    kernel_eq := by ext w; simp
    equivariant := by
      intro g w
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (BinaryConjugationSection.originalNormalizerAction_apply_coe _ g
        (Additive.ofMul w)).symm }
  exact Selection.ModuleChoice.moved_normalizer_section_irreducible D c.minimal
    c.escaping.t_mem c.escaping.t_not_normalizes c.escaping.crossed _
    (c.moved_fixed_eq_bot.symm ▸ s)

private theorem quotient_constituent_degrees (c : Context D t v I)
    {Q : Type*} [Group Q] (e : (L ⧸ pCore 2 L) ≃* Q)
    (ρ : Representation (ZMod 2) Q (Additive (⁅D.fullModule,L⁆ : Subgroup G)))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (ρ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hs : ∀ w, (s.coordinates w).toAdd = Additive.ofMul w)
    (A B : Subrepresentation ρ)
    (hA : IsIrreducible A.toRepresentation) (hB : IsIrreducible B.toRepresentation) :
    Module.finrank (ZMod 2) A.toSubmodule = Module.finrank (ZMod 2) B.toSubmodule := by
  let N := D.maximalLocal ⊓ normalizer (L : Set G)
  let K := L.subgroupOf N
  have hLN : L ≤ N :=
    le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer
  let : K.Normal := normal_subgroupOf_of_le_normalizer inf_le_right
  let q := (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))).comp
    (subgroupOfEquivOfLe hLN).toMonoidHom
  have hq : Function.Surjective q := (e.surjective.comp (QuotientGroup.mk'_surjective _)).comp
    (subgroupOfEquivOfLe hLN).surjective
  let η := BinaryConjugationSection.originalNormalizerAction (moved_normalizer_le (D := D))
  have he : η.comp K.subtype = ρ.comp q := by
    apply MonoidHom.ext
    intro l
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    dsimp only [MonoidHom.comp_apply,η]
    rw [BinaryConjugationSection.originalNormalizerAction_apply_coe]
    have hh := s.equivariant ((subgroupOfEquivOfLe hLN) l) w.toMul
    rw [hs,hs] at hh
    exact congrArg (fun z : Additive (⁅D.fullModule,L⁆ : Subgroup G) => (z.toMul : G)) hh
  have hd : ∀ A B : Subrepresentation (ρ.comp q),
      IsIrreducible A.toRepresentation → IsIrreducible B.toRepresentation →
      Module.finrank (ZMod 2) A.toSubmodule = Module.finrank (ZMod 2) B.toSubmodule := by
    rw [←he]
    exact normal_constituent_finrank_eq η (normalizer_irreducible c) K
  exact hd (A.compActors q) (B.compActors q)
    ((irreducible_comp_surjective_iff q hq _).mpr hA)
    ((irreducible_comp_surjective_iff q hq _).mpr hB)

/-- Every constituent of the original binary moved module is natural or dual,
with coordinates through the specified original two-core quotient. -/
theorem Context.original_binary_natural_constituents (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    ∃ (ρ : Representation (ZMod 2) BinaryLinearThree.Group
        (Additive (⁅D.fullModule,L⁆ : Subgroup G)))
      (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
        (ρ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))),
      (∀ w, (s.coordinates w).toAdd = Additive.ofMul w) ∧
      IsSemisimpleModule (ZMod 2)[BinaryLinearThree.Group] ρ.asModule ∧
      ρ.invariants = ⊥ ∧
      (∀ A : Subrepresentation ρ, IsIrreducible A.toRepresentation →
        Nonempty (A.toRepresentation.Equiv BinaryLinearThree.W) ∨
          Nonempty (A.toRepresentation.Equiv BinaryLinearThree.W.dual)) ∧
      ∃ B : Subgroup G, B ≤ ⁅D.moduleSubgroup,L⁆ ∧
        (Nonempty (BinaryConjugationSection L B ⊥
          (BinaryLinearThree.W.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) ∨
         Nonempty (BinaryConjugationSection L B ⊥
          (BinaryLinearThree.W.dual.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) := by
  let W := ⁅D.fullModule,L⁆
  let W₀ := ⁅D.moduleSubgroup,L⁆
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨ρ,s,hs,hss,hfix⟩ := c.original_quotient_semisimple e
  let U : Subrepresentation ρ := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 (W₀.subgroupOf W).toAddSubgroup
    apply_mem_toSubmodule := by
      intro g w hw
      obtain ⟨l,rfl⟩ := hq g
      have hh := s.equivariant l w.toMul
      rw [hs,hs] at hh
      have hc := (mem_normalizer_iff.mp ((normalizer_commutator_ge_right D.moduleSubgroup L)
        l.property) w.toMul).mp hw
      change ((ρ (q l) w).toMul : G) ∈ W₀
      have hco : ((ρ (q l) w).toMul : G) = (l:G)*(w.toMul:G)*(l:G)⁻¹ :=
        (congrArg (fun z : Additive W => (z.toMul : G)) hh).symm
      rwa [hco] }
  have hUne : U ≠ ⊥ := by
    intro hz
    apply Selection.ModuleChoice.local_moved_ne_bot D
    apply bot_unique
    intro w hw
    have hW : w ∈ W := (commutator_mono (le_componentOrbit _ _) le_rfl) hw
    have hh : Additive.ofMul (⟨w,hW⟩ : W) ∈ U := hw
    rw [hz] at hh
    exact congrArg (fun z : Additive W => (z.toMul : G)) hh
  obtain ⟨B,hB,hBU⟩ := (eq_bot_or_exists_atom_le U).resolve_left hUne
  have hiB : IsIrreducible B.toRepresentation := (Subrepresentation.irreducible_iff_isAtom B).mpr hB
  let B' : Subrepresentation (ρ.comp q) :=
    ⟨B.toSubmodule,fun g _ hw => B.apply_mem_toSubmodule (q g) hw⟩
  let K := s.invariantPreimage B'
  have hKW : K ≤ W := s.invariantPreimage_le B'
  have hKlocal : K ≤ W₀ := by
    intro w hw
    obtain ⟨hwW,hwB⟩ := (s.mem_invariantPreimage B' w).mp hw
    rw [hs] at hwB
    exact hBU hwB
  have hdB : Module.finrank (ZMod 2) B.toSubmodule < 8 := by
    by_contra hn
    let : IsIrreducible B'.toRepresentation :=
      (irreducible_comp_surjective_iff q hq B.toRepresentation).mpr hiB
    let : Nontrivial B'.toSubmodule := Subrepresentation.irreducible_module_nontrivial B'.toRepresentation
    exact c.no_large_irreducible_moved_subsection (c.actionFacts_of_binary_three_quotient e)
      K hKW (hKlocal.trans c.local_moved_le) (s.invariantSection B') (by
        change 8 ≤ Module.finrank (ZMod 2) B.toSubmodule
        omega)
  have hnat : ∀ A : Subrepresentation ρ, IsIrreducible A.toRepresentation →
      Nonempty (A.toRepresentation.Equiv BinaryLinearThree.W) ∨
        Nonempty (A.toRepresentation.Equiv BinaryLinearThree.W.dual) := by
    intro A hA
    let := hA
    have hdA : Module.finrank (ZMod 2) A.toSubmodule < 8 := by
      rw [quotient_constituent_degrees c e ρ s hs A B hA hiB]
      exact hdB
    have hn : ∃ g w, A.toRepresentation g w ≠ w := by
      by_contra! hh
      have hb : A = ⊥ := by
        apply Subrepresentation.toSubmodule_injective
        apply bot_unique
        intro w hw
        exact hfix.le (fun g => congrArg Subtype.val (hh g ⟨w,hw⟩))
      exact ((Subrepresentation.irreducible_iff_isAtom A).mp hA).ne_bot hb
    rcases BinaryLinearThree.IrreducibleCatalogue.classify_nontrivial A.toRepresentation hn with
      h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · obtain ⟨E⟩ := h
      rw [E.toLinearEquiv.finrank_eq,BinaryLinearThree.finrank_steinberg] at hdA
      omega
  refine ⟨ρ,s,hs,hss,hfix,hnat,K,hKlocal,?_⟩
  let r : BinaryConjugationSection L K ⊥ (B.toRepresentation.comp q) :=
    s.invariantSection B'
  rcases hnat B hiB with h | h
  · obtain ⟨E⟩ := h
    exact Or.inl ⟨r.relabel q E⟩
  · obtain ⟨E⟩ := h
    exact Or.inr ⟨r.relabel q E⟩

/-- The original local moved subgroup contains an actual natural three-space,
with zero coordinate kernel and its inclusion in the literal VI proved. The
graph twist merely chooses the orientation of the original quotient marking. -/
theorem Context.local_binary_natural_subsection (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    ∃ B : Subgroup G, B ≤ ⁅D.moduleSubgroup,L⁆ ∧ B ≤ orbitModule D v I ∧
      ∃ f : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group,
        Nonempty (BinaryConjugationSection L B ⊥
          (BinaryLinearThree.W.comp (f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) := by
  obtain ⟨ρ,s,hs,hss,hfix,hnat,B,hB,hmark⟩ := c.original_binary_natural_constituents e
  refine ⟨B,hB,hB.trans c.local_moved_le,?_⟩
  rcases hmark with h | h
  · exact ⟨e,h⟩
  · obtain ⟨r⟩ := h
    exact ⟨e.trans BinaryLinearThree.AutomorphismAction.graph,
      ⟨r.relabel _ BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm⟩⟩

end CFSG.Quasithin.Chapter10.PointControl.Constrained
