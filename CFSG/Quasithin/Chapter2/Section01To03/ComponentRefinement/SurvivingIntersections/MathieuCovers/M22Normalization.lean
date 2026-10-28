module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.Displacement
public import Theory.SpecificGroups.AlternatingSix.CommutingLocalRank

/-!
# Ambient normalization and displacement in the remaining M₂₂ cases

Both nontrivial covers contain the actual A₆ complement constructed in
their recognized hexad preimage. Quasithinness forbids two commuting A₆
subgroups, since E₉ × A₄ supplies a two-local subgroup of three-rank three.
Thus this component has no commuting conjugate; component calculus inside
the original H proves H normalizes L. This discharges the extra hypothesis
in the Γ₀ kernel-displacement calculation.

In particular a nontrivial covering kernel forces an element of N_T(S)
that moves it. This is a necessary configuration, not its exclusion. The
argument does not claim the component Sylow is characteristic in S.
Source: Aschbacher–Smith 2.3.7–9, printed pp.523–526, using the actual
I.2.2(6) hexad complements, printed p.412.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Sporadic.Mathieu Theory.GroupTheory
open ChapterI.Section02.ExceptionalCovers
variable {G : Type*} [Group G]
variable {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- In each nontrivial surviving cover the native hexad supplies an actual
A₆ subgroup of the original L, not a quotient or a group-family tag. -/
theorem LocalSetup.mathieuTwentyTwo_contains_a6
    (h : LocalSetup H L M S z) (e : (L ⧸ pCore 2 L) ≃* M22)
    (hk : pCore 2 L ≠ ⊥) :
    ∃ A : Subgroup L, Nonempty (A ≃* alternatingGroup (Fin 6)) := by
  rcases h.mathieuTwentyTwo_nontrivial_hexad_models e hk with ⟨_, hb⟩ | ⟨_, hq⟩
  · obtain ⟨d⟩ := hb m22Hexad123 m22Hexad123_mem
    exact ⟨d.complement, ⟨d.ambientComplementEquiv.symm⟩⟩
  · obtain ⟨d⟩ := hq m22Hexad123 m22Hexad123_mem
    exact ⟨d.complement, ⟨d.complementEquiv.symm⟩⟩

variable [Finite G]

/-- The actual nontrivial cover has no commuting ambient conjugate in a
quasithin group. This uses the constructed complement, including in order four. -/
theorem LocalSetup.mathieuTwentyTwo_no_commuting_conjugate
    (h : LocalSetup H L M S z) (hG : IsQuasithin G)
    (e : (L ⧸ pCore 2 L) ≃* M22) (hk : pCore 2 L ≠ ⊥) (g : G) :
    ¬ L ≤ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G) := by
  let := h.finite
  obtain ⟨A, ⟨eA⟩⟩ := h.mathieuTwentyTwo_contains_a6 e hk
  let B := A.map L.subtype
  let eB : B ≃* alternatingGroup (Fin 6) :=
    (A.equivMapOfInjective L.subtype L.subtype_injective).symm.trans eA
  intro hc
  apply alternatingGroup.not_commuting_a6_of_quasithin hG B
    (B.map (MulAut.conj g).toMonoidHom) eB
    (((MulAut.conj g).subgroupMap B).symm.trans eB)
  exact (map_subtype_le A).trans
    (hc.trans (Subgroup.centralizer_le (map_mono (map_subtype_le A))))

/-- Component subnormality upgrades to H-normalization here, because a
distinct component conjugate would commute with the first actual A₆ copy. -/
theorem LocalSetup.mathieuTwentyTwo_normalized
    (h : LocalSetup H L M S z) (hG : IsQuasithin G)
    (e : (L ⧸ pCore 2 L) ≃* M22) (hk : pCore 2 L ≠ ⊥) :
    H ≤ normalizer (L : Set G) := by
  let := h.finite
  have hn : (L.subgroupOf H).Normal := by
    apply normal_iff_map_conj_eq.mpr
    intro g
    by_contra hne
    have hc := h.component.commutator_eq_bot_of_ne
      (h.component.map_conj g) (Ne.symm hne)
    have he := congrArg (Subgroup.map H.subtype) hc
    rw [map_commutator, Subgroup.map_bot, map_subgroupOf_eq_of_le h.component_le, map_map] at he
    have hconj :
        H.subtype.comp (MulAut.conj g).toMonoidHom =
          (MulAut.conj (g : G)).toMonoidHom.comp H.subtype := rfl
    rw [hconj, ← map_map, map_subgroupOf_eq_of_le h.component_le] at he
    exact h.mathieuTwentyTwo_no_commuting_conjugate hG e hk g
      (commutator_eq_bot_iff_le_centralizer.mp he)
  exact (normal_subgroupOf_iff_le_normalizer h.component_le).mp hn

variable {C : GroupClass}

/-- The original source hypotheses force an actual kernel-moving element
of N_T(S). H-normalization is now proved, not retained as an extra premise. -/
theorem MathieuSourceSetup.mathieuTwentyTwo_kernel_displacement
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (source115 : Structural115Input G) (sourceC : LocalC129Input C G)
    (e : (L ⧸ pCore 2 L) ≃* M22) (hk : pCore 2 L ≠ ⊥) :
    ∃ g ∈ (c.T : Subgroup G),
      g ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      g ∉ normalizer (twoCore L : Set G) := by
  have h := c.localSetup hG source115 sourceC
  exact c.twoCore_displacement (h.mathieuTwentyTwo_normalized hG.quasithin e hk) hk

end CFSG.Quasithin.Chapter2.ComponentRefinement
end
