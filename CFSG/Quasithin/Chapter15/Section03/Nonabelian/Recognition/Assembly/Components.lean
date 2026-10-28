module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve

/-!
# Actual components for the G.9.3 application in 15.3.58

The minimal-normal reduction produces an isomorphism to a simple direct power.
Its coordinate subgroups are subnormal in the actor, so they are actual
components. Their join and their mutual isomorphism supply the component data
of the irreducible sieve, without assuming a second decomposition.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1149.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
namespace NormalReduction
variable {G : Type*} [Group G] {Z ZS : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  {C : GroupClass} {hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)}
  {K : Subgroup (ActorQuotient Z)} {v : ActorQuotient Z} {s : ℕ}

/-- The actual simple coordinate subgroups discharge the component hypotheses
of the irreducible sieve. Individual components are only subnormal in H*. -/
theorem MinimalNormalConclusion.componentData
    (h : MinimalNormalConclusion C hkernel K v s)
    (hirr : Representation.IsIrreducible ((actorRepresentation Z ZS hkernel).comp K.subtype)) :
    IrreducibleSieve.ComponentData (actorRepresentation Z ZS hkernel) K := by
  classical
  let := h.minimal.1
  refine ⟨h.minimal.1, h.nonsolvable, h.minimal.2.2, hirr, ?_⟩
  obtain ⟨S, hS, hna, _, n, hn, ⟨e⟩⟩ := h.simple_power
  let := hS
  have hZ : center S = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) inferInstance).resolve_right
      (fun ht => hna (center_eq_top_iff.mp ht))
  let : Group.IsPerfect S := ⟨
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator S) inferInstance).resolve_left
      (fun hb => hna ((commutator_eq_bot_iff S).mp hb))⟩
  let : IsQuasisimple S := ⟨
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  let L (i : Fin n) := (Components.componentEmbedding e i).range.map K.subtype
  let eL (i : Fin n) : S ≃* L i := (Components.componentEquiv e i).trans
    ((Components.componentEmbedding e i).range.equivMapOfInjective K.subtype
      Subtype.val_injective)
  have hcomp (i : Fin n) : IsComponent (ActorQuotient Z) (L i) :=
    ⟨(Components.component_normal e i).isSubnormal.trans' h.minimal.1.isSubnormal,
      IsQuasisimple.of_mulEquiv (eL i)⟩
  have hsimp (i : Fin n) : IsSimpleGroup (L i) := (eL i).symm.isSimpleGroup
  have hnonab (i : Fin n) : ¬ IsMulCommutative (L i) := by
    intro hc
    let := hc
    apply hna
    refine ⟨⟨fun a b => ?_⟩⟩
    apply (eL i).injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hgen : (⨆ i, L i) = K := by
    change (⨆ i, ((Components.componentEmbedding e i).range).map K.subtype) = K
    rw [← Subgroup.map_iSup, Components.iSup_component_eq_top,
      ← MonoidHom.range_eq_map, range_subtype]
  rcases hn with rfl | rfl
  · refine ⟨L 0, hcomp 0, hsimp 0, hnonab 0, Or.inl ?_⟩
    simpa using hgen.symm
  · refine ⟨L 0, hcomp 0, hsimp 0, hnonab 0, Or.inr
      ⟨L 1, hcomp 1, hsimp 1, hnonab 1, ?_, ⟨(eL 0).symm.trans (eL 1)⟩, ?_⟩⟩
    · intro he
      have he' : (Components.componentEmbedding e 0).range =
          (Components.componentEmbedding e 1).range :=
        Subgroup.map_injective K.subtype_injective he
      have hd := Components.component_disjoint e (show (0 : Fin 2) ≠ 1 by decide)
      rw [← he'] at hd
      have hb := disjoint_self.mp hd
      let : Nontrivial (Components.componentEmbedding e 0).range :=
        (Components.componentEquiv e 0).symm.toEquiv.nontrivial
      exact (nontrivial_iff_ne_bot _).mp inferInstance hb
    · calc
        K = ⨆ i, L i := hgen.symm
        _ = L 0 ⊔ L 1 := by
          apply le_antisymm
          · apply iSup_le
            intro i
            fin_cases i
            · exact le_sup_left
            · exact le_sup_right
          · exact sup_le (le_iSup L 0) (le_iSup L 1)

end NormalReduction
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
