module
public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension
public import Theory.SpecificGroups.PSL3Three.GraphWitnesses.EightCentralizers.GraphModel
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation

/-!
# Graph-centralizer quotients in the literal PSL₃(3) extension

Restrict the checked graph centralizer in Aut(PSL₃(3)) to the actual subgroup
of inner and graph automorphisms. Its marked C₂ × S₄ decomposition gives the
surjection to S₃ by the action on the three double transpositions. Every
conjugate has order 48, and the quotient kernel has order eight and equals
the intrinsic two-core. An intersection of order sixteen with an ambient
Sylow two-subgroup is therefore Sylow in the local subgroup.

The comparison retains the literal automorphisms and their conjugates. These
are the local-model inputs for E.1.2(E0–E1) in the PSL₃(3) case of
Aschbacher–Smith E.1.14(7), printed pp.210, 214; see also Asc82a, Lemma 4.11.
The graph-centralizer calculation is reused from `EightCentralizers.GraphModel`.
-/

public section
open Subgroup
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3Three.GraphLocalQuotients
open Matrix.PSL3Three.GraphWitnesses.EightCentralizers.GraphModel
open Theory.SpecificGroups.SymmetricSix
/-- The literal inner-and-graph subgroup, not a replacement finite carrier. -/
abbrev G := graphExtension (ZMod 3)

/-- Inverse transpose as an element of the actual extension. -/
@[expose] def graphElement : G :=
  ⟨graph (ZMod 3), Subgroup.mem_sup_right (mem_zpowers _)⟩

/-- The graph-involution centralizer inside the extension. -/
@[expose] def baseCentralizer : Subgroup G := centralizer {graphElement}

private theorem fullCentralizer_le : graphCentralizer ≤ graphExtension (ZMod 3) := by
  intro a _
  obtain ⟨x, hx | hx⟩ := automorphism_inner_or_inner_graph a
  · rw [hx]
    exact Subgroup.mem_sup_left ⟨x, rfl⟩
  · rw [hx]
    exact (graphExtension (ZMod 3)).mul_mem (Subgroup.mem_sup_left ⟨x, rfl⟩)
      (Subgroup.mem_sup_right (mem_zpowers _))

/-- Restriction preserves the full centralizer and its literal elements. -/
def baseToFull : baseCentralizer ≃* graphCentralizer where
  toFun x := ⟨x.val.val, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩
  invFun x := ⟨⟨x.val, fullCentralizer_le x.property⟩,
    mem_centralizer_singleton_iff.mpr (Subtype.ext
      (mem_centralizer_singleton_iff.mp x.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The checked centralizer decomposition restricted to the actual extension. -/
@[expose] noncomputable def baseEquiv : baseCentralizer ≃*
    zpowers (graph (ZMod 3)) × Equiv.Perm (Fin 4) :=
  baseToFull.trans graphCentralizerEquiv

/-- Conjugates of the actual graph-involution centralizer. -/
@[expose] def localSubgroup (c : G) : Subgroup G :=
  baseCentralizer.map (MulAut.conj c).toMonoidHom

/-- Marked coordinates on a conjugate local subgroup. -/
@[expose] noncomputable def localEquiv (c : G) : localSubgroup c ≃*
    zpowers (graph (ZMod 3)) × Equiv.Perm (Fin 4) :=
  (MulEquiv.subgroupMap (MulAut.conj c) baseCentralizer).symm.trans baseEquiv

/-- The action on the three double transpositions of the S₄ factor. -/
@[expose] noncomputable def localQuotient (c : G) : localSubgroup c →* Equiv.Perm (Fin 3) :=
  DuadCalculation.quotientHom.comp ((MonoidHom.snd _ _).comp (localEquiv c).toMonoidHom)

theorem localQuotient_surjective (c : G) : Function.Surjective (localQuotient c) := by
  intro y
  obtain ⟨s, hs⟩ := DuadCalculation.quotientHom_surjective y
  obtain ⟨x, hx⟩ := (localEquiv c).surjective (1, s)
  exact ⟨x, by change DuadCalculation.quotientHom ((localEquiv c x).2) = y; rw [hx]; exact hs⟩

/-- All the chosen local subgroups have order 48. -/
theorem localSubgroup_card (c : G) : Nat.card (localSubgroup c) = 48 := by
  rw [Nat.card_congr (localEquiv c).toEquiv, Nat.card_prod, graphPowers_card]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

theorem localQuotient_ker_card (c : G) : Nat.card (localQuotient c).ker = 8 := by
  have hc := (localQuotient c).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (localQuotient_surjective c),
    Subgroup.card_top, localSubgroup_card] at hc
  have hs : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [hs] at hc
  omega

theorem localQuotient_ker_isPGroup (c : G) : IsPGroup 2 (localQuotient c).ker :=
  IsPGroup.of_card (n := 3) (localQuotient_ker_card c)

/-- The epimorphism kernel is the intrinsic two-core. -/
theorem localQuotient_ker (c : G) : (localQuotient c).ker = pCore 2 (localSubgroup c) :=
  ker_eq_twoCore_of_surjective_perm_three _ (localQuotient_surjective c)
    (localQuotient_ker_isPGroup c)

theorem localSubgroup_twoCore_card (c : G) : Nat.card (pCore 2 (localSubgroup c)) = 8 := by
  rw [← localQuotient_ker, localQuotient_ker_card]

/-- The numeric intersection certificate proves the literal E0 Sylow clause. -/
theorem exists_localSylow_of_card (T : Sylow 2 G) (c : G)
    (hcard : Nat.card ((T : Subgroup G).subgroupOf (localSubgroup c)) = 16) :
    ∃ S : Sylow 2 (localSubgroup c),
      (S : Subgroup (localSubgroup c)) = (T : Subgroup G).subgroupOf (localSubgroup c) := by
  have hp : IsPGroup 2 ((T : Subgroup G).subgroupOf (localSubgroup c)) :=
    T.isPGroup'.comap_subtype
  have hc := ((T : Subgroup G).subgroupOf (localSubgroup c)).card_mul_index
  rw [hcard, localSubgroup_card] at hc
  have hi : ((T : Subgroup G).subgroupOf (localSubgroup c)).index = 3 := by omega
  exact ⟨hp.toSylow (by rw [hi]; decide), rfl⟩
/-- The chosen conjugate is the centralizer of the conjugated graph element. -/
theorem localSubgroup_eq_centralizer (c : G) :
    localSubgroup c = centralizer {(MulAut.conj c) graphElement} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg (MulAut.conj c) (mem_centralizer_singleton_iff.mp hy)
  · intro hx
    refine ⟨(MulAut.conj c).symm x, ?_, (MulAut.conj c).apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply (MulAut.conj c).injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using
      (mem_centralizer_singleton_iff.mp hx)

end Matrix.PSL3Three.GraphLocalQuotients
