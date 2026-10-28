module
public import Stellmacher.LaterDefs
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.Algebra.GroupWithZero.Action.End

/-!
# Quotient-module commutators and ambient lifts

For a quotient-module witness and an ambient actor Y contained in its acting
group A, the action commutator of the image of Y maps to [V,Y]. The witness's
conjugation equation proves that Y normalizes V. Lifting image elements
identifies the action-commutator generators, and the subgroup-conjugation
identity gives the ambient result.

The original full-preimage transport is retained as a short wrapper:
surjectivity makes the image of the full preimage exactly the given quotient
subgroup. Thus both arbitrary actors and factor preimages use one proof.

This is the transport for the factors [Z_a,E_i] in Stellmacher (8.1),
journal p.37 of `refs/latex/stellmacher-n-group.tex`. The exact witness
action is retained; no extra finiteness or faithfulness assumption is needed.
-/

namespace Stellmacher.Later
universe u

/-- Transport the commutator of an image actor to its actual ambient actor. -/
public theorem QuotientModuleWitness.commutatorAction_image_map_subtype
    {G : Type u} [Group G] {A B V : Subgroup G}
    (w : QuotientModuleWitness A B V) (Y : Subgroup G) (hYA : Y ≤ A) :
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom V w.action
    (commutatorAction ((Y.subgroupOf A).map w.projection) V).map V.subtype =
      ⁅V, Y⁆ := by
  let := w.groupX
  let := MulDistribMulAction.compHom V w.action
  change (commutatorAction ((Y.subgroupOf A).map w.projection) V).map V.subtype = ⁅V, Y⁆
  have hstable (a : A) (v : V) : (a : G) * (v : G) * (a : G)⁻¹ ∈ V := by
    rw [← w.action_compatible]
    exact ((w.action (w.projection a)) v).property
  have hnorm : Y ≤ Subgroup.normalizer (V : Set G) := by
    intro y hy
    let a : A := ⟨y, hYA hy⟩
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      exact hstable a ⟨v, hv⟩
    · intro hv
      have hh := hstable a⁻¹ ⟨y * v * y⁻¹, hv⟩
      simpa [a, mul_assoc] using hh
  let : Subgroup.Normalizes Y V := ⟨hnorm⟩
  have hcomm : commutatorAction ((Y.subgroupOf A).map w.projection) V =
      commutatorAction Y V := by
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨e, x, rfl⟩
      obtain ⟨a, ha, heq⟩ := e.property
      refine ⟨⟨a, ha⟩, x, ?_⟩
      congr 1
      apply Subtype.ext
      change ((w.action e.val) x : G) = (a : G) * (x : G) * (a : G)⁻¹
      rw [← heq, w.action_compatible]
    · rintro ⟨y, x, rfl⟩
      let a : A := ⟨y, hYA y.property⟩
      refine ⟨⟨w.projection a, Subgroup.mem_map_of_mem w.projection y.property⟩, x, ?_⟩
      congr 1
      apply Subtype.ext
      change (y : G) * (x : G) * (y : G)⁻¹ = ((w.action (w.projection a)) x : G)
      rw [w.action_compatible]
  rw [hcomm, commutatorAction_subgroup_conj_map_eq_commutator V Y hnorm]

/-- Full-preimage compatibility form of the image-actor transport. -/
public theorem QuotientModuleWitness.commutatorAction_map_subtype
    {G : Type u} [Group G] {A B V : Subgroup G}
    (w : QuotientModuleWitness A B V)
    (E : @Subgroup w.X w.groupX) :
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom V w.action
    (commutatorAction E V).map V.subtype =
      ⁅V, (E.comap w.projection).map A.subtype⁆ := by
  let := w.groupX
  let := MulDistribMulAction.compHom V w.action
  have hh := w.commutatorAction_image_map_subtype
    ((E.comap w.projection).map A.subtype) (Subgroup.map_subtype_le _)
  dsimp only at hh
  have hE : (((E.comap w.projection).map A.subtype).subgroupOf A).map w.projection = E := by
    rw [← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective A.subtype_injective,
      Subgroup.map_comap_eq_self_of_surjective w.surjective]
  rw [hE] at hh
  exact hh

end Stellmacher.Later
