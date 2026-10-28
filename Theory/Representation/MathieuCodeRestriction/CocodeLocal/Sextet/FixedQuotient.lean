module

public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Fixed vectors in a quotient with an irreducible top section

For a normal acting subgroup, the inverse image of fixed vectors in an invariant
quotient is invariant. If a middle term is centralized modulo the bottom term
and the top section is irreducible, that inverse image is either the middle term
or the entire module. An element whose fixed codimension exceeds the dimension
of the bottom term excludes the latter possibility.

This is the linear argument used in Aschbacher–Smith H.15.3(4), printed p.400.
Its local action and irreducibility hypotheses must be established separately.
Normality is inside the acting group, not inside a larger ambient group.
-/

@[expose] public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The inverse image of the fixed space in an invariant quotient is invariant
when the acting subgroup is normal in the ambient acting group. -/
noncomputable def quotientFixedPreimage (U : Subrepresentation ρ)
    (N : Subgroup G) [N.Normal] : Subrepresentation ρ where
  toSubmodule := (fixedSpace U.quotientRepresentation N).comap U.toSubmodule.mkQ
  apply_mem_toSubmodule g v hv :=
    (fixedSpace_stable_of_normal U.quotientRepresentation N
      (Subgroup.mem_top g) (U.toSubmodule.mkQ v)).mpr hv

lemma mem_quotientFixedPreimage (U : Subrepresentation ρ) (N : Subgroup G) [N.Normal]
    (v : V) : v ∈ quotientFixedPreimage ρ U N ↔
      ∀ n ∈ N, ρ n v - v ∈ U := by
  constructor
  · intro h n hn
    exact (Submodule.Quotient.eq U.toSubmodule).mp (h ⟨n,hn⟩)
  · intro h n
    exact (Submodule.Quotient.eq U.toSubmodule).mpr (h n.val n.property)

/-- A nontrivial action modulo the bottom term rules out extra fixed vectors
above an irreducible top section. -/
theorem fixedSpace_quotient_eq_image_of_irreducible
    (U W : Subrepresentation ρ) (hUW : U ≤ W) (N : Subgroup G) [N.Normal]
    [IsIrreducible W.quotientRepresentation]
    (hcomm : ∀ n ∈ N, ∀ w ∈ W, ρ n w - w ∈ U)
    (hmove : ∃ n ∈ N, ∃ v, ρ n v - v ∉ U) :
    fixedSpace U.quotientRepresentation N = W.toSubmodule.map U.toSubmodule.mkQ := by
  let D := quotientFixedPreimage ρ U N
  have hWD : W ≤ D := by
    intro w hw
    exact (mem_quotientFixedPreimage ρ U N w).mpr (fun n hn => hcomm n hn w hw)
  have hDW : D ≤ W := by
    rcases Subrepresentation.le_or_sup_eq_top_of_irreducible_quotient W D with h | h
    · exact h
    · have ht : D.toSubmodule = ⊤ := by simpa only [sup_eq_right.mpr (show W.toSubmodule ≤ D.toSubmodule from hWD)] using h
      obtain ⟨n, hn, v, hv⟩ := hmove
      have hm : v ∈ D := by change v ∈ D.toSubmodule; rw [ht]; trivial
      exact (hv ((mem_quotientFixedPreimage ρ U N v).mp hm n hn)).elim
  apply Submodule.comap_injective_of_surjective U.toSubmodule.mkQ_surjective
  rw [Submodule.comap_map_mkQ, sup_eq_right.mpr (show U.toSubmodule ≤ W.toSubmodule from hUW)]
  exact le_antisymm hDW hWD

/-- A cyclic fixed codimension larger than a subspace forces a nontrivial
induced action modulo that subspace. -/
theorem exists_displacement_not_mem_of_finrank_lt [FiniteDimensional (ZMod 2) V]
    (U : Submodule (ZMod 2) V) (a : G)
    (h : Module.finrank (ZMod 2) U < fixedCodim ρ (Subgroup.zpowers a)) :
    ∃ v, ρ a v - v ∉ U := by
  by_contra hn
  push Not at hn
  have hle : LinearMap.range (ρ a - LinearMap.id) ≤ U := by
    rintro _ ⟨v,rfl⟩
    exact hn v
  have hr := Submodule.finrank_mono hle
  rw [← fixedCodim_zpowers_eq_displacement_rank] at hr
  omega

/-- A single element's displacement supplies the nontriviality input to the
irreducible-top-section fixed-quotient argument. -/
theorem fixedSpace_quotient_eq_image_of_fixedCodim [FiniteDimensional (ZMod 2) V]
    (U W : Subrepresentation ρ) (hUW : U ≤ W) (N : Subgroup G) [N.Normal]
    [IsIrreducible W.quotientRepresentation]
    (hcomm : ∀ n ∈ N, ∀ w ∈ W, ρ n w - w ∈ U)
    (a : G) (ha : a ∈ N)
    (hcodim : Module.finrank (ZMod 2) U.toSubmodule <
      fixedCodim ρ (Subgroup.zpowers a)) :
    fixedSpace U.quotientRepresentation N = W.toSubmodule.map U.toSubmodule.mkQ := by
  obtain ⟨v,hv⟩ := exists_displacement_not_mem_of_finrank_lt ρ U.toSubmodule a hcodim
  exact fixedSpace_quotient_eq_image_of_irreducible ρ U W hUW N hcomm ⟨a,ha,v,hv⟩

end Representation.BinaryOffender
