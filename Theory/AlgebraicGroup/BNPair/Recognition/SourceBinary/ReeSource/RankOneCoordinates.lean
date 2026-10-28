module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PanelKernel

/-!
# Recovering a complete simple-root chart from a marked rank-one quotient

The source root injects into the faithful parabolic quotient. Under a
rank-one model marking carrying the entire Borel onto the normalizer of
its Sylow two-subgroup T, its image lies in T: a two-subgroup normalizing
a Sylow two-subgroup lies in it. The literal panel index is one plus the
source root order. If the model panel has degree 1 + |T|, finite counting
therefore makes the root injection onto T.

This constructs an actual root isomorphism and retains its representative
formula. It does not select a rank-one family or supply its model marking.
The natural rank-one catalogue is an earlier input; this is the subsequent
root-coordinate step in Fong–Seitz I (2A), pp.7–8, and II §10, p.221.
No perfectness or exclusion of the binary parameter enters this argument.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X M : Type*} [Group X] [Group M] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* M) (T : Sylow 2 M)
  (hB : (quotientBorel Q i).map μ.toMonoidHom = normalizer (T : Set M))

/-- Project the actual root to its supplied marked rank-one quotient. -/
def modelRootMap : simpleRoot Q split i →* M := μ.toMonoidHom.comp (rootProjection Q split i)

theorem modelRootMap_injective : Function.Injective (modelRootMap Q split i μ) :=
  μ.injective.comp (rootProjection_injective Q split i)

include hB in
theorem modelRootMap_range_le : (modelRootMap Q split i μ).range ≤ T := by
  have htwo : IsPGroup 2 (modelRootMap Q split i μ).range := by
    exact (split.isTwo.to_le (simpleRoot_le Q split i)).of_surjective
      (modelRootMap Q split i μ).rangeRestrict (modelRootMap Q split i μ).rangeRestrict_surjective
  have hn : (modelRootMap Q split i μ).range ≤ normalizer (T : Set M) := by
    rintro y ⟨r,rfl⟩
    rw [← hB]
    exact mem_map_of_mem μ.toMonoidHom
      (mem_map_of_mem (QuotientGroup.mk' (panelKernel Q i)) (show rootInEndpoint Q split i r ∈ endpointBorel Q i from split.U_le r.property.1))
  have he := htwo.inf_normalizer_sylow T
  rw [inf_of_le_left hn] at he
  exact le_of_inf_eq he.symm

include hB in
/-- The panel degree determines the root size under the natural rank-one marking. -/
theorem simpleRoot_card_of_panel_degree
    (hdegree : (normalizer (T : Set M)).index = 1 + Nat.card T) :
    Nat.card (simpleRoot Q split i) = Nat.card T := by
  have hindex := (quotientBorel Q i).index_map_equiv μ
  change ((quotientBorel Q i).map μ.toMonoidHom).index = (quotientBorel Q i).index at hindex
  rw [hB, quotientBorel_index Q split i, hdegree] at hindex
  omega

/-- Restrict the actual model projection to its entire Sylow root. -/
def modelRootSylowMap : simpleRoot Q split i →* T :=
  (modelRootMap Q split i μ).codRestrict T
    (fun r => modelRootMap_range_le Q split i μ T hB ⟨r,rfl⟩)

variable [Finite M]

theorem modelRootSylowMap_bijective
    (hdegree : (normalizer (T : Set M)).index = 1 + Nat.card T) :
    Function.Bijective (modelRootSylowMap Q split i μ T hB) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, simpleRoot_card_of_panel_degree Q split i μ T hB hdegree⟩
  intro r t he
  exact modelRootMap_injective Q split i μ (congrArg Subtype.val he)

/-- Actual source-to-model root coordinates, with no perfectness restriction. -/
def modelRootEquiv
    (hdegree : (normalizer (T : Set M)).index = 1 + Nat.card T) :
    simpleRoot Q split i ≃* T :=
  MulEquiv.ofBijective (modelRootSylowMap Q split i μ T hB)
    (modelRootSylowMap_bijective Q split i μ T hB hdegree)

@[simp] theorem modelRootEquiv_apply
    (hdegree : (normalizer (T : Set M)).index = 1 + Nat.card T)
    (r : simpleRoot Q split i) :
    (modelRootEquiv Q split i μ T hB hdegree r : M) = μ (rootProjection Q split i r) := rfl

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
