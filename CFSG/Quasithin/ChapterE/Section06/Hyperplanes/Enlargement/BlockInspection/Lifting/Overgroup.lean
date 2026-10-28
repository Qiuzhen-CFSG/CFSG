module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Five
public import Theory.GroupTheory.CComponent.PrimeGroupOvergroup

/-!
# The generated overgroup for the E.6.7 application

Write H₀ = C_G(A), Q = C_T(V), and K = ⟨X,Q⟩ for the C-component X
constructed by 1.2.4. The actual common Sylow gives Q ≤ H₀ and makes Q
Sylow in K. Trivial odd core of H₀ and the general C-component argument
give either an ordinary component X or F*(K) = O₂(K).

The latter equality concerns K, not just X. No classification of X as
a block is assumed or asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254; E.6.5 and E.6.7, pp.245–246.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
open ComponentBalance

variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- The genuine generated overgroup is characteristic two unless the
containing C-component is already an ordinary component of C_G(A). -/
theorem centralizer_cComponent_overgroup_dichotomy
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h21 : OddCoreFree V) {A X : Subgroup G} (hA : A ∈ obstructionFamily M V)
    (hX : X ∈ Chapter1.cComponentsIn (centralizer (A : Set G))) :
    CentralizerComponent A X ∨
      generalizedFitting ↥(X ⊔ sylowCentralizer (T : Subgroup G) V) =
        pCore 2 ↥(X ⊔ sylowCentralizer (T : Subgroup G) V) := by
  let H := centralizer (A : Set G)
  let Q := sylowCentralizer (T : Subgroup G) V
  have hQ := Chapter1.isSylowIn_iff.mp (h.sylow_obstruction hA)
  rcases hX.2.component_or_generalizedFitting_sup_eq_pCore hQ.1.comap_subtype
      (h21 A hA.1 hA.2.1) with hc | hf
  · exact Or.inl ⟨hX.1, hc⟩
  · right
    have he : (X.subgroupOf H ⊔ Q.subgroupOf H).map H.subtype = X ⊔ Q := by
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hX.1, map_subgroupOf_eq_of_le hQ.2.1]
    let e := ((X.subgroupOf H ⊔ Q.subgroupOf H).equivMapOfInjective
      H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr he)
    exact (map_generalizedFitting_equiv e).symm.trans
      ((congrArg (Subgroup.map e.toMonoidHom) hf).trans (pCore_map_iso 2 e))

/-- The actual Q is Sylow in ⟨X,Q⟩, and that group is contained in
C_G(A), exactly as required by E.6.7. -/
theorem cComponent_overgroup_sylow
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    {A X : Subgroup G} (hA : A ∈ obstructionFamily M V)
    (hX : X ∈ Chapter1.cComponentsIn (centralizer (A : Set G))) :
    Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V)
      (X ⊔ sylowCentralizer (T : Subgroup G) V) ∧
      X ⊔ sylowCentralizer (T : Subgroup G) V ≤ centralizer (A : Set G) := by
  have hS : Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V)
      (centralizer (A : Set G)) := h.sylow_obstruction hA
  have hle := sup_le hX.1 (Chapter1.isSylowIn_iff.mp hS).2.1
  exact ⟨hS.restrict le_sup_right hle, hle⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
