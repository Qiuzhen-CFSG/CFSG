module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Actions
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.Elementary
public import Theory.GroupTheory.CComponent.Structure
public import Theory.GroupTheory.PCoreRestriction

/-!
# Local algebra for the component replacement

The replacement in 15.3.49 is `K = ⟨L^T⟩ Y₀ T`. A Sylow subgroup carries
`O₂(H)` into `K`, keeping its two-core nontrivial, and the identity
`θ(M ∩ H) = Y₀` descends by monotonicity and idempotence. Components of
`J_H = ⟨V_α^H⟩` are subnormal relative to `H`, since that span is normal.
The last lemmas justify the product and normality assertions for `⟨L^T⟩`.

The component-generation assertion (i) is still a separate obligation. Its
consequence (j) is proved conditionally here. Neither the local action on the
smaller conjugate span nor the classification conclusions (k)–(l) are assumed
to transfer automatically to `K`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(i)–(k), printed pp.1143–1144.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- The proposed replacement, keeping the component closure separate from its supplement. -/
def reducedOvergroup (L Y0 T : Subgroup G) : Subgroup G :=
  localSpan L T ⊔ (Y0 ⊔ T)

/-- The order-three generator identity descends to every intermediate group containing `Y₀`. -/
theorem theta_intermediate (M H K Y0 : Subgroup G)
    (hKH : K ≤ H) (hYK : Y0 ≤ K) (hθ : theta (M ⊓ H) = Y0) :
    theta (M ⊓ K) = Y0 := by
  have hYM : Y0 ≤ M := (hθ ▸ theta_le _).trans inf_le_left
  have hYY : theta Y0 = Y0 := by rw [← hθ, theta_idempotent]
  apply le_antisymm
  · exact (theta_mono (inf_le_inf_left M hKH)).trans_eq hθ
  · rw [← hYY]
    exact theta_mono (le_inf hYM hYK)

/-- The replacement lies in the original local overgroup. -/
theorem reducedOvergroup_le {L Y0 T H : Subgroup G}
    (hL : L ≤ H) (hY : Y0 ≤ H) (hT : T ≤ H) : reducedOvergroup L Y0 T ≤ H :=
  sup_le (conjugateSpanBy_le hL (hT.trans H.le_normalizer)) (sup_le hY hT)

/-- A component outside `M` keeps the replacement outside `M`. -/
theorem reducedOvergroup_outside {L Y0 T M : Subgroup G} (hL : ¬ L ≤ M) :
    ¬ reducedOvergroup L Y0 T ≤ M :=
  fun h => hL ((le_conjugateSpanBy L T).trans (le_sup_left.trans h))

/-- A Sylow subgroup carries the original nontrivial two-core into the replacement. Hence the replacement still belongs to the actual local family. -/
theorem reducedOvergroup_mem_outsideFamily [Finite G]
    (L Y0 H M : Subgroup G) (T : Sylow 2 H)
    (hH : localTwoCore H ≠ ⊥) (hL : L ≤ H) (hLM : ¬ L ≤ M) (hY : Y0 ≤ H) :
    reducedOvergroup L Y0 ((T : Subgroup H).map H.subtype) ∈
      outsideFamily Y0 ((T : Subgroup H).map H.subtype) M := by
  let K := reducedOvergroup L Y0 ((T : Subgroup H).map H.subtype)
  have hKH : K ≤ H := reducedOvergroup_le hL hY (map_subtype_le _)
  have hQK : H.pCoreIn 2 ≤ K := (pCoreIn_le_sylow H T).trans
    (le_sup_right.trans le_sup_right)
  have hQ : H.pCoreIn 2 ≤ K.pCoreIn 2 := by
    simpa only [inf_eq_right.mpr hQK] using inf_pCoreIn_le_of_le 2 hKH
  refine ⟨⟨?_, (show Y0 ⊔ ((T : Subgroup H).map H.subtype) ≤ K from le_sup_right)⟩, reducedOvergroup_outside hLM⟩
  intro hb
  exact hH (le_bot_iff.mp (hQ.trans_eq hb))

/-- The conjugate span is normal relative to its generating overgroup. -/
theorem localSpan_normal (A H : Subgroup G) (hA : A ≤ H) :
    ((localSpan A H).subgroupOf H).Normal :=
  (normal_subgroupOf_iff_le_normalizer (conjugateSpanBy_le_self hA)).mpr
    (le_normalizer_conjugateSpanBy A H)

/-- Components of the conjugate span are C-components of the local overgroup. -/
theorem localSpan_component_isCComponent (A H L : Subgroup G)
    (hA : A ≤ H) (hL : L ≤ localSpan A H)
    (hc : (L.subgroupOf (localSpan A H)).IsCComponent) :
    (L.subgroupOf H).IsCComponent := by
  let J := localSpan A H
  have hJ : J ≤ H := conjugateSpanBy_le_self hA
  -- Map the component internal to J through its identification with J in H.
  have hcomp : ((L.subgroupOf H).subgroupOf (J.subgroupOf H)).IsCComponent := by
    have hh := hc.map_equiv (subgroupOfEquivOfLe hJ).symm
    have he : (L.subgroupOf J).map (subgroupOfEquivOfLe hJ).symm.toMonoidHom =
        (L.subgroupOf H).subgroupOf (J.subgroupOf H) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, x.property⟩, hx, rfl⟩
    rwa [he] at hh
  have hh := hcomp.map_subtype ((localSpan_normal A H hA).isSubnormal)
  rw [map_subgroupOf_eq_of_le (show L.subgroupOf H ≤ J.subgroupOf H from
    comap_mono hL)] at hh
  exact hh

/-- Subnormality here is relative to `H`, not ambient subnormality in `G`. -/
theorem localSpan_component_isSubnormal (A H L : Subgroup G)
    (hA : A ≤ H) (hL : L ≤ localSpan A H)
    (hc : (L.subgroupOf (localSpan A H)).IsCComponent) :
    (L.subgroupOf H).IsSubnormal :=
  (localSpan_component_isCComponent A H L hA hL hc).subnormal

/-- A component of `H` cannot lie in the solvable intersection `M ∩ H`. -/
theorem component_not_le_solvable_intersection (H M L : Subgroup G)
    [Group.IsSolvable ↥(M ⊓ H)] (hLH : L ≤ H)
    (hL : (L.subgroupOf H).IsCComponent) : ¬ L ≤ M := by
  intro hLM
  let f : L.subgroupOf H →* ↥(M ⊓ H) :=
    (inclusion (le_inf hLM hLH)).comp (subgroupOfEquivOfLe hLH).toMonoidHom
  exact hL.not_isSolvable (Group.isSolvable_of_isSolvable_injective
    (f := f) ((inclusion_injective (le_inf hLM hLH)).comp
      (subgroupOfEquivOfLe hLH).injective))

/-- Select a component and obtain a legitimate replacement in the local family.
The noncontainment in `M` follows from solvability, rather than being assumed. -/
theorem reducedOvergroup_mem_of_component [Finite G]
    (L Y0 H M : Subgroup G) (T : Sylow 2 H)
    [Group.IsSolvable ↥(M ⊓ H)] (hH : localTwoCore H ≠ ⊥)
    (hLH : L ≤ H) (hL : (L.subgroupOf H).IsCComponent) (hY : Y0 ≤ H) :
    reducedOvergroup L Y0 ((T : Subgroup H).map H.subtype) ∈
      outsideFamily Y0 ((T : Subgroup H).map H.subtype) M :=
  reducedOvergroup_mem_outsideFamily L Y0 H M T hH hLH
    (component_not_le_solvable_intersection H M L hLH hL) hY

/-- A genuine best offender has nontrivial conjugate span. -/
theorem localSpan_ne_bot_of_bestOffender
    (H U Z A : Subgroup G) [IsElementaryAbelian 2 U]
    (action : SectionAction H U Z)
    (hA : IsBestOffender action.representation (starImage H A)) :
    localSpan A H ≠ ⊥ := by
  intro hb
  have ha : A = ⊥ := le_bot_iff.mp ((le_conjugateSpanBy A H).trans_eq hb)
  exact hA.1.1 (by simp [starImage, ha])

/-- A nontrivial group generated by its C-components cannot be solvable. -/
theorem localSpan_not_solvable_of_components
    (A H : Subgroup G) (hA : localSpan A H ≠ ⊥)
    (hc : (cComponentLayer (localSpan A H)).map (localSpan A H).subtype = localSpan A H) :
    ¬ Group.IsSolvable (localSpan A H) := by
  intro hs
  let := hs
  have hbot : cComponentLayer (localSpan A H) = ⊥ := by
    apply le_bot_iff.mp
    apply sSup_le
    intro L hL
    exact (hL.not_isSolvable inferInstance).elim
  apply hA
  rw [← hc, hbot, Subgroup.map_bot]

/-- The deduction (i) implies (j), applied to every eligible intermediate group.
The component-generation premise must be proved by the (i) argument. -/
theorem solvable_overgroup_le_of_components
    (Y0 T M H : Subgroup G)
    (hcomponents : ∀ K : Subgroup G, Y0 ⊔ T ≤ K → K ≤ H → ¬ K ≤ M →
      ∃ A : Subgroup G, A ≤ K ∧ localSpan A K ≠ ⊥ ∧
        (cComponentLayer (localSpan A K)).map (localSpan A K).subtype = localSpan A K)
    (K : Subgroup G) [Group.IsSolvable K]
    (hYK : Y0 ⊔ T ≤ K) (hKH : K ≤ H) : K ≤ M ⊓ H := by
  apply le_inf _ hKH
  by_contra hKM
  obtain ⟨A, hAK, hA, hc⟩ := hcomponents K hYK hKH hKM
  have hspan : localSpan A K ≤ K := conjugateSpanBy_le_self hAK
  let : Group.IsSolvable (localSpan A K) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hspan)
  exact localSpan_not_solvable_of_components A K hA hc inferInstance

/-- A `T`-invariant subgroup normalizing `L` also normalizes `⟨L^T⟩`. -/
theorem normalizes_localSpan_of_normalizes
    (L Y0 T : Subgroup G) (hYL : Y0 ≤ normalizer (L : Set G))
    (hTY : T ≤ normalizer (Y0 : Set G)) :
    Y0 ≤ normalizer (localSpan L T : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro y hy x ⟨t, ht, l, hl, rfl⟩
  have htY : t⁻¹ * y * t ∈ Y0 := by
    simpa only [inv_inv] using
      le_normalizer_iff.mp hTY t⁻¹ (T.inv_mem ht) y hy
  have hl' : (t⁻¹ * y * t) * l * (t⁻¹ * y * t)⁻¹ ∈ L :=
    le_normalizer_iff.mp hYL _ htY l hl
  apply Subgroup.subset_closure
  refine ⟨t, ht, _, hl', ?_⟩
  group

/-- The equality `L = [L,Y₀]` extends to its `T`-conjugate span.
This is the commutator assertion used before the Borel argument in (k). -/
theorem componentClosure_commutator
    (L Y0 T : Subgroup G) (hL : L = ⁅L, Y0⁆)
    (hTY : T ≤ normalizer (Y0 : Set G)) :
    localSpan L T = ⁅localSpan L T, Y0⁆ := by
  have hYL : Y0 ≤ normalizer (L : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hL.ge
  apply le_antisymm _ (le_normalizer_iff_commutator_le_left.mp
    (normalizes_localSpan_of_normalizes L Y0 T hYL hTY))
  apply (closure_le _).mpr
  rintro x ⟨t, ht, l, hl, rfl⟩
  have hconj : L.map (MulAut.conj t).toMonoidHom ≤ localSpan L T := by
    rintro x ⟨a, ha, rfl⟩
    exact subset_closure ⟨t, ht, a, ha, rfl⟩
  have hcomm : L.map (MulAut.conj t).toMonoidHom ≤ ⁅localSpan L T, Y0⁆ := by
    have hYmap : Y0.map (MulAut.conj t).toMonoidHom = Y0 :=
      mem_normalizer_iff_map_conj_eq.mp (hTY ht)
    conv_lhs => rw [hL]
    rw [map_commutator, hYmap]
    exact commutator_mono hconj le_rfl
  exact hcomm (mem_map_of_mem _ hl)

/-- The component closure is normal in the replacement. -/
theorem componentClosure_normal_in_replacement
    (L Y0 T : Subgroup G) (hYL : Y0 ≤ normalizer (L : Set G))
    (hTY : T ≤ normalizer (Y0 : Set G)) :
    ((localSpan L T).subgroupOf (reducedOvergroup L Y0 T)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
  exact sup_le (localSpan L T).le_normalizer
    (sup_le (normalizes_localSpan_of_normalizes L Y0 T hYL hTY)
      (le_normalizer_conjugateSpanBy L T))

open scoped Pointwise in
/-- The replacement join is the literal setwise product used in the source. -/
theorem reducedOvergroup_product
    (L Y0 T : Subgroup G) (hYL : Y0 ≤ normalizer (L : Set G))
    (hTY : T ≤ normalizer (Y0 : Set G)) :
    (reducedOvergroup L Y0 T : Set G) = (localSpan L T : Set G) *
      (Y0 : Set G) * (T : Set G) := by
  rw [reducedOvergroup, coe_mul_of_right_le_normalizer_left _ _
    (sup_le (normalizes_localSpan_of_normalizes L Y0 T hYL hTY)
      (le_normalizer_conjugateSpanBy L T)),
    coe_mul_of_right_le_normalizer_left Y0 T hTY, mul_assoc]


end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
