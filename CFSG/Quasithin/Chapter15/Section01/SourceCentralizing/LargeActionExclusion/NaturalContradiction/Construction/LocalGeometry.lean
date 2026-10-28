module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.Flag
public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators.FirstPlane
public import Theory.GroupTheory.PCoreImageRestriction
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# Placement and movement of the first natural parabolic

All subgroups here are the preimages in the already chosen natural flag.
Residuals and two-cores transport through its literal action. The first
parabolic fixes the moving plane setwise, and its two-core is precisely
the pointwise centralizer of that plane in S. The cubic element in its
residual moves the whole plane.

The original hypothesis that J(T) centralizes V puts J(T) in this core.
Thompson heredity then makes P₀ normalize J(T), and the proved source
normalizer control places P₀ inside M. This establishes the first-node
placement and movement in 15.1.29 without any orbit or rank-two premise.
The further equality with C_T(V), end-node orbit, and rank-two input remain
separate obligations on the same flag.

Source: Aschbacher--Smith, 15.1.9(1), B.2.3(3), and 15.1.29,
printed pp.1103--1104 of `refs/quasithin.pdf` for the latter argument.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open BinaryLinear.OrderedResidualConjugators
open CFSG.Quasithin.ChapterD.UniqueFactor
open CFSG.Quasithin.Chapter15.Section03
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {t : G}

/-- Images of the embedded residuals under the literal natural action. -/
theorem node_residual_image (a : NaturalFlag d t) (i : Fin a.m) :
    (((pResidual 2 (a.node i)).map (a.node i).subtype).subgroupOf
      (d.L ⊔ d.S)).map a.action = nodeResidual a.basis i := by
  have he : ((pResidual 2 (a.node i)).map (a.node i).subtype).subgroupOf (d.L ⊔ d.S) =
      (pResidual 2 ((a.node i).subgroupOf (d.L ⊔ d.S))).map
        ((a.node i).subgroupOf (d.L ⊔ d.S)).subtype := by
    apply map_injective (d.L ⊔ d.S).subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans (a.node_le i)),
      map_embedded_pResidual, map_subgroupOf_eq_of_le (a.node_le i)]
  rw [he, map_embedded_pResidual, a.node_image]
  rfl

/-- The coordinates preserve subgroup containment. -/
theorem spaceOf_mono (a : NaturalFlag d t) {A B : Subgroup G} (hAB : A ≤ B) :
    a.spaceOf A ≤ a.spaceOf B := by
  let := a.elementary
  intro v hv
  obtain ⟨v,rfl⟩ := a.coordinates.surjective v
  exact (a.mem_spaceOf_coordinates B v).mpr (hAB ((a.mem_spaceOf_coordinates A v).mp hv))

/-- Containment is also reflected for subgroups of the natural module. -/
theorem spaceOf_le_iff (a : NaturalFlag d t) {A B : Subgroup G} (hA : A ≤ d.UL t) :
    a.spaceOf A ≤ a.spaceOf B ↔ A ≤ B := by
  let := a.elementary
  refine ⟨?_, a.spaceOf_mono⟩
  intro hh g hg
  let v : Additive (d.UL t) := Additive.ofMul ⟨g,hA hg⟩
  exact (a.mem_spaceOf_coordinates B v).mp
    (hh ((a.mem_spaceOf_coordinates A v).mpr hg))

/-- A linear displacement is the coordinate image of the actual group commutator. -/
theorem action_sub_mem_spaceOf_commutator (a : NaturalFlag d t)
    (A Y : Subgroup G) (g : (d.L ⊔ d.S : Subgroup G)) (hg : g.val ∈ Y)
    (v : Additive (d.UL t)) (hv : v.toMul.val ∈ A) :
    letI := a.elementary
    a.action g (a.coordinates v) - a.coordinates v ∈ a.spaceOf ⁅A,Y⁆ := by
  let := a.elementary
  change naturalAction _ _ _ _ g (a.coordinates v) - a.coordinates v ∈ _
  rw [naturalAction_apply, ← map_sub, a.mem_spaceOf_coordinates]
  rw [toMul_sub, div_eq_mul_inv]
  change g.val * v.toMul.val * g.val⁻¹ * v.toMul.val⁻¹ ∈ ⁅A,Y⁆
  rw [commutator_comm A Y]
  exact commutator_mem_commutator hg hv

/-- The actual first residual moves any subgroup marked by the first plane. -/
theorem first_moves_plane (a : NaturalFlag d t) (W : Subgroup G)
    (hW : W ≤ d.UL t)
    (hcut : a.spaceOf W = cutSpace a.basis ⟨1,by have := a.dimension; omega⟩) :
    ⁅W,a.parabolics.Y0⁆ = W := by
  let := a.elementary
  have hn : a.parabolics.P0 ≤ normalizer (W : Set G) :=
    a.node_normalizes_cut W hW _ ⟨1,by have := a.dimension; omega⟩ (by simp) hcut
  apply le_antisymm
    (le_normalizer_iff_commutator_le_left.mp ((map_subtype_le _).trans hn))
  apply (a.spaceOf_le_iff hW).mp
  rw [hcut]
  apply first_plane_le_of_residual_differences (by have := a.dimension; omega)
  intro g hg v hv
  rw [← a.node_residual_image] at hg
  obtain ⟨g,hg,rfl⟩ := hg
  obtain ⟨v,rfl⟩ := a.coordinates.surjective v
  apply a.action_sub_mem_spaceOf_commutator W a.parabolics.Y0 g hg v
  exact (a.mem_spaceOf_coordinates W v).mp (hcut.symm ▸ hv)

/-- The movement clause of original 15.1.29 on the common source triple. -/
theorem first_moves_movingPlane (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : CFSG.Quasithin.ChapterA.Section05To06.IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) :
    ⁅d.nineMovingPlane,a.parabolics.Y0⁆ = d.nineMovingPlane := by
  let s := hs.1.nineSource_of_natural_moved_module hM hu h t ht htS hnat
  obtain ⟨n,hn,⟨e⟩⟩ := hs.2.2
  let hf := facts_of_small_binary_model
    (small_binary_model_of_marking hn e)
  exact a.first_moves_plane _ (d.nineMovingPlane_le_UL s hG h hf t ht htS)
    (a.movingPlane_cut hG hM hu h hs ht htS hnat)


/-- The node core is pulled back through the same natural action. -/
theorem node_core_mem_iff (a : NaturalFlag d t) (i : Fin a.m)
    (g : (d.L ⊔ d.S : Subgroup G)) :
    g.val ∈ (a.node i).pCoreIn 2 ↔
      g.val ∈ a.node i ∧ a.action g ∈ (minimalParabolic a.basis i).pCoreIn 2 := by
  let : Finite (LinearGroup (a.m + 1)) := Finite.of_injective
    (fun g : LinearGroup (a.m + 1) => (g : Space (a.m + 1) → Space (a.m + 1)))
    DFunLike.coe_injective
  have hk : IsPGroup 2 a.action.ker := by
    rw [show a.action.ker = pCore 2 (d.L ⊔ d.S : Subgroup G) from a.kernel]
    exact pCore_isPGroup
  have he := inf_comap_pCoreIn_eq_of_ker_isPGroup 2 a.action
    ((a.node i).subgroupOf (d.L ⊔ d.S)) hk
  rw [a.node_image, pCoreIn_subgroupOf 2 (a.node i) (d.L ⊔ d.S) (a.node_le i)] at he
  exact (SetLike.ext_iff.mp he g).symm

/-- The first node's two-core is its pointwise centralizer of the marked plane. -/
theorem first_core_eq_plane_centralizer (a : NaturalFlag d t) (W : Subgroup G)
    (hW : W ≤ d.UL t)
    (hcut : a.spaceOf W = cutSpace a.basis ⟨1,by have := a.dimension; omega⟩) :
    a.parabolics.P0.pCoreIn 2 = a.parabolics.P0 ⊓ centralizer (W : Set G) := by
  let := a.elementary
  have hm : 2 ≤ a.m := by have := a.dimension; omega
  have hf (g : (d.L ⊔ d.S : Subgroup G)) :
      (∀ w ∈ cutSpace a.basis ⟨1,by omega⟩, a.action g w = w) ↔
        g.val ∈ centralizer (W : Set G) := by
    constructor
    · intro hc w hw
      let v : Additive (d.UL t) := Additive.ofMul ⟨w,hW hw⟩
      have hv : a.coordinates v ∈ cutSpace a.basis ⟨1,by omega⟩ :=
        hcut ▸ (a.mem_spaceOf_coordinates W v).mpr hw
      have he := hc (a.coordinates v) hv
      change naturalAction _ _ _ _ g (a.coordinates v) = _ at he
      rw [naturalAction_apply] at he
      have he' := congrArg (fun u : Additive (d.UL t) => u.toMul.val)
        (a.coordinates.injective he)
      change g.val * w * g.val⁻¹ = w at he'
      exact (mul_inv_eq_iff_eq_mul.mp he').symm
    · intro hc w hw
      obtain ⟨v,rfl⟩ := a.coordinates.surjective w
      have hv := (a.mem_spaceOf_coordinates W v).mp (hcut.symm ▸ hw)
      change naturalAction _ _ _ _ g (a.coordinates v) = _
      rw [naturalAction_apply]
      apply congrArg a.coordinates
      apply Additive.toMul.injective
      apply Subtype.ext
      change g.val * v.toMul.val * g.val⁻¹ = v.toMul.val
      rw [← hc _ hv, mul_inv_cancel_right]
  ext g
  constructor
  · intro hg
    have hgP := pCoreIn_le 2 a.parabolics.P0 hg
    let gH : (d.L ⊔ d.S : Subgroup G) := ⟨g,a.parabolics_le.1 hgP⟩
    have hg' := (a.node_core_mem_iff _ gH).mp hg
    exact ⟨hgP,(hf gH).mp ((mem_first_core_iff hm a.basis _).mp hg'.2).2⟩
  · rintro ⟨hgP,hgW⟩
    let gH : (d.L ⊔ d.S : Subgroup G) := ⟨g,a.parabolics_le.1 hgP⟩
    apply (a.node_core_mem_iff _ gH).mpr
    refine ⟨hgP,(mem_first_core_iff hm a.basis _).mpr ⟨?_,(hf gH).mpr hgW⟩⟩
    have hi := mem_map_of_mem a.action (show gH ∈
      (a.node ⟨0,by omega⟩).subgroupOf (d.L ⊔ d.S) from hgP)
    rwa [a.node_image] at hi

/-- In the source Sylow subgroup the same pointwise centralizer is O₂(P₀). -/
theorem first_core_eq_sylow_plane_centralizer (a : NaturalFlag d t)
    (s : d.ExchangedSource) (W : Subgroup G) (hW : W ≤ d.UL t)
    (hcut : a.spaceOf W = cutSpace a.basis ⟨1,by have := a.dimension; omega⟩) :
    a.parabolics.P0.pCoreIn 2 = d.S ⊓ centralizer (W : Set G) := by
  have he := a.first_core_eq_plane_centralizer W hW hcut
  obtain ⟨P,hP⟩ := a.node_sylow s ⟨0,by have := a.dimension; omega⟩
  have hcoreS : a.parabolics.P0.pCoreIn 2 ≤ d.S := (pCoreIn_le_sylow _ P).trans_eq hP
  apply le_antisymm
  · exact le_inf hcoreS (he.le.trans inf_le_right)
  · rw [he]
    exact inf_le_inf_right _ a.sylow_le.1

/-- Original B.2.3 and 15.1.9 place the first parabolic inside M. -/
theorem first_le_selected (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : CFSG.Quasithin.ChapterA.Section05To06.IsOrderingMaximal T M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) : a.parabolics.P0 ≤ M := by
  let s := hs.1.nineSource_of_natural_moved_module hM hu h t ht htS hnat
  obtain ⟨n,hn,⟨e⟩⟩ := hs.2.2
  let hf := facts_of_small_binary_model (small_binary_model_of_marking hn e)
  have hcore := a.first_core_eq_sylow_plane_centralizer hs.1 d.nineMovingPlane
    (d.nineMovingPlane_le_UL s hG h hf t ht htS)
    (a.movingPlane_cut hG hM hu h hs ht htS hnat)
  have hV2V : d.nineMovingPlane ≤ V := le_sup_right.trans_eq s.planes_sup
  have hZ1V : d.Z1 ≤ V := d.Z1_le_fixed.trans inf_le_left
  have hJV : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (V : Set G) := hJ.trans (centralizer_le hfull.le)
  have hJT : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      (T : Subgroup G) := sSup_le fun _ hA => hA.1
  have hJQ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      a.parabolics.P0.pCoreIn 2 := by
    rw [hcore]
    exact le_inf (le_inf hJT (hJV.trans (centralizer_le hZ1V)))
      (hJV.trans (centralizer_le hV2V))
  have hQT : a.parabolics.P0.pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [hcore]
    exact inf_le_left.trans d.S_le_T
  have he := Stellmacher.elementaryAbelianMaxJ_eq_of_intermediate
    (T : Subgroup G) (a.parabolics.P0.pCoreIn 2) hJQ hQT
  have hnP : a.parabolics.P0 ≤ normalizer
      (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    rw [← he]
    exact (a.parabolics.P0.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image a.parabolics.P0
        (pCore 2 a.parabolics.P0))).trans
      (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ _)
  exact hnP.trans (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
