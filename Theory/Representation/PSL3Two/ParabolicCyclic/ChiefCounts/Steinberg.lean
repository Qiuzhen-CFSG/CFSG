module

public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Actor
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Reindex
public import Theory.Representation.PSL3Two.SteinbergStructure.ParabolicFactors.PointSeries

/-!
# The Steinberg count on the embedded line residual

The coordinate flag for the point parabolic remains a chief flag after
restriction to its embedded two-residual.  The same cubic used in the
coordinate certificates belongs to that residual, so the cover and
noncentrality arguments still apply.  We then transport the flag through the
actual inverse-transpose duality and identify its image residual with the
marked line residual.

Source: Aschbacher--Smith H.6.3(3), printed pp.387--388, and 14.7.22(2).
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

open Matrix Representation
open BinaryLinearThree BinaryLinearThree.IrreducibleCatalogue Matrix.PSL3Two
open BinaryLinearThree.SteinbergStructure.ParabolicFactors
open BinaryLinearThree.SteinbergStructure.ParabolicFactors.Calculations
namespace BinaryLinearThree.ParabolicCyclic.ChiefCounts

private def pointResidualActor : Subgroup Group :=
  (pResidual 2 pointParabolicSL).map pointParabolicSL.subtype

private theorem pointResidualActor_le : pointResidualActor ≤ pointParabolicSL := by
  rintro g ⟨x, _, rfl⟩
  exact x.property

private theorem pointResidual_map_duality :
    pointResidualActor.map flagDuality.toMonoidHom = actor := by
  change ((pResidual 2 pointParabolicSL).map pointParabolicSL.subtype).map
    flagDuality.toMonoidHom = actor
  rw [Subgroup.map_embedded_pResidual, flagDuality_map_point]
  rfl

private theorem point_cubic_mem_residual : cubic ∈ pointResidualActor := by
  let x : pointParabolicSL := ⟨cubic, cubic_mem⟩
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    decide
  exact ⟨x, Subgroup.mem_pResidual_of_orderOf_coprime
    (Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hx3) (by decide)), rfl⟩

private theorem residual_coordinates_action (g : Group) (v : Steinberg) :
    coordinates (S g v) = action g (coordinates v) := by
  have hv : (matrixOf (coordinates v)).toLin' = v.val :=
    congrArg Subtype.val (coordinates.symm_apply_apply v)
  have hm (h : Group) : LinearMap.toMatrix' (W h) = h.val :=
    LinearMap.toMatrix'_toLin' h.val
  change readMatrix (LinearMap.toMatrix' (W g ∘ₗ v.val ∘ₗ W g⁻¹)) = _
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hm, hm, ← hv,
    LinearMap.toMatrix'_toLin']
  simp only [action, Matrix.mul_assoc]

private theorem residual_invariant (i : Fin 6) (g : Group)
    (hg : g ∈ pointParabolicSL) (v : Eight) (hv : inLayer i v) :
    inLayer i (action g v) := by
  let f : Eight →ₗ[ZMod 2] Eight := coordinates.conj (S g)
  have hf (w : Eight) : f w = action g w := by
    change coordinates (S g (coordinates.symm w)) = action g w
    rw [residual_coordinates_action, coordinates.apply_symm_apply]
  rw [← hf]
  have hsum : v = ∑ j : Fin 8, v j • Pi.single j 1 := pi_eq_sum_univ' v
  rw [hsum, map_sum]
  apply (coordinateLayer i).sum_mem
  intro j hj
  rw [map_smul]
  by_cases ha : allowed i j = true
  · apply (coordinateLayer i).smul_mem
    rw [hf]
    exact invariant_certificate i g
      ((mem_pointParabolicSL_iff g).mp hg).1
      ((mem_pointParabolicSL_iff g).mp hg).2 j ha
  · have hz : v j = 0 := hv j (Bool.eq_false_iff.mpr ha)
    rw [hz, zero_smul]
    exact (coordinateLayer i).zero_mem

private theorem residual_linear_maps_layer (i j : Fin 6)
    (f : Eight →ₗ[ZMod 2] Eight)
    (hf : ∀ k, allowed i k = true → inLayer j (f (Pi.single k 1)))
    (v : Eight) (hv : inLayer i v) : inLayer j (f v) := by
  have hsum : v = ∑ k : Fin 8, v k • Pi.single k 1 := pi_eq_sum_univ' v
  rw [hsum, map_sum]
  apply (coordinateLayer j).sum_mem
  intro k hk
  rw [map_smul]
  by_cases ha : allowed i k = true
  · exact (coordinateLayer j).smul_mem _ (hf k ha)
  · have hz : v k = 0 := hv k (Bool.eq_false_iff.mpr ha)
    rw [hz, zero_smul]
    exact (coordinateLayer j).zero_mem

private noncomputable def pointResidualLayer (i : Fin 6) :
    Subrepresentation (S.comp pointResidualActor.subtype) where
  toSubmodule := (coordinateLayer i).comap coordinates.toLinearMap
  apply_mem_toSubmodule g v hv := by
    change inLayer i (coordinates (S g.val v))
    rw [residual_coordinates_action]
    change inLayer i (coordinates v) at hv
    exact residual_invariant i g.val (pointResidualActor_le g.property)
      (coordinates v) hv

private theorem pointResidualLayer_mem (i : Fin 6) (v : Steinberg) :
    v ∈ pointResidualLayer i ↔ inLayer i (coordinates v) := by
  rfl

private theorem pointResidualLayer_chief (i : Fin 5) :
    pointResidualLayer i.castSucc ⋖ pointResidualLayer i.succ := by
  have hle : pointResidualLayer i.castSucc ≤ pointResidualLayer i.succ :=
    fun v hv => (pointResidualLayer_mem i.succ v).mpr
      (layer_inclusion i _ ((pointResidualLayer_mem i.castSucc v).mp hv))
  apply covBy_of_eq_or_eq
  · refine lt_of_le_not_ge hle ?_
    intro h
    obtain ⟨v, hv, hn⟩ := layer_strict i
    have hh := h (show coordinates.symm v ∈ pointResidualLayer i.succ by
      exact (pointResidualLayer_mem i.succ _).mpr (by simpa using hv))
    have hh' : inLayer i.castSucc (coordinates (coordinates.symm v)) :=
      (pointResidualLayer_mem i.castSucc _).mp hh
    exact hn (by simpa using hh')
  · intro P hlow hupp
    by_cases he : P ≤ pointResidualLayer i.castSucc
    · exact Or.inl (le_antisymm he hlow)
    · right
      apply le_antisymm hupp
      obtain ⟨x, hx, hn⟩ := SetLike.not_le_iff_exists.mp he
      intro y hy
      have hxu := hupp hx
      have hxn : sectionCoord i (coordinates x) ≠ 0 := by
        intro hz
        exact hn ((pointResidualLayer_mem i.castSucc _).mpr
          ((layer_kernel i _ ((pointResidualLayer_mem i.succ _).mp hxu)).mpr hz))
      obtain ⟨a, b, hab⟩ := simple_certificate i (sectionCoord i (coordinates x))
        (sectionCoord i (coordinates y)) (section_valid i _) hxn (section_valid i _)
      have hcx : S cubic x ∈ P :=
        P.apply_mem_toSubmodule ⟨cubic, point_cubic_mem_residual⟩ hx
      have hcomb : a • x + b • S cubic x ∈ P :=
        P.toSubmodule.add_mem (P.toSubmodule.smul_mem a hx)
          (P.toSubmodule.smul_mem b hcx)
      have hres : y - (a • x + b • S cubic x) ∈ pointResidualLayer i.castSucc := by
        apply (pointResidualLayer_mem i.castSucc _).mpr
        apply (layer_kernel i _ ?_).mpr
        · change sectionMap i (coordinates (y - (a • x + b • S cubic x))) = 0
          rw [map_sub coordinates, map_add coordinates, map_smul coordinates,
            map_smul coordinates, map_sub (sectionMap i), map_add (sectionMap i),
            map_smul (sectionMap i), map_smul (sectionMap i)]
          change sectionCoord i (coordinates y) -
            (a • sectionCoord i (coordinates x) + b •
              sectionCoord i (coordinates (S cubic x))) = 0
          rw [residual_coordinates_action,
            section_action i (coordinates x)
              ((pointResidualLayer_mem i.succ _).mp hxu),
            hab, sub_self]
        · exact (pointResidualLayer_mem i.succ _).mp
            ((pointResidualLayer i.succ).toSubmodule.sub_mem hy (hupp hcomb))
      have hh := P.toSubmodule.add_mem (hlow hres) hcomb
      rw [sub_add_cancel y (a • x + b • S cubic x)] at hh
      exact hh

set_option maxHeartbeats 800000 in
private theorem pointResidualLayer_central_iff (i : Fin 5) :
    Central (pointResidualLayer i.castSucc) (pointResidualLayer i.succ) ↔
      i = 1 ∨ i = 3 := by
  constructor
  · intro hc
    by_contra hi
    obtain ⟨v, hv, hn⟩ := noncentral_certificate i hi
    have hh := hc ⟨cubic, point_cubic_mem_residual⟩
      (coordinates.symm v)
      ((pointResidualLayer_mem i.succ _).mpr (by simpa using hv))
    have hh' : inLayer i.castSucc
        (coordinates (S cubic (coordinates.symm v) - coordinates.symm v)) :=
      (pointResidualLayer_mem i.castSucc _).mp hh
    rw [map_sub coordinates, residual_coordinates_action,
      coordinates.apply_symm_apply] at hh'
    exact hn hh'
  · intro hi g v hv
    have hv' : inLayer i.succ (coordinates v) :=
      (pointResidualLayer_mem i.succ v).mp hv
    apply (pointResidualLayer_mem i.castSucc _).mpr
    change inLayer i.castSucc (coordinates (S g.val v - v))
    rw [map_sub coordinates, residual_coordinates_action]
    have hf (w : Eight) : coordinates (S g.val (coordinates.symm w)) =
        action g.val w := by
      simpa using residual_coordinates_action g.val (coordinates.symm w)
    rw [← hf]
    let d : Eight →ₗ[ZMod 2] Eight :=
      coordinates.conj (S g.val) - LinearMap.id
    change inLayer i.castSucc (d (coordinates v))
    apply residual_linear_maps_layer i.succ i.castSucc d ?_ (coordinates v) hv'
    intro j hj
    change inLayer i.castSucc
      ((coordinates.conj (S g.val)) (Pi.single j 1) - Pi.single j 1)
    have hact : (coordinates.conj (S g.val)) (Pi.single j 1) =
        action g.val (Pi.single j 1) := by
      change coordinates (S g.val (coordinates.symm (Pi.single j 1))) = _
      simpa using residual_coordinates_action g.val (coordinates.symm (Pi.single j 1))
    rw [hact]
    exact central_certificate i hi g.val
      ((mem_pointParabolicSL_iff g.val).mp
        (pointResidualActor_le g.property)).1
      ((mem_pointParabolicSL_iff g.val).mp
        (pointResidualActor_le g.property)).2 j hj

private noncomputable def pointResidualSeries :
    Series (S.comp pointResidualActor.subtype) where
  length := 5
  toFun := pointResidualLayer
  step i := pointResidualLayer_chief i

private theorem pointResidualLayer_bot : pointResidualLayer 0 = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  apply Submodule.ext
  intro v
  change inLayer 0 (coordinates v) ↔ v = 0
  have hh : ∀ w : Eight, inLayer 0 w ↔ w = 0 := by decide +kernel
  rw [hh]
  exact coordinates.map_eq_zero_iff

private theorem pointResidualLayer_top : pointResidualLayer 5 = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  apply Submodule.ext
  intro v
  change inLayer 5 (coordinates v) ↔ True
  have hh : ∀ w : Eight, inLayer 5 w := by decide +kernel
  exact iff_true_intro (hh _)

private theorem point_residual_count :
    HasCount (S.comp pointResidualActor.subtype) 3 := by
  refine ⟨pointResidualSeries, pointResidualLayer_bot, pointResidualLayer_top, ?_⟩
  have h : pointResidualSeries.count = ({0, 2, 4} : Finset (Fin 5)).card := by
    apply Series.count_eq_card
    intro i
    change i ∈ ({0, 2, 4} : Finset (Fin 5)) ↔
      ¬ Central (pointResidualLayer i.castSucc) (pointResidualLayer i.succ)
    rw [pointResidualLayer_central_iff]
    fin_cases i <;> decide
  exact h.trans (by decide)

private def dualityResidualHom : pointResidualActor →* actor :=
  (flagDuality.toMonoidHom.comp pointResidualActor.subtype).codRestrict actor
    (by
      intro g
      rw [← pointResidual_map_duality]
      exact Subgroup.mem_map.mpr ⟨g.val, g.property, rfl⟩)

private theorem dualityResidualHom_surjective : Function.Surjective dualityResidualHom := by
  intro g
  obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp (show g.val ∈
      pointResidualActor.map flagDuality.toMonoidHom from by
    rw [pointResidual_map_duality]
    exact g.property)
  exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩

private def dualityResidualHomInv : actor →* pointResidualActor :=
  (flagDuality.symm.toMonoidHom.comp actor.subtype).codRestrict pointResidualActor
    (by
      intro g
      have hm : g.val ∈ pointResidualActor.map flagDuality.toMonoidHom := by
        rw [pointResidual_map_duality]
        exact g.property
      obtain ⟨x, hx, he⟩ := Subgroup.mem_map.mp hm
      have he' := congrArg (fun z : Group => flagDuality.symm z) he
      change flagDuality.symm (flagDuality x) = flagDuality.symm g.val at he'
      rw [flagDuality.symm_apply_apply] at he'
      change flagDuality.symm g.val ∈ pointResidualActor
      exact he'.symm ▸ hx)

private theorem dualityResidualHomInv_surjective :
    Function.Surjective dualityResidualHomInv := by
  intro g
  refine ⟨⟨flagDuality g.val, ?_⟩, ?_⟩
  · rw [← pointResidual_map_duality]
    exact Subgroup.mem_map.mpr ⟨g.val, g.property, rfl⟩
  · apply Subtype.ext
    change flagDuality.symm (flagDuality g.val) = g.val
    simp

private theorem duality_pullback_eq :
    (((S.comp flagDuality.toMonoidHom).comp pointResidualActor.subtype).comp
      dualityResidualHomInv) = S.comp actor.subtype := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  change S (flagDuality (flagDuality.symm g.val)) v = S g.val v
  rw [flagDuality.apply_symm_apply]

/-- The embedded line residual has three noncentral chief factors on Steinberg. -/
theorem steinberg_count : HasCount (S.comp actor.subtype) 3 := by
  have hdual := point_residual_count.mapEquiv
    (restrictEquiv (SteinbergStructure.autEquiv flagDuality)
      pointResidualActor.subtype)
  have hre := HasCount.reindex dualityResidualHomInv
    dualityResidualHomInv_surjective hdual
  rw [duality_pullback_eq] at hre
  exact hre

end BinaryLinearThree.ParabolicCyclic.ChiefCounts
