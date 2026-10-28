module

public import Theory.Representation.PSL3Two.SteinbergStructure.ParabolicFactors.Basic
public import Theory.Representation.PSL3Two.SteinbergStructure.ParabolicFactors.Calculations

/-!
# The three noncentral chief factors of each binary parabolic

The coordinate flag has five sections, of dimensions 2, 1, 2, 1, 2. On each
two-dimensional section an element of order three spans the section from any
nonzero coset, proving simplicity. The other two sections are central and
one-dimensional. Thus this is a genuine chief series with exactly three
noncentral factors. Flag duality gives the marked line parabolic, and the
actual representation equivalences transport the result to all conjugates.

Source: Aschbacher–Smith H.6.3(3), printed pp.387–388, combined manuscript
of 1 March 2004. All assertions concern the literal trace-zero adjoint module.
-/

public section
open Matrix Representation
open BinaryLinearThree BinaryLinearThree.IrreducibleCatalogue Matrix.PSL3Two
open BinaryLinearThree.SteinbergStructure.ParabolicFactors.Calculations
namespace BinaryLinearThree.SteinbergStructure.ParabolicFactors
private theorem coordinates_action (g : Group) (v : Steinberg) :
    coordinates (S g v) = action g (coordinates v) := by
  have hv : (matrixOf (coordinates v)).toLin' = v.val :=
    congrArg Subtype.val (coordinates.symm_apply_apply v)
  have hm (h : Group) : LinearMap.toMatrix' (W h) = h.val :=
    LinearMap.toMatrix'_toLin' h.val
  change readMatrix (LinearMap.toMatrix' (W g ∘ₗ v.val ∘ₗ W g⁻¹)) = _
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hm, hm, ← hv,
    LinearMap.toMatrix'_toLin']
  simp only [action, Matrix.mul_assoc]

private theorem action_linear (g : Group) : ∃ f : Eight →ₗ[ZMod 2] Eight, ∀ v, f v = action g v := by
  refine ⟨coordinates.conj (S g), fun v => ?_⟩
  simpa using coordinates_action g (coordinates.symm v)
private theorem invariant (i : Fin 6) (g : Group) (hg : g ∈ pointParabolicSL)
    (v : Eight) (hv : inLayer i v) : inLayer i (action g v) := by
  obtain ⟨f, hf⟩ := action_linear g
  rw [← hf]
  have hsum : v = ∑ j : Fin 8, v j • Pi.single j 1 := pi_eq_sum_univ' v
  rw [hsum, map_sum]
  apply (coordinateLayer i).sum_mem
  intro j hj
  rw [map_smul]
  by_cases ha : allowed i j = true
  · apply (coordinateLayer i).smul_mem
    rw [hf]
    exact invariant_certificate i g ((mem_pointParabolicSL_iff g).mp hg).1
      ((mem_pointParabolicSL_iff g).mp hg).2 j ha
  · have hz : v j = 0 := hv j (Bool.eq_false_iff.mpr ha)
    rw [hz, zero_smul]
    exact (coordinateLayer i).zero_mem

noncomputable def pointLayer (i : Fin 6) : Subrepresentation (S.comp pointParabolicSL.subtype) where
  toSubmodule := (coordinateLayer i).comap coordinates.toLinearMap
  apply_mem_toSubmodule g v hv := by
    change inLayer i (coordinates (S g.val v))
    rw [coordinates_action]
    exact invariant i g.val g.property (coordinates v) hv

set_option backward.isDefEq.respectTransparency false in
theorem pointLayer_chief (i : Fin 5) : pointLayer i.castSucc ⋖ pointLayer i.succ := by
  have hle : pointLayer i.castSucc ≤ pointLayer i.succ := fun v hv => layer_inclusion i _ hv
  apply covBy_of_eq_or_eq
  · refine lt_of_le_not_ge hle ?_
    intro h
    obtain ⟨v,hv,hn⟩ := layer_strict i
    have hh := h (show coordinates.symm v ∈ pointLayer i.succ by
      change inLayer i.succ (coordinates (coordinates.symm v)); simpa using hv)
    change inLayer i.castSucc (coordinates (coordinates.symm v)) at hh
    exact hn (by simpa using hh)
  · intro P hlow hupp
    by_cases he : P ≤ pointLayer i.castSucc
    · exact Or.inl (le_antisymm he hlow)
    · right
      apply le_antisymm hupp
      obtain ⟨x,hx,hn⟩ := SetLike.not_le_iff_exists.mp he
      have hxu := hupp hx
      have hxn : sectionCoord i (coordinates x) ≠ 0 := by
        intro hz
        exact hn ((layer_kernel i _ hxu).mpr hz)
      intro y hy
      obtain ⟨a,b,hab⟩ := simple_certificate i (sectionCoord i (coordinates x))
        (sectionCoord i (coordinates y)) (section_valid i _) hxn (section_valid i _)
      have hcx : S cubic x ∈ P := P.apply_mem_toSubmodule ⟨cubic,cubic_mem⟩ hx
      have hcomb : a • x + b • S cubic x ∈ P :=
        P.toSubmodule.add_mem (P.toSubmodule.smul_mem a hx) (P.toSubmodule.smul_mem b hcx)
      have hres : y - (a • x + b • S cubic x) ∈ pointLayer i.castSucc := by
        apply (layer_kernel i _ ?_).mpr
        · change sectionMap i (coordinates (y - (a • x + b • S cubic x))) = 0
          rw [map_sub coordinates, map_add coordinates, map_smul coordinates,
            map_smul coordinates, map_sub (sectionMap i), map_add (sectionMap i),
            map_smul (sectionMap i), map_smul (sectionMap i)]
          change sectionCoord i (coordinates y) -
            (a • sectionCoord i (coordinates x) + b • sectionCoord i (coordinates (S cubic x))) = 0
          rw [coordinates_action, section_action i (coordinates x) hxu, hab, sub_self]
        · exact (pointLayer i.succ).toSubmodule.sub_mem hy (hupp hcomb)
      have hh := P.toSubmodule.add_mem (hlow hres) hcomb
      rw [sub_add_cancel y (a • x + b • S cubic x)] at hh
      exact hh

open scoped MonoidAlgebra in
/-- Each displayed section is simple for the actual restricted parabolic action. -/
theorem pointLayer_simple (i : Fin 5) :
    IsSimpleModule (ZMod 2)[pointParabolicSL]
      ((pointLayer i.succ).asSubmodule ⧸
        Submodule.comap (pointLayer i.succ).asSubmodule.subtype
          (pointLayer i.castSucc).asSubmodule) :=
  chiefFactor_simple pointParabolicSL _ _ (pointLayer_chief i)

private theorem linear_maps_layer (i j : Fin 6) (f : Eight →ₗ[ZMod 2] Eight)
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

theorem pointLayer_central_iff (i : Fin 5) :
    CentralSection pointParabolicSL (pointLayer i.castSucc) (pointLayer i.succ) ↔
      i = 1 ∨ i = 3 := by
  constructor
  · intro hc
    by_contra hi
    obtain ⟨v,hv,hn⟩ := noncentral_certificate i hi
    have hh := hc ⟨cubic,cubic_mem⟩ (coordinates.symm v)
      (by change inLayer i.succ (coordinates (coordinates.symm v)); simpa using hv)
    change inLayer i.castSucc (coordinates (S cubic (coordinates.symm v) - coordinates.symm v)) at hh
    rw [map_sub coordinates, coordinates_action, coordinates.apply_symm_apply] at hh
    exact hn hh
  · intro hi g v hv
    change inLayer i.castSucc (coordinates (S g.val v - v))
    rw [map_sub coordinates, coordinates_action]
    obtain ⟨f,hf⟩ := action_linear g.val
    rw [← hf]
    let d : Eight →ₗ[ZMod 2] Eight := f - LinearMap.id
    change inLayer i.castSucc (d (coordinates v))
    apply linear_maps_layer i.succ i.castSucc d ?_ (coordinates v) hv
    intro j hj
    change inLayer i.castSucc (f (Pi.single j 1) - Pi.single j 1)
    rw [hf]
    exact central_certificate i hi g.val ((mem_pointParabolicSL_iff g.val).mp g.property).1
      ((mem_pointParabolicSL_iff g.val).mp g.property).2 j hj

theorem point_three_noncentral : HasThreeNoncentralChiefFactors pointParabolicSL := by
  refine ⟨pointLayer, ?_, ?_, pointLayer_chief, {0,2,4}, by decide, ?_⟩
  · apply Subrepresentation.toSubmodule_injective
    apply Submodule.ext
    intro v
    change inLayer 0 (coordinates v) ↔ v = 0
    have hh : ∀ w : Eight, inLayer 0 w ↔ w = 0 := by decide +kernel
    rw [hh]
    exact coordinates.map_eq_zero_iff
  · apply Subrepresentation.toSubmodule_injective
    apply Submodule.ext
    intro v
    change inLayer 5 (coordinates v) ↔ True
    have hh : ∀ w : Eight, inLayer 5 w := by decide +kernel
    exact iff_true_intro (hh _)
  · intro i
    rw [pointLayer_central_iff]
    fin_cases i <;> decide

theorem line_three_noncentral : HasThreeNoncentralChiefFactors lineParabolicSL := by
  rw [← flagDuality_map_point]
  exact HasThreeNoncentralChiefFactors.map _ point_three_noncentral flagDuality

theorem parabolic_conjugate_three_noncentral (H : Subgroup Group)
    (hH : H = pointParabolicSL ∨ H = lineParabolicSL) (g : Group) :
    HasThreeNoncentralChiefFactors (H.map (MulAut.conj g).toMonoidHom) := by
  apply HasThreeNoncentralChiefFactors.map
  rcases hH with rfl | rfl
  · exact point_three_noncentral
  · exact line_three_noncentral

end BinaryLinearThree.SteinbergStructure.ParabolicFactors
