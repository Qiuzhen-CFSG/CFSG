module

public import Theory.Representation.HexacodeAction.EvenOrbitWeights
public import Theory.Representation.HexacodeAction.PlaneStabilizer.TwoCore

/-!
# The actual full-weight vector stabilizer is A5

Restrict the action on the six full-weight scalar planes to the subgroup
fixing a specified nonzero vector. The cubic kernel acts by the primitive
field scalars and intersects this vector stabilizer trivially. Its orbit
has size eighteen, so the vector stabilizer has order sixty and its faithful
action on the other five scalar planes is the full alternating group.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 12.7.4(2),
printed pp.839--840. The original ATLAS hexacode and scalar are retained;
see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode

/-- The actual even actor fixing a specified hexacode vector. -/
@[expose] def fullWeightVectorStabilizer (v : hexacode) : Subgroup HexEvenAutomorphisms where
  carrier := {g | evenAction g v = v}
  one_mem' := by change evenAction 1 v = v; rw [map_one]; rfl
  mul_mem' := by
    intro g h hg hh
    change evenAction (g*h) v = v
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    have h := congrArg (evenAction g⁻¹) hg
    change (evenAction g⁻¹ * evenAction g) v = evenAction g⁻¹ v at h
    rw [← map_mul, inv_mul_cancel, map_one] at h
    exact h.symm

private theorem fixes_field_point (v : hexacode) (g : fullWeightVectorStabilizer v) :
    g.val.val ∈ BinaryOffender.subspaceStabilizer action
      ((Submodule.span F {v}).restrictScalars Bit) := by
  intro w
  constructor
  · intro hw
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hw
    apply Submodule.mem_span_singleton.mpr
    refine ⟨r, ?_⟩
    apply (evenFieldAction g.val).injective
    rw [map_smul]
    exact (congrArg (fun z => r • z) g.property).trans hr
  · intro hw
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    apply Submodule.mem_span_singleton.mpr
    refine ⟨r, ?_⟩
    change r • v = evenFieldAction g.val (r • v)
    rw [map_smul]
    exact congrArg (fun z => r • z) g.property.symm

private def pointFixingProjection (v : hexacode)
    (hP : IsFullWeightScalarPlane ((Submodule.span F {v}).restrictScalars Bit)) :
    fullWeightVectorStabilizer v →*
      fixingSubgroup (alternatingGroup FullWeightScalarPlane)
        (({⟨(Submodule.span F {v}).restrictScalars Bit, hP⟩} : Finset FullWeightScalarPlane) :
          Set FullWeightScalarPlane) :=
  (planeAlternating.comp (fullWeightVectorStabilizer v).subtype).codRestrict _ (by
    rintro g ⟨Q, hQ⟩
    have he : Q = ⟨(Submodule.span F {v}).restrictScalars Bit, hP⟩ := Finset.mem_singleton.mp hQ
    subst Q
    exact (planePerm_fixed_iff g.val _).mpr (fixes_field_point v g))

private def pointFixingEquiv (v : hexacode)
    (hP : IsFullWeightScalarPlane ((Submodule.span F {v}).restrictScalars Bit)) :
    fixingSubgroup (alternatingGroup FullWeightScalarPlane)
      (({⟨(Submodule.span F {v}).restrictScalars Bit, hP⟩} : Finset FullWeightScalarPlane) :
        Set FullWeightScalarPlane) ≃* alternatingGroup (Fin 5) := by
  classical
  refine (Atlas.Families.Alternating.stabilizerComplementEquiv _).trans
    (Atlas.Families.Alternating.relabel (Fintype.equivFinOfCardEq ?_))
  simp [fullWeightScalarPlane_card]

/-- The original six-plane action restricted to the vector stabilizer,
followed by the permutation marking on the other five planes. -/
def fullWeightVectorStabilizerA5 (v : hexacode)
    (hP : IsFullWeightScalarPlane ((Submodule.span F {v}).restrictScalars Bit)) :
    fullWeightVectorStabilizer v →* alternatingGroup (Fin 5) :=
  (pointFixingEquiv v hP).toMonoidHom.comp (pointFixingProjection v hP)

private theorem plane_kernel_eq_scalar : planeAlternating.ker = zpowers hexEvenZ := by
  have hz : hexEvenZ ∈ planeAlternating.ker := Subtype.ext planePerm_scalar
  have hle : zpowers hexEvenZ ≤ planeAlternating.ker := zpowers_le.mpr hz
  exact (eq_of_le_of_card_ge hle (by
    rw [Nat.card_zpowers, hexEvenZ_order, planeAlternating_kernel_card])).symm

private theorem scalar_fixed_trivial (v : hexacode) (hv : v ≠ 0)
    (g : HexEvenAutomorphisms) (hg : g ∈ zpowers hexEvenZ)
    (hfix : evenAction g v = v) : g = 1 := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hexEvenZ_order] at hg
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hg
  have hn3 : n < 3 := Finset.mem_range.mp hn
  have hscalar : evenAction hexEvenZ v = omega • v := scalar_eq_omega_smul v
  interval_cases n
  · exact pow_zero _
  · have he : omega • v = (1 : F) • v := by simpa only [pow_one, hscalar, one_smul] using hfix
    have hh : (omega - 1) • v = 0 := by rw [sub_smul, he, sub_self]
    rcases smul_eq_zero.mp hh with h | h
    · exact False.elim ((by decide : omega ≠ 1) (sub_eq_zero.mp h))
    · exact False.elim (hv h)
  · have he : (omega ^ 2) • v = (1 : F) • v := by
      change evenAction (hexEvenZ * hexEvenZ) v = v at hfix
      rw [map_mul, Module.End.mul_apply, hscalar] at hfix
      change evenFieldAction hexEvenZ (omega • v) = v at hfix
      rw [map_smul] at hfix
      change omega • (evenAction hexEvenZ v) = v at hfix
      rw [hscalar] at hfix
      simpa only [pow_two, mul_smul, one_smul] using hfix
    have hh : (omega ^ 2 - 1) • v = 0 := by rw [sub_smul, he, sub_self]
    rcases smul_eq_zero.mp hh with h | h
    · exact False.elim ((by decide : omega ^ 2 ≠ 1) (sub_eq_zero.mp h))
    · exact False.elim (hv h)

/-- Fixing a nonzero vector removes the whole cubic scalar kernel. -/
theorem fullWeightVectorStabilizerA5_injective (v : hexacode) (hv : v ≠ 0)
    (hP : IsFullWeightScalarPlane ((Submodule.span F {v}).restrictScalars Bit)) :
    Function.Injective (fullWeightVectorStabilizerA5 v hP) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  change (pointFixingEquiv v hP) (pointFixingProjection v hP g) = 1 at hg
  have he : pointFixingProjection v hP g = 1 :=
    (pointFixingEquiv v hP).injective (hg.trans (map_one _).symm)
  have hk : g.val ∈ planeAlternating.ker := congrArg Subtype.val he
  rw [plane_kernel_eq_scalar] at hk
  exact Subtype.ext (scalar_fixed_trivial v hv g.val hk g.property)

/-- A full-weight vector has orbit eighteen and actual stabilizer sixty. -/
theorem fullWeightVectorStabilizer_card (v : hexacode) (hv : v ≠ 0)
    (hP : IsFullWeightScalarPlane ((Submodule.span F {v}).restrictScalars Bit)) :
    Nat.card (fullWeightVectorStabilizer v) = 60 := by
  let : MulAction HexEvenAutomorphisms hexacode := {
    smul := fun g w => evenAction g w
    one_smul := fun w => by change evenAction 1 w = w; rw [map_one]; rfl
    mul_smul := fun g h w => by
      change evenAction (g*h) w = evenAction g (evenAction h w)
      rw [map_mul, Module.End.mul_apply] }
  have hweight : hammingNorm v.val = 6 :=
    hP.2.2 ⟨v, Submodule.mem_span_singleton_self v⟩ (fun h => hv (congrArg Subtype.val h))
  have ho : (MulAction.orbit HexEvenAutomorphisms v).ncard = 18 := by
    exact (evenAction_orbit_card v hv).trans (by simp [hweight])
  have hc := (fullWeightVectorStabilizer v).card_mul_index
  have hi : (fullWeightVectorStabilizer v).index = 18 :=
    (MulAction.index_stabilizer HexEvenAutomorphisms v).trans ho
  rw [hi, hexEven_card] at hc
  omega

/-- The faithful action on the other five planes has the whole A5 image. -/
theorem fullWeightVectorStabilizerA5_surjective (v : hexacode) (hv : v ≠ 0)
    (hP : IsFullWeightScalarPlane ((Submodule.span F {v}).restrictScalars Bit)) :
    Function.Surjective (fullWeightVectorStabilizerA5 v hP) := by
  apply ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨fullWeightVectorStabilizerA5_injective v hv hP, ?_⟩).2
  rw [fullWeightVectorStabilizer_card v hv hP, nat_card_alternatingGroup]
  norm_num

/-- The exact vector-stabilizer identification induced by its six-plane action. -/
@[expose] def fullWeightVectorStabilizerEquiv (v : hexacode) (hv : v ≠ 0)
    (hP : IsFullWeightScalarPlane ((Submodule.span F {v}).restrictScalars Bit)) :
    fullWeightVectorStabilizer v ≃* alternatingGroup (Fin 5) :=
  MulEquiv.ofBijective (fullWeightVectorStabilizerA5 v hP)
    ⟨fullWeightVectorStabilizerA5_injective v hv hP,
      fullWeightVectorStabilizerA5_surjective v hv hP⟩

end Representation.Hexacode
