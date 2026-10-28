module

public import Theory.Representation.HexacodeAction.PlaneStabilizer

/-!
# Odd kernels and normal four-groups in full-weight plane stabilizers

The even hexacode group has order 1080 and its action on the six full-weight
scalar planes covers A₆, so the action kernel has order three. Restricting
this actual action to a plane stabilizer and relabeling the other five planes
produces an A₅ quotient whose kernel embeds in that order-three kernel.
A normal subgroup of order four has trivial image in A₅, which would force
four to divide three.

This is the model calculation used to exclude the full-weight orbit in the
alternative-section repair of Aschbacher–Smith 13.8.21(2), printed p.956
(PDF p.973), combined manuscript of 1 March 2004. The six-plane geometry and
quotient construction are from `PlaneStabilizer` and its attributed ATLAS
ports. Here the restricted quotient is constructed with its kernel map
explicit, supplying the additional odd-kernel bound.
-/

public section

open Atlas.Codes Subgroup
namespace Representation.Hexacode

/-- The kernel of the actual six-plane action has order three. -/
theorem planeAlternating_kernel_card : Nat.card planeAlternating.ker = 3 := by
  have hc : Nat.card (alternatingGroup FullWeightScalarPlane) = 360 := by
    rw [Nat.card_congr (Equiv.altCongrHom
      (Fintype.equivFinOfCardEq fullWeightScalarPlane_card)).toEquiv]
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have h := planeAlternating.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr planeAlternating_surjective,
    Subgroup.card_top, hc, hexEven_card] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 360) h

private noncomputable def fixingProjection
    (P : Submodule (ZMod 2) hexacode) (hP : IsFullWeightScalarPlane P) :
    (hexSign.ker ⊓ BinaryOffender.subspaceStabilizer action P : Subgroup HexAutomorphisms) →*
      fixingSubgroup (alternatingGroup FullWeightScalarPlane)
        (({⟨P,hP⟩} : Finset FullWeightScalarPlane) : Set FullWeightScalarPlane) :=
  (planeAlternating.comp (Subgroup.inclusion inf_le_left)).codRestrict _ (by
    rintro g ⟨Q,hQ⟩
    have he : Q = ⟨P,hP⟩ := Finset.mem_singleton.mp hQ
    subst Q
    exact (planePerm_fixed_iff ⟨g.val,g.property.1⟩ ⟨P,hP⟩).2 g.property.2)

private theorem fixingProjection_surjective
    (P : Submodule (ZMod 2) hexacode) (hP : IsFullWeightScalarPlane P) :
    Function.Surjective (fixingProjection P hP) := by
  intro k
  obtain ⟨g,hg⟩ := planeAlternating_surjective k.val
  have hfix : planePerm g ⟨P,hP⟩ = ⟨P,hP⟩ := by
    change (planeAlternating g).val ⟨P,hP⟩ = ⟨P,hP⟩
    rw [hg]
    exact k.property ⟨⟨P,hP⟩, Finset.mem_singleton_self _⟩
  refine ⟨⟨g.val, g.property, (planePerm_fixed_iff g ⟨P,hP⟩).1 hfix⟩, ?_⟩
  exact Subtype.ext hg

private noncomputable def fixingA5Equiv (P : FullWeightScalarPlane) :
    fixingSubgroup (alternatingGroup FullWeightScalarPlane)
        (({P} : Finset FullWeightScalarPlane) : Set FullWeightScalarPlane) ≃*
      alternatingGroup (Fin 5) := by
  classical
  refine (Atlas.Families.Alternating.stabilizerComplementEquiv {P}).trans
    (Atlas.Families.Alternating.relabel (Fintype.equivFinOfCardEq ?_))
  simp [fullWeightScalarPlane_card]

/-- Restriction to the other five planes gives an A₅ quotient with odd kernel. -/
theorem exists_surjective_planeStabilizer_A5_kernel_card_dvd_three
    (P : Submodule (ZMod 2) hexacode) (hP : IsFullWeightScalarPlane P) :
    ∃ f : (hexSign.ker ⊓ BinaryOffender.subspaceStabilizer action P : Subgroup HexAutomorphisms) →*
        alternatingGroup (Fin 5), Function.Surjective f ∧ Nat.card f.ker ∣ 3 := by
  let f := (fixingA5Equiv ⟨P,hP⟩).toMonoidHom.comp (fixingProjection P hP)
  refine ⟨f, (fixingA5Equiv ⟨P,hP⟩).surjective.comp
    (fixingProjection_surjective P hP), ?_⟩
  have hk : f.ker ≤ (planeAlternating.comp (Subgroup.inclusion inf_le_left)).ker := by
    intro g hg
    have he : fixingProjection P hP g = 1 :=
      (fixingA5Equiv ⟨P,hP⟩).injective (hg.trans (map_one _).symm)
    exact congrArg Subtype.val he
  let k : f.ker →* planeAlternating.ker :=
    ((Subgroup.inclusion inf_le_left).comp f.ker.subtype).codRestrict _ (fun g => hk g.property)
  have hi : Function.Injective k := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : planeAlternating.ker => z.val.val) h))
  have hd := Subgroup.card_dvd_of_injective k hi
  rwa [planeAlternating_kernel_card] at hd

/-- An even full-weight plane stabilizer has no normal subgroup of order four. -/
theorem fullWeightScalarPlaneStabilizer_normal_card_ne_four
    (P : Submodule (ZMod 2) hexacode) (hP : IsFullWeightScalarPlane P)
    (N : Subgroup (hexSign.ker ⊓ BinaryOffender.subspaceStabilizer action P :
      Subgroup HexAutomorphisms)) [N.Normal] : Nat.card N ≠ 4 := by
  intro hfour
  obtain ⟨f,hf,hk⟩ := exists_surjective_planeStabilizer_A5_kernel_card_dvd_three P hP
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : (N.map f).Normal := (inferInstance : N.Normal).map f hf
  rcases (inferInstance : (N.map f).Normal).eq_bot_or_eq_top with hb | ht
  · have hd := Subgroup.card_dvd_of_le ((Subgroup.map_eq_bot_iff N).mp hb)
    rw [hfour] at hd
    have hbad := hd.trans hk
    norm_num at hbad
  · have hd := N.card_map_dvd f
    rw [ht, Subgroup.card_top, hfour] at hd
    rw [nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd

end Representation.Hexacode
