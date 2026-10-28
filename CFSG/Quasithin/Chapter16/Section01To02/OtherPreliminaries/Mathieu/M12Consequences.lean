module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.Statements
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# M₁₂ component and Sylow-index consequences

The S₃/Q₈² branch is solvable because both its actual normal kernel and its
quotient are solvable. It therefore has no quasisimple component. In either
product branch, a Sylow two-subgroup has order 64, whereas the intersection
with the fixed subgroup has order dividing gcd(64,240) = 16. Its index is
therefore greater than two, independently of which Sylow subgroup was chosen.

Source: Aschbacher–Smith 16.1.5(4) and the M₁₂ application in 16.1.7–8,
combined manuscript of 1 March 2004, printed pp.1171–1173. The final theorem
is conditional on the exact table alternative; the exhaustive table remains
an obligation of the source assembly. No component classification follows
merely from the order of a centralizer.
-/

public section

open Subgroup Sporadic.Mathieu Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu

private theorem s3_solvable : Group.IsSolvable S3 := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range
    (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]

/-- The quaternion-kernel branch of the M₁₂ table is solvable. -/
theorem quaternionExtension_solvable {C : Type*} [Group C] [Finite C] (h : IsM12QuaternionExtension C) :
    Group.IsSolvable C := by
  obtain ⟨Q, hQn, ⟨d⟩, ⟨e⟩⟩ := h
  let := hQn
  let : Group.IsNilpotent Q := (IsPGroup.of_card (p := 2) (n := 5) d.card).isNilpotent
  let : Group.IsSolvable S3 := s3_solvable
  let : Group.IsSolvable (C ⧸ Q) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact (Group.isSolvable_iff_subgroup_quotient Q).mpr ⟨inferInstance, inferInstance⟩

private theorem index_bound (C : Subgroup M12) (hC : Nat.card C ∣ 240) (S : Sylow 2 M12) :
    2 < C.relIndex (S : Subgroup M12) := by
  have hS : Nat.card S = 64 := S.card_eq_multiplicity.trans (by rw [m12_order]; decide +kernel)
  let K := C.subgroupOf (S : Subgroup M12)
  let f : K →* C :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : C => (t : M12)) h
  have hdC : Nat.card K ∣ 240 := (card_dvd_of_injective f hf).trans hC
  have hdS : Nat.card K ∣ 64 := hS ▸ K.card_subgroup_dvd_card
  have hgcd := Nat.dvd_gcd hdS hdC
  norm_num at hgcd
  have hle : Nat.card K ≤ 16 := Nat.le_of_dvd (by decide) hgcd
  have he := K.card_mul_index
  rw [hS] at he
  change 2 < K.index
  nlinarith

/-- Both product branches have fixed-point index greater than two in every Sylow subgroup. -/
theorem m12_product_fixed_sylow_index (r : MulAut M12)
    (hC : Nonempty (r.fixedSubgroup ≃* C2 × S5) ∨ Nonempty (r.fixedSubgroup ≃* C2 × A5))
    (S : Sylow 2 M12) : 2 < r.fixedSubgroup.relIndex (S : Subgroup M12) := by
  apply index_bound r.fixedSubgroup _ S
  rcases hC with hC | hC
  · obtain ⟨e⟩ := hC
    have hc : Nat.card r.fixedSubgroup = 240 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod]
      norm_num [C2, S5, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [hc]
  · obtain ⟨e⟩ := hC
    have hc : Nat.card r.fixedSubgroup = 120 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod]
      change Nat.card C2 * Nat.card (alternatingGroup (Fin 5)) = 120
      rw [nat_card_alternatingGroup, Nat.card_fin]
      norm_num [C2, Nat.card_eq_fintype_card, Nat.factorial]
    rw [hc]
    decide

/-- The quaternion-kernel branch contributes no components to 16.1.7. -/
theorem quaternionExtension_no_component {C : Type*} [Group C] [Finite C]
    (h : IsM12QuaternionExtension C) (K : Subgroup C) : ¬ IsComponent C K := by
  let : Group.IsSolvable C := quaternionExtension_solvable h
  intro hK
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  exact Group.IsPerfect.not_isSolvable K inferInstance

/-- The exact table implies the M₁₂ strict-index assertion used in 16.1.8. -/
theorem m12_component_index_of_alternative (r : MulAut M12)
    (ht : M12InvolutionAlternative r) (K : Subgroup r.fixedSubgroup)
    (hK : IsComponent r.fixedSubgroup K) (S : Sylow 2 M12) :
    2 < r.fixedSubgroup.relIndex (S : Subgroup M12) := by
  rcases ht with ⟨_, hq | hp⟩ | ⟨_, hp⟩
  · exact (quaternionExtension_no_component hq K hK).elim
  · exact m12_product_fixed_sylow_index r (Or.inl hp) S
  · exact m12_product_fixed_sylow_index r (Or.inr hp) S
end CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
