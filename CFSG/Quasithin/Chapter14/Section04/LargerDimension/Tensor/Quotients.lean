module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Family
public import Theory.SpecificGroups.TensorThreeFiveLocalQuotients

/-!
# Applying the small tensor models to the actual source subgroups

Source: Aschbacher–Smith, Lemma 14.4.10, printed pp.1010–1011.
The actual three-core calculation proves X₁ ∈ X for both possible H*.
A marked S₃ × S₄ image constructs the whole overlap quotient and retains
its quotient-map formula. A marked C₂ × A₄ image contradicts the S₃
quotient from 14.4.8, forcing the symmetric-five actor.

The image equivalences in the latter two deductions are explicit model
placement premises, not proofs that the source subgroups have those images.
The natural tensor geometry must construct them before clause (5) is complete.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
open Theory.SpecificGroups.TensorThreeFive
variable {G : Type*} [Group G] [Finite G]

/-- For either actual H* isomorphism in case (5), X₁ belongs to X. This does
not require a tensor-action or family-membership certificate. -/
theorem first_mem_X {H T : Subgroup G} (hT : T ≤ H)
    (hmodel : Nonempty (coreQuotient H ≃* S3 × Equiv.Perm (Fin 5)) ∨
      Nonempty (coreQuotient H ≃* S3 × alternatingGroup (Fin 5))) :
    first H ∈ XFamily H T :=
  first_mem_X_of_threeCore_card hT (tensor_threeCore_card hmodel)

/-- A concrete S₃ × S₄ image identifies the whole overlap quotient in (5).
The remaining model placement is precisely the equivalence e. -/
noncomputable def overlapQuotientEquiv {H T : Subgroup G} (hT : T ≤ H)
    (e : star H (overlap H T) ≃* S3 × S4) :
    coreQuotient (overlap H T) ≃* S3 × S3 :=
  (starCoreQuotientEquiv (overlap_le hT)).trans
    ((QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans overlapEquiv)

/-- The whole quotient witness is induced by the specified quotient map and
the S₄ action on its double transpositions. -/
theorem overlapQuotientEquiv_mk {H T : Subgroup G} (hT : T ≤ H)
    (e : star H (overlap H T) ≃* S3 × S4) (x : overlap H T) :
    overlapQuotientEquiv hT e (QuotientGroup.mk' _ x) =
      overlapMap (e (starHom (overlap_le hT) x)) := rfl

/-- The C₂ × A₄ local image contradicts the S₃ quotient supplied by 14.4.8
for X₂ ∈ Y. All kernels here are intrinsic two-cores. -/
theorem not_small_image_of_local_symmetric_three {H J : Subgroup G} (hJ : J ≤ H)
    (e : star H J ≃* C2 × A4) (hs : Nonempty (coreQuotient J ≃* S3)) : False := by
  obtain ⟨s⟩ := hs
  let c := (starCoreQuotientEquiv hJ).trans
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hh := Nat.card_congr (c.symm.trans s).toEquiv
  rw [small_quotient_card] at hh
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hh

/-- The forced S₃ × S₅ conclusion once the alternating-case local image has
been computed and 14.4.8 supplies the actual X₂T quotient. The local-image
premise remains to be discharged by the natural tensor calculation. -/
theorem symmetric_five_of_local_image {H T : Subgroup G} (hT : T ≤ H)
    (hmodel : Nonempty (coreQuotient H ≃* S3 × Equiv.Perm (Fin 5)) ∨
      Nonempty (coreQuotient H ≃* S3 × alternatingGroup (Fin 5)))
    (hsmall : Nonempty (coreQuotient H ≃* S3 × alternatingGroup (Fin 5)) →
      Nonempty (star H (second H T ⊔ T) ≃* C2 × A4))
    (hlocal : Nonempty (coreQuotient (second H T ⊔ T) ≃* S3)) :
    Nonempty (coreQuotient H ≃* S3 × Equiv.Perm (Fin 5)) := by
  rcases hmodel with h | h
  · exact h
  · obtain ⟨e⟩ := hsmall h
    exact False.elim (not_small_image_of_local_symmetric_three
      (sup_le (second_le H T) hT) e hlocal)
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor

end
