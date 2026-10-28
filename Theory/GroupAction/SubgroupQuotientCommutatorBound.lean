module

public import Theory.GroupAction.SubgroupQuotientCommutatorImage

/-!
# Lift quotient point control to an ambient commutator bound

For the supplied quotient-conjugation action of P on Q/Z, suppose K lies
in P and C lies in Q. If every point displacement from K on C maps into
the image of R, then the ambient commutator [K,C] lies in R joined with Z.
The actual action formula and normality instance are retained explicitly.

Apply point control to inverse points. Expanding the literal conjugation
formula identifies their action differences with the quotient image of each
group commutator. Lift this image to an element of R. Equality of quotient
cosets places the quotient of the two ambient elements in Z, so their product
lies in R joined with Z. Commutator generation finishes the containment.

This is the native quotient-action transfer used in Stellmacher (9.10),
printed p.57, after the canonical support displacement bound. It is independent
of finite cardinality, elementary modules, and graph hypotheses.
-/

namespace Subgroup
open scoped commutatorElement

public theorem quotient_conjugation_commutator_le_sup
    {G : Type*} [Group G]
    (P Q Z C K R : Subgroup G)
    (hPQ : P ≤ normalizer (Q : Set G)) (hKP : K ≤ P) (hCQ : C ≤ Q)
    [(Z.subgroupOf Q).Normal]
    (action : P →* MulAut (Q ⧸ Z.subgroupOf Q))
    (hformula : ∀ actor : P, ∀ point : Q,
      action actor (QuotientGroup.mk' (Z.subgroupOf Q) point) =
        QuotientGroup.mk' (Z.subgroupOf Q)
          ⟨(actor : G) * (point : G) * (actor : G)⁻¹,
            (mem_normalizer_iff.mp (hPQ actor.property) point).mp point.property⟩)
    (hcontrol : ∀ actor : P, (actor : G) ∈ K → ∀ point : Q, (point : G) ∈ C →
      (QuotientGroup.mk' (Z.subgroupOf Q) point)⁻¹ *
        action actor (QuotientGroup.mk' (Z.subgroupOf Q) point) ∈
          (R.subgroupOf Q).map (QuotientGroup.mk' (Z.subgroupOf Q))) :
    ⁅K, C⁆ ≤ R ⊔ Z := by
  let projection := QuotientGroup.mk' (Z.subgroupOf Q)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro point hpoint actor hactor
  let pointQ : Q := ⟨point, hCQ hpoint⟩
  let actorP : P := ⟨actor, hKP hactor⟩
  have hcomm : ⁅point, actor⁆ ∈ Q :=
    (le_normalizer_iff_commutator_le_left.mp (hKP.trans hPQ))
      (commutator_mem_commutator (hCQ hpoint) hactor)
  have himage := hcontrol actorP hactor pointQ⁻¹ (C.inv_mem hpoint)
  have heq : (projection pointQ⁻¹)⁻¹ * action actorP (projection pointQ⁻¹) =
      projection ⟨⁅point, actor⁆, hcomm⟩ := by
    rw [hformula, ← map_inv, ← map_mul]
    apply congrArg projection
    apply Subtype.ext
    simp only [coe_mul, coe_inv, inv_inv, commutatorElement_def, pointQ, actorP, mul_assoc]
  change (projection pointQ⁻¹)⁻¹ * action actorP (projection pointQ⁻¹) ∈ _ at himage
  rw [heq] at himage
  obtain ⟨lift, hlift, hequal⟩ := himage
  have hquotient := (QuotientGroup.eq_iff_div_mem.mp hequal.symm)
  change ⁅point, actor⁆ / (lift : G) ∈ Z at hquotient
  have hproduct := (R ⊔ Z).mul_mem
    ((show Z ≤ R ⊔ Z from le_sup_right) hquotient)
    ((show R ≤ R ⊔ Z from le_sup_left) hlift)
  change ⁅point, actor⁆ / (lift : G) * (lift : G) ∈ R ⊔ Z at hproduct
  simpa only [div_mul_cancel] using hproduct

end Subgroup
