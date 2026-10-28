module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorLevi
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Compatible Weyl representatives in the actual root actors

A Sylow two-subgroup of N projects isomorphically to W whenever W is a
two-group, since the full Cartan H is odd. Inverting this projection gives
one homomorphic section. Each simple image lies in its actual root actor:
compare it with the actor lift, and use the odd quotient H R_i / R_i.
Thus the involution and dihedral relations hold simultaneously, including
rotation order four and the smallest unitary fields.

Independently of the rotation order, the two actors generate the entire
Weyl-root span. Their internal reflection lifts supply representatives of
every Weyl class, so conjugating their simple roots recovers the span.
The original F.1.1 application identifies this span with the whole quotient.

Source: Fong--Seitz I, following (5C), printed p.26; II, introduction,
pp.191--192. These are unlabelled source lifts. Compatibility with the
field-labelled torus and rank-one matrix equations is still to be proved.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

@[expose] def weylSylow : Sylow 2 Q.tits.N := Classical.choice inferInstance

@[expose] def weylSylowProjection : weylSylow Q →* Weyl Q :=
  (QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)).comp ((weylSylow Q : Subgroup Q.tits.N).subtype)

include split in
theorem weylSylowProjection_injective : Function.Injective (weylSylowProjection Q) := by
  apply injective_comp_subtype_of_coprime_ker (p := 2)
  · rw [QuotientGroup.ker_mk',
      Nat.card_congr (subgroupOfEquivOfLe (show Q.tits.B ⊓ Q.tits.N ≤ Q.tits.N from inf_le_right)).toEquiv]
    exact split.odd
  · exact (weylSylow Q).isPGroup'

theorem weylSylowProjection_surjective (hW : IsPGroup 2 (Weyl Q)) :
    Function.Surjective (weylSylowProjection Q) := by
  let q := QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
  let R : Sylow 2 (Weyl Q) := (weylSylow Q).mapSurjective
    (show Function.Surjective q from QuotientGroup.mk'_surjective _)
  have ht : (R : Subgroup (Weyl Q)) = ⊤ := by
    apply top_unique
    exact (hW.to_subgroup ⊤).le_sylow_of_normal R
  intro w
  have hw : w ∈ (weylSylow Q : Subgroup Q.tits.N).map q := by
    change w ∈ (R : Subgroup (Weyl Q))
    rw [ht]; trivial
  obtain ⟨n,hn,he⟩ := hw
  exact ⟨⟨n,hn⟩,he⟩

@[expose] def weylSylowEquiv (hW : IsPGroup 2 (Weyl Q)) : weylSylow Q ≃* Weyl Q :=
  MulEquiv.ofBijective (weylSylowProjection Q)
    ⟨weylSylowProjection_injective Q split,weylSylowProjection_surjective Q hW⟩

/-- A single Sylow subgroup of N gives one compatible section of the entire Weyl group. -/
@[expose] def actorWeylSection (hW : IsPGroup 2 (Weyl Q)) : Weyl Q →* Q.tits.N :=
  ((weylSylow Q : Subgroup Q.tits.N).subtype).comp (weylSylowEquiv Q split hW).symm.toMonoidHom

@[simp] theorem actorWeylSection_class (hW : IsPGroup 2 (Weyl Q)) (w : Weyl Q) :
    QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
      (actorWeylSection Q split hW w) = w :=
  (weylSylowEquiv Q split hW).apply_symm_apply w

theorem actorWeylSection_simple_mem (hW : IsPGroup 2 (Weyl Q)) (i : Fin 2) :
    (actorWeylSection Q split hW (Q.simple i) : X ⧸ Q.D) ∈ rootActor Q split i := by
  let n := actorWeylSection Q split hW (Q.simple i)
  obtain ⟨r,hr,hR⟩ := exists_actor_weyl_lift Q split i
  have hh : ((r⁻¹*n : Q.tits.N) : X ⧸ Q.D) ∈ Q.tits.B ⊓ Q.tits.N := by
    change r⁻¹*n ∈ (Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (r⁻¹*n) = 1
    rw [map_mul,map_inv,hr,actorWeylSection_class,inv_mul_cancel]
  have hn : (n : X ⧸ Q.D) ∈ rootActor Q split i ⊔ (Q.tits.B ⊓ Q.tits.N) := by
    have he := mul_mem_sup hR hh
    simpa only [coe_mul,coe_inv,mul_inv_cancel_left] using he
  obtain ⟨k,hk⟩ := (weylSylow Q).isPGroup'.exists_pow_pow_eq_one
    ((weylSylowEquiv Q split hW).symm (Q.simple i))
  apply mem_rootActor_of_two_power Q split i hn k
  exact congrArg (fun z : weylSylow Q => (z.val : X ⧸ Q.D)) hk

@[simp] theorem actorWeylSection_simple_square (hW : IsPGroup 2 (Weyl Q)) (i : Fin 2) :
    actorWeylSection Q split hW (Q.simple i)^2 = 1 := by
  rw [← map_pow,(Q.tits.involutions _ (Q.simple_mem i)).2,map_one]

theorem actorWeylSection_rotation (hW : IsPGroup 2 (Weyl Q)) :
    (actorWeylSection Q split hW (Q.simple 0) *
      actorWeylSection Q split hW (Q.simple 1))^rotationOrder Q = 1 := by
  rw [← map_mul,← map_pow]
  change actorWeylSection Q split hW ((Q.simple 0*Q.simple 1)^orderOf (Q.simple 0*Q.simple 1)) = 1
  rw [pow_orderOf_eq_one,map_one]

theorem weyl_isTwo_of_quadrangle (hm : rotationOrder Q = 4) : IsPGroup 2 (Weyl Q) := by
  apply IsPGroup.iff_card.mpr
  exact ⟨3,by rw [weyl_card,hm]; norm_num⟩

/-- The two actual rank-one actors generate exactly the Weyl-root span. -/
theorem rootActors_sup_eq_weylRootSpan :
    rootActor Q split 0 ⊔ rootActor Q split 1 = RootGeneration.weylRootSpan Q split := by
  let K := rootActor Q split 0 ⊔ rootActor Q split 1
  have hR (i : Fin 2) : rootActor Q split i ≤ K := by
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  apply le_antisymm
  · apply sup_le <;> apply sup_le
    · exact (simpleRoot_le Q split 0).trans (RootGeneration.unipotent_le_weylRootSpan Q split)
    · exact RootGeneration.conjugate_le_weylRootSpan Q split 0 _
    · exact (simpleRoot_le Q split 1).trans (RootGeneration.unipotent_le_weylRootSpan Q split)
    · exact RootGeneration.conjugate_le_weylRootSpan Q split 1 _
  · rw [RootGeneration.weylRootSpan_eq_iSup_weyl]
    apply iSup_le
    intro i
    apply iSup_le
    intro w
    obtain ⟨k,hk,hw⟩ := exists_weyl_lift_in Q
      (fun j => (actorReflection Q split j).val)
      (fun j => (actorReflection Q split j).class_eq) K
      (fun j => hR j (actorReflection Q split j).mem_rankOne) w
    rw [rightConjugate_eq_of_quotient_eq _ (torus_normalizes_simpleRoot Q split i)
      (representative w) k ((representative_spec w).trans hw.symm)]
    intro x hx
    have he := K.mul_mem (K.mul_mem (K.inv_mem hk) (hR i (mem_sup_left hx))) hk
    change (k : X ⧸ Q.D)⁻¹ * ((k : X ⧸ Q.D)*x*(k : X ⧸ Q.D)⁻¹) *
      (k : X ⧸ Q.D) ∈ K at he
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using he

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
