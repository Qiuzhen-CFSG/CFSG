module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.ResidualQuotients
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Elementary
public import Theory.Quasithin.EvenCharacteristic

/-!
# Original residual obstructions in the native linear-five local

A finite group with full two-core quotient SL₅(2) has order not divisible by
27. Consequently it contains no subgroup with a U₃(3) full-core quotient;
normality in the larger group is unnecessary. For a maximal two-local, the
SL₃(2) normal-residual obstruction instead excludes containment by forcing
equality with the larger two-local.

The native order-1024 elementary F already makes N(F) a genuine two-local.
The results for its conjugates take the precise full intrinsic quotient as an
explicit input. Construction of that quotient belongs to the native F producer;
no quotient or local shape is inferred from F's order.

Source: Kleidman--Wilson (1988), Lemma 1.1.1, p.485; An--O'Brien--Wilson
(2003), Section 4, p.122. The SL₅(2) order is 9,999,360. These source-specific
exits do not classify arbitrary radicals in this local.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals.LinearFiveLocal
attribute [local irreducible] modelGroup matrixA matrixB

/-- The binary core cannot add a factor of three to the linear-five quotient. -/
theorem not_dvd_card_of_linearFive_quotient
    {M : Type*} [Group M] [Finite M]
    (e : (M ⧸ pCore 2 M) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    ¬ 27 ∣ Nat.card M := by
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := M)).exists_card_eq
  have hc := Nat.card_congr e.toEquiv
  rw [Representation.SL5ExteriorSquare.card_specialLinearFive] at hc
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 M),hc,hk]
  have hcop : Nat.Coprime 27 (2 ^ k) := (by decide : Nat.Coprime 27 2).pow_right k
  rw [hcop.dvd_mul_right]
  decide

/-- Any marked unitary residual fails to embed, without a normality assumption. -/
theorem unitary_residual_not_embed_linearFive
    {B M : Type*} [Group B] [Group M] [Finite B] [Finite M]
    (b : (B ⧸ pCore 2 B) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (e : (M ⧸ pCore 2 M) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (f : B →* M) (hf : Function.Injective f) : False := by
  have hc : Nat.card (B ⧸ pCore 2 B) = 6048 :=
    (Nat.card_congr b.toEquiv).trans Atlas.G2.LieAutomorphismExtensions.card_binaryDerived
  have hd := card_quotient_dvd_card (pCore 2 B)
  rw [hc] at hd
  exact not_dvd_card_of_linearFive_quotient e
    ((by decide : 27 ∣ 6048).trans (hd.trans (card_dvd_of_injective f hf)))

/-- The subgroup version of the unitary order obstruction. -/
theorem unitary_residual_not_le_linearFive
    {G : Type*} [Group G] [Finite G] (B M : Subgroup G)
    (b : (B ⧸ pCore 2 B) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (e : (M ⧸ pCore 2 M) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    ¬ B ≤ M := fun h =>
  unitary_residual_not_embed_linearFive b e (inclusion h) (inclusion_injective h)

/-- Maximality among two-locals forces equality and the literal quotient contradiction. -/
theorem maximal_local_not_le_linearFive
    {G : Type*} [Group G] [Finite G] (N M : Subgroup G)
    (hN : IsMaximalTwoLocal N) (hM : IsTwoLocal M)
    (hq : ¬ Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))
    (e : (M ⧸ pCore 2 M) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    ¬ N ≤ M := by
  intro hle
  have he : N = M := le_antisymm hle (hN.2 hM hle)
  exact hq ⟨(QuotientGroup.congr _ _ (MulEquiv.subgroupCongr he)
    (pCore_map_iso 2 (MulEquiv.subgroupCongr he))).trans e⟩

/-- The constructed native F supplies a nontrivial binary normalizer witness. -/
theorem native_normalizer_isTwoLocal :
    IsTwoLocal (normalizer (LinearFive.F : Set Model)) := by
  have hne : LinearFive.F ≠ ⊥ := by
    intro h
    have hc := LinearFive.F_card
    rw [h,card_bot] at hc
    omega
  let := LinearFive.F_elementary
  exact ⟨LinearFive.F,hne,IsElementaryAbelian.isPGroup 2 _,rfl⟩

/-- Transport the producer's full intrinsic quotient to the literal conjugate local. -/
def nativeConjugateQuotientEquiv
    (e : ((normalizer (LinearFive.F : Set Model)) ⧸
      pCore 2 (normalizer (LinearFive.F : Set Model))) ≃*
        Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) (g : Model) :
    let M := (normalizer (LinearFive.F : Set Model)).map (MulAut.conj g).toMonoidHom
    M ⧸ pCore 2 M ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  (QuotientGroup.congr _ _ ((MulAut.conj g).subgroupMap _).symm
    (pCore_map_iso 2 ((MulAut.conj g).subgroupMap _).symm)).trans e

/-- Conditional on the native quotient, all conjugate linear-five placements are excluded. -/
theorem maximal_local_not_le_native_conjugate
    (N : Subgroup Model) (hN : IsMaximalTwoLocal N)
    (hq : ¬ Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))
    (e : ((normalizer (LinearFive.F : Set Model)) ⧸
      pCore 2 (normalizer (LinearFive.F : Set Model))) ≃*
        Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) (g : Model) :
    ¬ N ≤ (normalizer (LinearFive.F : Set Model)).map (MulAut.conj g).toMonoidHom :=
  maximal_local_not_le_linearFive N _ hN
    (Theory.Quasithin.isTwoLocal_map (MulAut.conj g) native_normalizer_isTwoLocal)
    hq (nativeConjugateQuotientEquiv e g)

end Janko4.LocalStructure.LargeCenterRadicals.LinearFiveLocal
