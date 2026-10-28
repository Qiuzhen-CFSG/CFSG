module

public import Theory.GroupTheory.CentralBinaryCommutatorDuality
public import Theory.Representation.BinaryConjugationSection
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Central commutator duality on ambient binary sections

Let H normalize Q and U, with U finite elementary abelian, and let [Q,U]
lie in an order-two subgroup Z ≤ Q centralized by H. The commutator pairing
constructs the literal sections U/C_U(Q) and Q/C_Q(U), with the latter
carried by the linear dual of the former. Both coordinate maps are onto;
their kernels are the actual relative centralizers. No nonzero pairing,
equal-order assumption or surjectivity input is required.

We use the proved finite binary pairing duality after removing both radicals.
Conjugation on the first quotient gives its representation. Simultaneous
invariance of the pairing gives the inverse-actor formula on the second.
Working with ambient subgroups preserves all original inclusion and quotient
maps, without identifying nested subgroup carriers.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), F.9.7, printed p.321; application 14.5.21(1), p.1019.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement
noncomputable section
namespace Representation.BinaryConjugationSection

private def binaryAction {D A : Type*} [Group D] [Group A]
    [IsElementaryAbelian 2 A] (α : D →* MulAut A) :
    Representation (ZMod 2) D (Additive A) where
  toFun a := (α a).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext v
    change α 1 v.toMul = v.toMul
    rw [map_one]
    rfl
  map_mul' a b := by
    ext v
    change α (a * b) v.toMul = α a (α b v.toMul)
    rw [map_mul]
    rfl

private theorem pairing_sections
    {G : Type*} [Group G] (H Q U : Subgroup G) [Finite U]
    [IsElementaryAbelian 2 U]
    (hQH : Q ≤ H) (hUH : U ≤ H)
    (hNQ : H ≤ normalizer Q) (hNU : H ≤ normalizer U)
    (f : Q →* (U →* Multiplicative (ZMod 2)))
    (hf : ∀ (q : Q) (u : U), f q u = 1 ↔ ⁅(q : G), (u : G)⁆ = 1)
    (hinv : ∀ (h : H) (q : Q) (u : U),
      f ⟨h * q * (h : G)⁻¹, (mem_normalizer_iff.mp (hNQ h.property) q).mp q.property⟩
        ⟨h * u * (h : G)⁻¹, (mem_normalizer_iff.mp (hNU h.property) u).mp u.property⟩ =
          f q u) :
    ∃ (ρ : Representation (ZMod 2) H
        (Additive (U ⧸ (U ⊓ centralizer (Q : Set G)).subgroupOf U)))
      (sU : BinaryConjugationSection H U (U ⊓ centralizer (Q : Set G)) ρ)
      (sQ : BinaryConjugationSection H Q (Q ⊓ centralizer (U : Set G)) ρ.dual),
      (∀ (q : Q) (u : U),
        (sQ.coordinates q).toAdd (sU.coordinates u).toAdd = 0 ↔
          ⁅(q : G), (u : G)⁆ = 1) ∧
      (∀ u : U, (sU.coordinates u).toAdd = Additive.ofMul
        (QuotientGroup.mk' ((U ⊓ centralizer (Q : Set G)).subgroupOf U) u)) := by
  let E := U ⊓ centralizer (Q : Set G)
  let A := U ⧸ E.subgroupOf U
  have hkU : f.flip.ker = E.subgroupOf U := by
    ext u
    change f.flip u = 1 ↔ (u : G) ∈ E
    constructor
    · intro he
      refine ⟨u.property, ?_⟩
      intro q hq
      exact (commutatorElement_eq_one_iff_mul_comm.mp ((hf ⟨q, hq⟩ u).mp
        (congrArg (fun k : Q →* Multiplicative (ZMod 2) => k ⟨q, hq⟩) he)))
    · intro hu
      ext q
      exact (hf q u).mpr (commutatorElement_eq_one_iff_mul_comm.mpr (hu.2 q q.property))
  have hkQ : f.ker = (Q ⊓ centralizer (U : Set G)).subgroupOf Q := by
    ext q
    change f q = 1 ↔ (q : G) ∈ Q ⊓ centralizer (U : Set G)
    constructor
    · intro he
      refine ⟨q.property, ?_⟩
      intro u hu
      exact (commutatorElement_eq_one_iff_mul_comm.mp ((hf q ⟨u, hu⟩).mp
        (congrArg (fun k : U →* Multiplicative (ZMod 2) => k ⟨u, hu⟩) he))).symm
    · intro hq
      ext u
      exact (hf q u).mpr
        (commutatorElement_eq_one_iff_mul_comm.mpr (hq.2 u u.property).symm)
  have hNE : H ≤ normalizer E :=
    (le_inf hNU (hNQ.trans (normalizer_le_normalizer_centralizer Q))).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨α, hα⟩ := exists_quotient_conjugation_action H U E hNU hNE inferInstance
  let ρ := binaryAction α
  let cU : U →* Multiplicative (Additive A) := {
    toFun u := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' (E.subgroupOf U) u))
    map_one' := (QuotientGroup.mk' _).map_one
    map_mul' := (QuotientGroup.mk' _).map_mul }
  let sU : BinaryConjugationSection H U E ρ := {
    section_le := hUH
    kernel_le := inf_le_left
    normalized := hNU
    coordinates := cU
    onto := QuotientGroup.mk'_surjective _
    kernel_eq := QuotientGroup.ker_mk' _
    equivariant := fun h u => (hα h u).symm }
  obtain ⟨e, he⟩ := MonoidHom.exists_binary_pairing_quotient_duality f.flip
  let t := QuotientGroup.quotientMulEquivOfEq hkU.symm
  let transport : ((U ⧸ f.flip.ker) →* Multiplicative (ZMod 2)) ≃*
      (A →* Multiplicative (ZMod 2)) := {
    toFun k := k.comp t.toMonoidHom
    invFun k := k.comp t.symm.toMonoidHom
    left_inv k := by ext u; simp
    right_inv k := by ext u; simp
    map_mul' _ _ := rfl }
  let e' : (Q ⧸ f.ker) ≃* Multiplicative (Module.Dual (ZMod 2) (Additive A)) := e.trans (transport.trans MonoidHom.binaryCharacterEquivLinearDual)
  let cQ := e'.toMonoidHom.comp (QuotientGroup.mk' f.ker)
  have heval (q : Q) (u : U) :
      (cQ q).toAdd (cU u).toAdd = (f q u).toAdd :=
    congrArg Multiplicative.toAdd (he u q)
  have hceq (h : H) (q : Q) :
      (cQ ⟨h * q * (h : G)⁻¹,
        (mem_normalizer_iff.mp (hNQ h.property) q).mp q.property⟩).toAdd =
      ρ.dual h (cQ q).toAdd := by
    ext a
    obtain ⟨u, rfl⟩ := sU.onto (Multiplicative.ofAdd a)
    change (cQ _).toAdd (cU u).toAdd = (cQ q).toAdd (ρ h⁻¹ (cU u).toAdd)
    rw [← sU.equivariant h⁻¹ u]
    change (cQ _).toAdd (cU u).toAdd = (cQ q).toAdd (cU _).toAdd
    rw [heval, heval]
    apply congrArg Multiplicative.toAdd
    let v : U := ⟨(h⁻¹ : H) * u * ((h⁻¹ : H) : G)⁻¹,
      (mem_normalizer_iff.mp (hNU h⁻¹.property) u).mp u.property⟩
    have hv : (⟨h * v * (h : G)⁻¹,
        (mem_normalizer_iff.mp (hNU h.property) v).mp v.property⟩ : U) = u := by
      apply Subtype.ext
      simp [v, mul_assoc]
    simpa only [hv] using hinv h q v
  let sQ : BinaryConjugationSection H Q (Q ⊓ centralizer (U : Set G)) ρ.dual := {
    section_le := hQH
    kernel_le := inf_le_left
    normalized := hNQ
    coordinates := cQ
    onto := e'.surjective.comp (QuotientGroup.mk'_surjective _)
    kernel_eq := by
      ext q
      change e' (QuotientGroup.mk' f.ker q) = 1 ↔ _
      rw [← e'.map_one, e'.injective.eq_iff]
      change q ∈ (QuotientGroup.mk' f.ker).ker ↔ _
      rw [QuotientGroup.ker_mk', hkQ]
    equivariant := hceq }
  refine ⟨ρ, sU, sQ, ?_, fun _ => rfl⟩
  intro q u
  change (cQ q).toAdd (cU u).toAdd = 0 ↔ _
  rw [heval]
  exact hf q u

end Representation.BinaryConjugationSection

namespace Representation.BinaryConjugationSection

/-- Central binary commutators construct the two literal radical sections,
with the contragredient action on the second section. -/
public theorem exists_central_duality
    {G : Type*} [Group G] (H Q U Z : Subgroup G) [Finite U]
    [IsElementaryAbelian 2 U]
    (hQH : Q ≤ H) (hUH : U ≤ H)
    (hNQ : H ≤ normalizer Q) (hNU : H ≤ normalizer U)
    (hZQ : Z ≤ Q) (hZ : Z ≤ centralizer (H : Set G))
    (hcomm : ⁅Q, U⁆ ≤ Z) (hcard : Nat.card Z = 2) :
    ∃ (ρ : Representation (ZMod 2) H
        (Additive (U ⧸ (U ⊓ centralizer (Q : Set G)).subgroupOf U)))
      (sU : BinaryConjugationSection H U (U ⊓ centralizer (Q : Set G)) ρ)
      (sQ : BinaryConjugationSection H Q (Q ⊓ centralizer (U : Set G)) ρ.dual),
      (∀ (q : Q) (u : U),
        (sQ.coordinates q).toAdd (sU.coordinates u).toAdd = 0 ↔
          ⁅(q : G), (u : G)⁆ = 1) ∧
      (∀ u : U, (sU.coordinates u).toAdd = Additive.ofMul
        (QuotientGroup.mk' ((U ⊓ centralizer (Q : Set G)).subgroupOf U) u)) := by
  let eZ : Z ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hcard (by simp)
  have hbot : (⊥ : Subgroup G).subgroupOf Z = (⊥ : Subgroup Z) := by ext z; simp
  let : ((⊥ : Subgroup G).subgroupOf Z).Normal := hbot.symm ▸ inferInstance
  let e0 : (Z ⧸ (⊥ : Subgroup G).subgroupOf Z) ≃* Z :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let : IsMulCommutative (Z ⧸ (⊥ : Subgroup G).subgroupOf Z) :=
    ⟨⟨fun a b => (e0.trans eZ).injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  have hQZ : Q ≤ centralizer (Z : Set G) :=
    le_centralizer_iff.mp (hZ.trans (centralizer_le hQH))
  have hZU : ⁅Z, U⁆ ≤ ⊥ := by
    rw [le_bot_iff, commutator_eq_bot_iff_le_centralizer]
    exact hZ.trans (centralizer_le hUH)
  let f : Q →* (U →* Multiplicative (ZMod 2)) :=
    (centralQuotientCommutatorPairing Q U Z ⊥ hZQ hQZ hcomm hZU).compr₂
      (e0.trans eZ).toMonoidHom
  have hf (q : Q) (u : U) : f q u =
      eZ ⟨⁅(q : G), (u : G)⁆,
        hcomm (commutator_mem_commutator q.property u.property)⟩ := by
    dsimp only [f]
    rw [MonoidHom.compr₂_apply, centralQuotientCommutatorPairing_apply]
    rfl
  apply pairing_sections H Q U hQH hUH hNQ hNU f
  · intro q u
    rw [hf, ← eZ.map_one, eZ.injective.eq_iff, Subtype.ext_iff]
    rfl
  · intro h q u
    rw [hf, hf]
    congr 1
    apply Subtype.ext
    change ⁅(h : G) * q * (h : G)⁻¹, (h : G) * u * (h : G)⁻¹⁆ = ⁅(q : G), (u : G)⁆
    rw [← conjugate_commutatorElement,
      hZ (hcomm (commutator_mem_commutator q.property u.property)) h h.property,
      mul_inv_cancel_right]

end Representation.BinaryConjugationSection
