module

public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.Quotient
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.SextetSeed
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.SextetComplement

/-!
# Six-point cubic normalizers in the native Mathieu group

For every native subgroup D of order three fixing six points, its normalizer
complements the intrinsic two-core of a genuine sextet stabilizer. The sextet
is conjugate to the standard sextet by an actual native permutation. The proof
transports the representative complement, its stabilizer and its two-core by
the same conjugation. Normality is recorded inside that stabilizer.

The re-exported quotient isomorphism identifies N(D)/D with the full symmetric
group on the literal fixed-point set; its quotient-map formula identifies the
action with restriction of the native permutation. The representative's class
is characterized by subgroup order three and exactly six common fixed points.
This is the structural class called 3A in the source's Modular Atlas convention
(p.396). It uses the shared historical `m24Element3B`, whereas the shared
`m24Element3A` is fixed-point-free; neither declaration is renamed.

Source: Aschbacher–Smith H.15.7(1–2), printed pp.401–402, combined manuscript
of 1 March 2004. This module supplies its cubic group geometry; the cocode
module and fixed-line assertions belong to the surrounding source assembly.
-/

public section

namespace MathieuCode.SixPoint
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open SextetComplement
open scoped Pointwise

/-- Every six-fixed-point cubic has a normalizer complement in a genuine sextet
stabilizer, with an actual native conjugator to the standard sextet. -/
theorem normalizer_sextet_complement (D : Subgroup M24)
    (hD : Nat.card D = 3) (hfix : Nat.card (FixedPoint D) = 6) :
    ∃ S : Sextet,
      let N := Subgroup.normalizer (D : Set M24)
      let H := sextetStabilizer S
      let K := (pCore 2 H).map H.subtype
      N ≤ H ∧ K ⊓ N = ⊥ ∧ K ⊔ N = H ∧
        ∃ g : M24, g.val • S.parts = standardSextet.parts := by
  obtain ⟨g, hg⟩ := cubicSubgroup_conjugacy D hD hfix
  have hg' : cubicSubgroup.map (MulAut.conj g⁻¹).toMonoidHom = D := by
    rw [← hg, Subgroup.map_map]
    have hh : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id M24 := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hh, Subgroup.map_id]
  obtain ⟨S, hN, hi, hs, t, ht⟩ := cubicNormalizer_sextet_complement
  change (sextetStabilizer S).pCoreIn 2 ⊓
    Subgroup.normalizer (cubicSubgroup : Set M24) = ⊥ at hi
  change (sextetStabilizer S).pCoreIn 2 ⊔
    Subgroup.normalizer (cubicSubgroup : Set M24) = sextetStabilizer S at hs
  refine ⟨translateSextet g⁻¹ S, ?_⟩
  dsimp only
  have hn := cubicSubgroup.map_equiv_normalizer_eq (MulAut.conj g⁻¹)
  rw [hg'] at hn
  have hk := Subgroup.map_pCoreIn_of_injective 2
    (sextetStabilizer S) (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  rw [← translateSextet_stabilizer] at hk
  change _ ≤ _ ∧ (sextetStabilizer _).pCoreIn 2 ⊓ _ = ⊥ ∧
    (sextetStabilizer _).pCoreIn 2 ⊔ _ = _ ∧ _
  rw [← hk, ← hn, ← Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
    hi, Subgroup.map_bot, ← Subgroup.map_sup, hs, translateSextet_stabilizer]
  refine ⟨Subgroup.map_mono hN, rfl, rfl, t * g, ?_⟩
  change (t * g) • (g⁻¹ • S.parts) = standardSextet.parts
  rw [mul_smul, smul_inv_smul]
  exact ht

/-- The intrinsic two-core is normal relative to the sextet stabilizer containing
the normalizer complement. -/
theorem normalizer_sextet_complement_normal (D : Subgroup M24)
    (hD : Nat.card D = 3) (hfix : Nat.card (FixedPoint D) = 6) :
    ∃ S : Sextet,
      let N := Subgroup.normalizer (D : Set M24)
      let H := sextetStabilizer S
      let K := (pCore 2 H).map H.subtype
      N ≤ H ∧ (K.subgroupOf H).Normal ∧ K ⊓ N = ⊥ ∧ K ⊔ N = H ∧
        ∃ g : M24, g.val • S.parts = standardSextet.parts := by
  obtain ⟨S, hN, hi, hs, hg⟩ := normalizer_sextet_complement D hD hfix
  refine ⟨S, hN, ?_, hi, hs, hg⟩
  change (((pCore 2 (sextetStabilizer S)).map (sextetStabilizer S).subtype).comap
    (sextetStabilizer S).subtype).Normal
  rw [Subgroup.comap_map_eq_self_of_injective (sextetStabilizer S).subtype_injective]
  infer_instance

/-- A structural characterization of the source's six-fixed-point cubic class,
independent of the shared historical 3A/3B names. -/
theorem cubicSubgroup_conjugacy_iff (D : Subgroup M24) :
    (∃ g : M24, D.map (MulAut.conj g).toMonoidHom = cubicSubgroup) ↔
      Nat.card D = 3 ∧ Nat.card (FixedPoint D) = 6 := by
  constructor
  · rintro ⟨g, hg⟩
    constructor
    · rw [← Subgroup.card_map_of_injective (K := D)
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
        hg, cubicSubgroup_card]
    · have hf := congrArg Set.ncard (fixedPoints_conjugate D g)
      rw [hg, Set.ncard_smul_set] at hf
      change Nat.card (MulAction.fixedPoints D (Fin 24)) = 6
      rw [Nat.card_coe_set_eq, hf, ← Nat.card_coe_set_eq]
      exact cubicSubgroup_fixed_card
  · rintro ⟨hD, hfix⟩
    exact cubicSubgroup_conjugacy D hD hfix

/-- The historically named `m24Element3A` generates a fixed-point-free subgroup;
its shared name therefore does not identify the six-point class used by the source. -/
theorem historical3A_subgroup_fixed_card :
    Nat.card (FixedPoint (Subgroup.zpowers (⟨m24Element3A, m24Element3A_mem⟩ : M24))) = 0 := by
  classical
  let e : FixedPoint (Subgroup.zpowers (⟨m24Element3A, m24Element3A_mem⟩ : M24)) ≃
      {i : Fin 24 // i ∈ m24Element3A.supportᶜ} :=
    Equiv.subtypeEquivRight fun i => by
      rw [mem_fixedPoint_zpowers_iff]
      simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
      rfl
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_compl, Fintype.card_fin, m24Element3A_fixed_card]

end MathieuCode.SixPoint
