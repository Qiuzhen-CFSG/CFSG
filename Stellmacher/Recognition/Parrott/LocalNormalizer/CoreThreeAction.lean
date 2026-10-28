module

public import Stellmacher.Recognition.Parrott.NormalizerCoreThreeAction
public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.NormalizerCoreSolvable
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreOmegaQuotient
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreThreeCyclic
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreThreeFixed

/-!
# The actual second normalizer from local inputs

These calculations retain the supplied second elementary subgroup and Sylow.
The original derived-core normalizer identity and solvability of the actual
second normalizer replace the ambient N₂ assumption. All subgroup images,
centers, omega subgroups and conjugators are the original literal ones.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678. This is the local-input extension of `NormalizerCoreThreeAction`.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-! The three-center and cyclic-fixed-point conclusions are deliberately
packaged with the literal subgroup maps used by the preceding modules.  This
is the interface consumed by the normalizer-fusion assembly. -/
/-- Compatible Sylow-three witnesses in the actual second normalizer core. -/
public theorem exists_normalizer_three_action_package_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let X := K.map N.subtype
    let A := (Q : Subgroup N).map N.subtype
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    letI : U.Characteristic := omega₁_characteristic K
    let V := U.map K.subtype
    letI : V.Normal := ConjAct.normal_of_characteristic_of_normal
    ∃ t v b : G,
      t ∈ E ⊓ d.F ∧ v ∈ E ⊓ d.F ∧
      orderOf t = 2 ∧ orderOf v = 2 ∧
      t ∉ zpowers z ∧ v ∉ ZK ∧
      ZK = zpowers z ⊔ zpowers t ∧
      ZU = (zpowers z ⊔ zpowers t) ⊔ zpowers v ∧
      (∃ q : Q, ((q : N) : G) * z * ((q : N) : G)⁻¹ = t) ∧
      v ∈ centralizer (A : Set G) ∧
      ZU ⊓ centralizer (A : Set G) = zpowers v ∧
      d.F ⊓ centralizer (A : Set G) = zpowers v ∧
      ¬ IsConj z v ∧
      b ∈ X ∧ orderOf b = 4 ∧ b ^ 2 = v ∧
      X ⊓ centralizer (A : Set G) = zpowers b ∧
      IsCyclic (X ⊓ centralizer (A : Set G) : Subgroup G) ∧
      Nat.card (X ⊓ centralizer (A : Set G) : Subgroup G) = 4 ∧
      Nonempty ((N ⧸ V) ≃* Equiv.Perm (Fin 4)) := by
  intro H J E N K U X A ZK ZU V
  obtain ⟨t, v, ht, hv, ht2, hv2, htz, hvZ, hZK, hZU, hq, hvC,
      hZUfix, hFfix, hnc⟩ :=
    d.exists_normalizer_three_fixed_generators_of_local_inputs h hlocal hproper Q
  obtain ⟨b, hbX, hb4, hb2, hbC⟩ :=
    d.exists_normalizer_three_cyclic_generator_of_local_inputs h hlocal hproper Q v hv2 hFfix
  have hcyclic : IsCyclic (X ⊓ centralizer (A : Set G) : Subgroup G) := by
    rw [hbC]
    infer_instance
  have hcard : Nat.card (X ⊓ centralizer (A : Set G) : Subgroup G) = 4 := by
    rw [hbC, Nat.card_zpowers, hb4]
  have hquot := d.normalizer_omega_quotient_of_local_inputs h hlocal hproper
  exact ⟨t, v, b, ht, hv, ht2, hv2, htz, hvZ, hZK, hZU, hq, hvC,
    hZUfix, hFfix, hnc, hbX, hb4, hb2, hbC, hcyclic, hcard, hquot⟩

/-- A Sylow three-subgroup and compatible witnesses for all the local action
conclusions, without a Sylow subgroup supplied by the caller. -/
public theorem exists_normalizer_three_action_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    ∃ Q : Sylow 3 (normalizer (d.F : Set G)),
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let X := K.map N.subtype
    let A := (Q : Subgroup N).map N.subtype
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    letI : U.Characteristic := omega₁_characteristic K
    let V := U.map K.subtype
    letI : V.Normal := ConjAct.normal_of_characteristic_of_normal
    ∃ t v b : G,
      t ∈ E ⊓ d.F ∧ v ∈ E ⊓ d.F ∧
      orderOf t = 2 ∧ orderOf v = 2 ∧
      t ∉ zpowers z ∧ v ∉ ZK ∧
      ZK = zpowers z ⊔ zpowers t ∧
      ZU = (zpowers z ⊔ zpowers t) ⊔ zpowers v ∧
      (∃ q : Q, ((q : N) : G) * z * ((q : N) : G)⁻¹ = t) ∧
      v ∈ centralizer (A : Set G) ∧
      ZU ⊓ centralizer (A : Set G) = zpowers v ∧
      d.F ⊓ centralizer (A : Set G) = zpowers v ∧
      ¬ IsConj z v ∧
      b ∈ X ∧ orderOf b = 4 ∧ b ^ 2 = v ∧
      X ⊓ centralizer (A : Set G) = zpowers b ∧
      IsCyclic (X ⊓ centralizer (A : Set G) : Subgroup G) ∧
      Nat.card (X ⊓ centralizer (A : Set G) : Subgroup G) = 4 ∧
      Nonempty ((N ⧸ V) ≃* Equiv.Perm (Fin 4)) := by
  classical
  let Q : Sylow 3 (normalizer (d.F : Set G)) := Classical.choice inferInstance
  exact ⟨Q, d.exists_normalizer_three_action_package_of_local_inputs h hlocal hproper Q⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
