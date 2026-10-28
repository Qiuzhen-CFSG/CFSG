module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.LinearCartanExclusion
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorFactorSection

/-!
# The original opposite Cartan excludes the linear tensor model

The literal second tensor factor centralizes the original component modulo
its two-core. The degree-three local-A₅ calculation turns this into
centralization of the old component's quotient, without a model-centralizing
premise. Its normalizer orbit then contains the full original Cartan, whose
order-three subgroup lies in the old component, giving the contradiction.

The original model map, its local marking and restricted kernels, and the
actual Cartan and orbit marking remain explicit source data. This is the
linear terminal implication of 9.3.8, not an unconditional tensor exclusion.
Source: Aschbacher–Smith, printed p.734.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 Chapter4 ChapterA.Section03
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The original opposite Cartan factor centralizes the old component's
two-core quotient in either degree-three action row. -/
theorem linear_opposite_factor_centralizes_old_section
    (hF : Nat.card F = 4)
    (I K E : Subgroup G) (hLI : L ≤ I) (hKI : K ≤ I) (hEI : E ≤ I)
    (f : I →* SL(3,F)) (S : Sylow 2 SL(3,F))
    (hL : (L.subgroupOf I).map f ∈ localCComponents S)
    (hproper : (L.subgroupOf I).map f ≠ ⊤)
    (hkL : IsPGroup 2 (f.subgroupMap (L.subgroupOf I)).ker)
    (hE : E ≤ localOrbit T L)
    (hfirst : ∀ (x : G) (hx : x ∈ E), (m.quotient ⟨x,hE hx⟩).1 = 1)
    (hEK : E ≤ normalizer (K : Set G))
    (hkK : IsPGroup 2 (f.subgroupMap (K.subgroupOf I)).ker)
    (h3 : ∀ x ∈ E, x ^ 3 = 1) : E ≤ sectionCentralizer K :=
  source_tensor_linear_original_chosen_factor hF I L K E hLI hKI hEI f S
    hL hproper e hkL (m.opposite_factor_le_sectionCentralizer E hE hfirst) hEK hkK h3

/-- The same original Cartan orbit excludes SL₃(4), for both the single
and repeated natural-module rows. No section-centralization premise remains. -/
theorem false_of_linear_opposite_cartan
    (hF : Nat.card F = 4)
    (I K A E N B : Subgroup G) (hLI : L ≤ I) (hKI : K ≤ I) (hEI : E ≤ I)
    (f : I →* SL(3,F)) (S : Sylow 2 SL(3,F))
    (hL : (L.subgroupOf I).map f ∈ localCComponents S)
    (hproper : (L.subgroupOf I).map f ≠ ⊤)
    (hkL : IsPGroup 2 (f.subgroupMap (L.subgroupOf I)).ker)
    (hE : E ≤ localOrbit T L)
    (hfirst : ∀ (x : G) (hx : x ∈ E), (m.quotient ⟨x,hE hx⟩).1 = 1)
    (hEK : E ≤ normalizer (K : Set G))
    (hkK : IsPGroup 2 (f.subgroupMap (K.subgroupOf I)).ker)
    (h3 : ∀ x ∈ E, x ^ 3 = 1)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hNK : N ≤ normalizer (K : Set G)) (hgen : componentOrbit E N = A)
    (hBA : B ≤ A) (hBK : B ≤ K) (hB : Nat.card B = 3) : False := by
  have hBne : B ≠ ⊥ := by
    intro he
    rw [he,Subgroup.card_bot] at hB
    omega
  obtain ⟨b,hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hb3 : orderOf b = 3 := by
    exact ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp
      (hB ▸ orderOf_dvd_natCard b)).resolve_left (fun h => hb (orderOf_eq_one_iff.mp h))
  exact source_tensor_torus_cubic_contradiction K A E N eK hNK
    (m.linear_opposite_factor_centralizes_old_section hF I K E hLI hKI hEI
      f S hL hproper hkL hE hfirst hEK hkK h3)
    hgen b (hBA b.property) (hBK b.property)
    ((Subgroup.orderOf_coe b).trans hb3)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
