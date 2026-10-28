module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PlaneMotion
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.PrimeOrderClosure
/-!
# Lifting section-point three-rank to the original plane centralizer

A cubic that fixes a point modulo a fixed binary subspace fixes its lift.
Apply this first to the K-fixed kernel of the component section and then
to the original line V₁. A nonzero section image ensures V₂ is generated
by V₁ and the chosen vector. Thus every cubic in the section stabilizer
centralizes V₂. Cubic closure preserves three-rank, giving the literal
rank comparison with C_G(V₂), without a splitting assumption.

Source: Aschbacher–Smith, proof of13.7.6, printed p.939, step(iii).
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion NaturalAction
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
private theorem cubic_linear {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) A E) (a : A) (ha : a ^ 3 = 1) (v : E)
    (hc : ρ a (ρ a v - v) = ρ a v - v) : ρ a v = v := by
  have htwo : ρ a (ρ a v) = v := by
    rw [map_sub, ZModModule.sub_eq_add, ZModModule.sub_eq_add,
      add_comm (ρ a v) v] at hc
    exact add_right_cancel hc
  have hthree : ρ a (ρ a (ρ a v)) = v := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    rw [show a * a * a = a ^ 3 by simp [pow_succ], ha, map_one, Module.End.one_apply]
  simpa only [htwo] using hthree

private theorem cubic_group {D : Type*} [Group D] (a v : D) (ha : a ^ 3 = 1)
    (hc : a * (a * v * a⁻¹ * v⁻¹) * a⁻¹ = a * v * a⁻¹ * v⁻¹)
    (ht : (a * v * a⁻¹ * v⁻¹) ^ 2 = 1) : a * v * a⁻¹ = v := by
  let f : MulAut D := MulAut.conj a
  let c := a * v * a⁻¹ * v⁻¹
  have hcv : f v = c * v := by dsimp [f,c]; group
  have hfc : f c = c := hc
  have htwo : f (f v) = v := by
    rw [hcv, map_mul, hfc, hcv, ← mul_assoc, ← pow_two, ht, one_mul]
  have hthree : f (f (f v)) = v := by
    change a * (a * (a * v * a⁻¹) * a⁻¹) * a⁻¹ = v
    calc
      _ = a ^ 3 * v * (a ^ 3)⁻¹ := by simp only [pow_succ, pow_zero, one_mul, mul_inv_rev]; group
      _ = v := by rw [ha]; simp
  change f v = v
  simpa only [htwo] using hthree

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

private theorem plane_eq_join (v : V₂) (hv : (v : G) ∉ V₁) :
    V₂ = V₁ ⊔ zpowers (v : G) := by
  let := elementary d
  have hvV := d.plane_le_seed.trans d.seed_le v.property
  have hnorm : (v : G) ∈ normalizer (V₁ : Set G) :=
    (Subgroup.centralizer_le_normalizer _) ((V.le_centralizer.trans
      (centralizer_le (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)))) hvV)
  have hc := card_sup_zpowers_of_normalizing_involution V₁ (v : G)
    (elemPow_eq_one_of_isElementaryAbelian _ hvV) hv hnorm
  apply Eq.symm
  apply eq_of_le_of_card_ge (sup_le d.line_le_plane (zpowers_le.mpr v.property))
  rw [hc, d.line_card, d.plane_card]

variable [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]

private theorem cubic_section_fixes_plane
    (hHN : H ≤ normalizer (V₁ : Set G)) (hKH : K ≤ H)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (v : V₂) (hu : seedVector H V₃ V₁ ⟨v, d.plane_le_seed v.property⟩ ∈
      commutatorImage H V₃ V₁ K)
    (hn : (Submodule.Quotient.mk ⟨_, hu⟩ : ComponentSection H V₃ V₁ ρ K) ≠ 0)
    (hs : ∀ (k : K) (u : commutatorImage H V₃ V₁ K),
      ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) u ∈ commutatorImage H V₃ V₁ K)
    (k : K) (hk : k ^ 3 = 1)
    (he : (Submodule.Quotient.mk
      ⟨ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k))
        (seedVector H V₃ V₁ ⟨v, d.plane_le_seed v.property⟩), hs k ⟨_, hu⟩⟩ :
          ComponentSection H V₃ V₁ ρ K) = Submodule.Quotient.mk ⟨_, hu⟩) :
    (k : G) ∈ centralizer (V₂ : Set G) := by
  let u : commutatorImage H V₃ V₁ K := ⟨_, hu⟩
  let a := QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)
  have ha : a ^ 3 = 1 := by simp only [a, ← map_pow, hk, map_one]
  have hd := (Submodule.Quotient.eq (fixedInCommutator H V₃ V₁ ρ K)).mp he
  change ρ a u.val - u.val ∈ fixedSpace ρ (Section08.Source.starImage H K) at hd
  have hc := hd ⟨a, ⟨inclusion hKH k, k.property, rfl⟩⟩
  change ρ a (ρ a u.val - u.val) = ρ a u.val - u.val at hc
  have hfix := cubic_linear ρ a ha u.val hc
  let w : Section08.Source.UH H V₃ := ⟨v, le_conjugateSpanBy V₃ H (d.plane_le_seed v.property)⟩
  let w' : Section08.Source.UH H V₃ :=
    ⟨(k : G) * (v : G) * (k : G)⁻¹,
      le_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ H)
        k (hKH k.property) v w.property⟩
  have hq : vector H V₃ V₁ w' = vector H V₃ V₁ w :=
    (hρ (inclusion hKH k) w).symm.trans hfix
  let q := QuotientGroup.mk' (V₁.subgroupOf (Section08.Source.UH H V₃))
  have hq' : q w' = q w := congrArg Additive.toMul hq
  have hcmem : (w' * w⁻¹ : Section08.Source.UH H V₃).val ∈ V₁ := by
    change w' * w⁻¹ ∈ V₁.subgroupOf (Section08.Source.UH H V₃)
    apply (QuotientGroup.eq_one_iff (N := V₁.subgroupOf (Section08.Source.UH H V₃)) _).mp
    change q (w' * w⁻¹) = 1
    rw [map_mul, map_inv, hq', mul_inv_cancel]
  change (k : G) * (v : G) * (k : G)⁻¹ * (v : G)⁻¹ ∈ V₁ at hcmem
  have hkc : (k : G) ∈ centralizer (V₁ : Set G) :=
    normalizer_le_centralizer_of_card_two V₁ d.line_card (hHN (hKH k.property))
  let := elementary d
  have hc2 : ((k : G) * (v : G) * (k : G)⁻¹ * (v : G)⁻¹) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian _
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le) hcmem)
  have hcc : (k : G) * ((k : G) * (v : G) * (k : G)⁻¹ * (v : G)⁻¹) * (k : G)⁻¹ =
      (k : G) * (v : G) * (k : G)⁻¹ * (v : G)⁻¹ := by
    rw [← mem_centralizer_iff.mp hkc _ hcmem, mul_inv_cancel_right]
  have hkv := cubic_group (k : G) (v : G) (congrArg Subtype.val hk) hcc hc2
  have hv : (v : G) ∉ V₁ := by
    intro hv
    have hw : vector H V₃ V₁ w = 0 :=
      (QuotientGroup.eq_one_iff (N := V₁.subgroupOf (Section08.Source.UH H V₃)) w).mpr hv
    have hu0 : u = 0 := Subtype.ext hw
    apply hn
    change (Submodule.Quotient.mk u : ComponentSection H V₃ V₁ ρ K) = 0
    rw [hu0, Submodule.Quotient.mk_zero]
  have hle : V₂ ≤ centralizer ({(k : G)} : Set G) := by
    rw [plane_eq_join d v hv]
    apply sup_le
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hkc x hx)
    · apply zpowers_le.mpr
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hkv).symm
  exact mem_centralizer_iff.mpr (fun x hx => mem_centralizer_singleton_iff.mp (hle hx))

/-- The actual section-point stabilizer has no larger three-rank than the
centralizer of the original plane. Both central kernels are removed by cubics. -/
theorem section_point_rank_le_plane_centralizer
    (hHN : H ≤ normalizer (V₁ : Set G)) (hKH : K ≤ H)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (v : V₂) (hu : seedVector H V₃ V₁ ⟨v, d.plane_le_seed v.property⟩ ∈
      commutatorImage H V₃ V₁ K)
    (hn : (Submodule.Quotient.mk ⟨_, hu⟩ : ComponentSection H V₃ V₁ ρ K) ≠ 0)
    (hs : ∀ (k : K) (u : commutatorImage H V₃ V₁ K),
      ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) u ∈ commutatorImage H V₃ V₁ K)
    (P : Subgroup K)
    (hP : ∀ k ∈ P, (Submodule.Quotient.mk
      ⟨ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k))
        (seedVector H V₃ V₁ ⟨v, d.plane_le_seed v.property⟩), hs k ⟨_, hu⟩⟩ :
          ComponentSection H V₃ V₁ ρ K) = Submodule.Quotient.mk ⟨_, hu⟩) :
    primeRank 3 P ≤ primeRank 3 (centralizer (V₂ : Set G)) := by
  let C : Subgroup K := closure {k | k ∈ P ∧ orderOf k = 3}
  have hC : C ≤ (centralizer (V₂ : Set G)).comap K.subtype := by
    apply (closure_le _).mpr
    intro k hk
    exact cubic_section_fixes_plane d hHN hKH ρ hρ v hu hn hs k
      (hk.2 ▸ pow_orderOf_eq_one k) (hP k hk.1)
  rw [← primeRank_primeOrderClosure 3 P]
  exact (primeRank_congr 3 (C.equivMapOfInjective K.subtype K.subtype_injective)).le.trans
    (primeRank_mono 3 (map_le_iff_le_comap.mpr hC))

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
