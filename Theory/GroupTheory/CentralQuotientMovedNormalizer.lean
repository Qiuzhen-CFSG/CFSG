module
public import Theory.GroupTheory.PerfectNormalizerLift
public import Theory.GroupTheory.PerfectSmallNormalizer
public import Theory.GroupTheory.PerfectSolvableSectionLift
public import Theory.GroupTheory.PCoreInRestriction
public import Mathlib.GroupTheory.Sylow

/-!
# Moving sections and normalizers through central quotients

A subgroup E=[E,B] is recovered from its image under a central quotient
once B is normalized: central errors disappear from commutators. Thus
normalization and trivial action on the B-core quotient transport the
original rigidity on E to its literal image. Restriction to an overgroup
preserves the same assertion.

For a normalizing p-subgroup Q, a Sylow index bounds the relative index
inside Q even when Q is not contained in the chosen Sylow. The join with
the Sylow intersection is a p-group; its order supplies the comparison.

Source application: Aschbacher--Smith, proof of 12.6.12, printed
pp.825--826, using the literal L_v and V_v central-quotient images.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G F : Type*} [Group G] [Group F] [Finite G]

/-- Central discrepancies do not affect a fully moved section once its actor is normalized. -/
theorem mem_normalizer_moved_of_central_image
    (f : G →* F) (hk : f.ker ≤ center G) (B E : Subgroup G)
    (hm : ⁅E,B⁆ = E) {r : G}
    (hrB : r ∈ normalizer (B : Set G))
    (hrE : f r ∈ normalizer (E.map f : Set F)) : r ∈ normalizer (E : Set G) := by
  let a := (MulAut.conj r).toMonoidHom
  have hB : B.map a = B := mem_normalizer_iff_map_conj_eq.mp hrB
  have hmove : ⁅E.map a,B⁆ = E.map a := by
    rw [←hB,←map_commutator,hm]
  have hle : E.map a ≤ E := by
    rw [←hmove]
    apply commutator_le.mpr
    intro x hx b hb
    have hfx : f x ∈ E.map f := by
      obtain ⟨y,hy,rfl⟩ := hx
      have hh := (mem_normalizer_iff.mp hrE (f y)).mp (mem_map_of_mem f hy)
      change f (r*y*r⁻¹) ∈ E.map f
      simpa only [map_mul,map_inv] using hh
    obtain ⟨w,hw,he⟩ := hfx
    have hz : x*w⁻¹ ∈ center G := hk (by
      rw [MonoidHom.mem_ker,map_mul,map_inv,he,mul_inv_cancel])
    have hc (g : G) : Commute (x*w⁻¹) g := (mem_center_iff.mp hz g).symm
    have hcomm : ⁅x,b⁆ = ⁅w,b⁆ := by
      calc
        ⁅x,b⁆ = ⁅(x*w⁻¹)*w,b⁆ := by rw [inv_mul_cancel_right]
        _ = ⁅w,b⁆ := by
          rw [commutatorElement_mul_left_eq_conj_mul,(hc b).commutator_eq,
            mul_one,(hc ⁅w,b⁆).eq,mul_inv_cancel_right]
    rw [hcomm]
    exact hm ▸ commutator_mem_commutator hw hb
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj r).injective])

/-- A normalizing Sylow intersection controls the relative index in any normalized p-subgroup. -/
theorem relIndex_pGroup_le_sylow_of_normalizes
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (N Q : Subgroup G)
    (hQ : IsPGroup p Q) (hNQ : N ≤ normalizer (Q : Set G)) :
    N.relIndex Q ≤ N.relIndex (P : Subgroup G) := by
  let A := (P : Subgroup G) ⊓ N
  have hA : IsPGroup p A := P.isPGroup'.to_le inf_le_left
  have hn : A ≤ normalizer (Q : Set G) := inf_le_right.trans hNQ
  have hp := hQ.to_sup_of_normal_left' hA hn
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have hcard : Nat.card (Q ⊔ A : Subgroup G) ≤ Nat.card P :=
    (card_le_of_le hS).trans_eq (Nat.card_congr (S.equiv P).toEquiv)
  have h1 := relIndex_mul_relIndex (⊥ : Subgroup G) A (Q ⊔ A) bot_le le_sup_right
  have h2 := relIndex_mul_relIndex (⊥ : Subgroup G) A (P : Subgroup G) bot_le inf_le_left
  simp only [relIndex_bot_left] at h1 h2
  have hb : A.relIndex Q ≤ A.relIndex (P : Subgroup G) := by
    rw [←relIndex_sup_of_normalizes_left Q A hn]
    have hpos : 0 < Nat.card A := Nat.card_pos
    nlinarith
  exact (relIndex_le_of_le_left (show A ≤ N from inf_le_right) index_ne_zero_of_finite).trans
    (by simpa only [A,inf_relIndex_left] using hb)

/-- Transport the original core-quotient commutant rigidity through the given central map. -/
theorem core_rigidity_central_image [Finite F]
    (f : G →* F) (hf : Function.Surjective f) (hk : f.ker ≤ center G)
    (B E : Subgroup G) [Group.IsPerfect B]
    (hkp : IsPGroup 2 (f.subgroupMap B).ker) (hm : ⁅E,B⁆ = E)
    (hfix : ∀ r ∈ normalizer (B : Set G) ⊓ normalizer (E : Set G),
      (∀ b ∈ B, ⁅r,b⁆ ∈ B.pCoreIn 2) → r ∈ centralizer (E : Set G)) :
    ∀ r ∈ normalizer (B.map f : Set F) ⊓ normalizer (E.map f : Set F),
      (∀ b ∈ B.map f, ⁅r,b⁆ ∈ (B.map f).pCoreIn 2) →
      r ∈ centralizer (E.map f : Set F) := by
  intro r hr hc
  obtain ⟨x,rfl⟩ := hf r
  have hxB : x ∈ normalizer (B : Set G) := by
    rw [←comap_normalizer_map_eq_of_perfect f hk B]
    exact hr.1
  have hxE := mem_normalizer_moved_of_central_image f hk B E hm hxB hr.2
  have hx : x ∈ centralizer (E : Set G) := by
    apply hfix x ⟨hxB,hxE⟩
    intro b hb
    apply mem_pCoreIn_of_map_mem f B hkp
    · exact le_normalizer_iff_commutator_le_right.mp (zpowers_le.mpr hxB)
        (commutator_mem_commutator (mem_zpowers x) hb)
    · rw [map_commutatorElement]
      exact hc (f b) (mem_map_of_mem f hb)
  rintro _ ⟨w,hw,rfl⟩
  simpa only [map_mul] using congrArg f (hx w hw)

omit [Finite G] in
/-- Restrict the literal core-quotient rigidity to an overgroup containing both original subgroups. -/
theorem core_rigidity_subgroupOf (C B E : Subgroup G) (hBC : B ≤ C) (hEC : E ≤ C)
    (hfix : ∀ r ∈ normalizer (B : Set G) ⊓ normalizer (E : Set G),
      (∀ b ∈ B, ⁅r,b⁆ ∈ B.pCoreIn 2) → r ∈ centralizer (E : Set G)) :
    ∀ r ∈ normalizer (B.subgroupOf C : Set C) ⊓ normalizer (E.subgroupOf C : Set C),
      (∀ b ∈ B.subgroupOf C, ⁅r,b⁆ ∈ (B.subgroupOf C).pCoreIn 2) →
      r ∈ centralizer (E.subgroupOf C : Set C) := by
  intro r hr hc
  have hrB : (r : G) ∈ normalizer (B : Set G) := by
    have h := hr.1
    rwa [←subgroupOf_normalizer_eq hBC] at h
  have hrE : (r : G) ∈ normalizer (E : Set G) := by
    have h := hr.2
    rwa [←subgroupOf_normalizer_eq hEC] at h
  have hrfix : (r : G) ∈ centralizer (E : Set G) := by
    apply hfix r ⟨hrB,hrE⟩
    intro b hb
    have h := hc ⟨b,hBC hb⟩ hb
    rwa [pCoreIn_subgroupOf 2 B C hBC] at h
  intro e he
  exact Subtype.ext (hrfix e he)
end Subgroup
