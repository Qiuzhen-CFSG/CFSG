module
public import Mathlib.GroupTheory.Sylow
public import Theory.GroupTheory.SubgroupConjugation
public import Stellmacher.OmegaOneCenterMap

/-!
# Normalizers of abelian Sylow omega subgroups and invariant conjugates

If a p-subgroup V is weakly closed in a Sylow p-subgroup of N(B), then
N(V) is transitive on the conjugates of B normalized by V. Conjugate V
back into N(B), align its Sylow subgroup, and use weak closure to correct
the original conjugator. For abelian Sylow subgroups, their omega subgroup
is weakly closed simply because every element of order dividing two lies
in it. The numerical C4-square bound identifies the literal source seed.

Source: Aschbacher--Smith J.4.10, first paragraph, printed p.444, applying
the Sylow argument in A.1.7. No coprime-complement conjugacy is asserted.
-/

public section
open Subgroup
open scoped Pointwise

namespace Theory.GroupTheory.NormalizedSylowTransitivity
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Weak closure corrects a conjugator to normalize the invariant subgroup. -/
theorem conjugator (B V : Subgroup G) (P : Sylow p (normalizer (B : Set G)))
    (hV : IsPGroup p V)
    (hweak : ∀ g : G, V.conjBy g ≤ (P : Subgroup (normalizer (B : Set G))).map
      (normalizer (B : Set G)).subtype → V.conjBy g = V)
    (g : G) (hn : V ≤ normalizer ((B.conjBy g : Subgroup G) : Set G)) :
    ∃ n ∈ normalizer (V : Set G), B.conjBy n = B.conjBy g := by
  let N := normalizer (B : Set G)
  let W := V.conjBy g⁻¹
  have hWN : W ≤ N := by
    rintro _ ⟨v, hv, rfl⟩
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hh := mem_normalizer_iff_map_conj_eq.mp (hn hv)
    change (B.conjBy g).conjBy v = B.conjBy g at hh
    have hh' := congrArg (fun A : Subgroup G => A.conjBy g⁻¹) hh
    change B.conjBy ((MulAut.conj g⁻¹) v) = B
    simpa only [conjBy_conjBy, inv_mul_cancel, conjBy_one, MulAut.conj_apply,
      inv_inv, mul_assoc] using hh'
  obtain ⟨R, hR⟩ := ((hV.map (MulAut.conj g⁻¹).toMonoidHom).comap_subtype
    (K := N)).exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq N R P
  have hm : (W.subgroupOf N).map (MulAut.conj a).toMonoidHom ≤ (P : Subgroup N) := by
    rw [← ha]
    exact map_mono hR
  have hfix : V.conjBy ((a : G) * g⁻¹) = V := by
    apply hweak
    rintro _ ⟨v, hv, rfl⟩
    have hw : (MulAut.conj g⁻¹) v ∈ W := mem_map_of_mem _ hv
    have hav := hm (mem_map_of_mem (MulAut.conj a).toMonoidHom
      (show (⟨(MulAut.conj g⁻¹) v, hWN hw⟩ : N) ∈ W.subgroupOf N from hw))
    have hh := mem_map_of_mem N.subtype hav
    convert hh using 1
    simp [MulAut.conj_apply, mul_assoc]
  have han : (a : G) * g⁻¹ ∈ normalizer (V : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr hfix
  refine ⟨g * (a : G)⁻¹, ?_, ?_⟩
  · simpa only [mul_inv_rev, inv_inv] using (normalizer (V : Set G)).inv_mem han
  · have haB : B.conjBy (a : G)⁻¹ = B :=
      mem_normalizer_iff_map_conj_eq.mp (N.inv_mem a.property)
    rw [conjBy_mul, haB]

/-- The omega subgroup of an abelian subgroup is weakly closed inside it. -/
theorem omega_weakly_closed (I : Subgroup G) [IsMulCommutative I]
    (g : G) (hg : (Stellmacher.omegaOneCenterAmbient I).conjBy g ≤ I) :
    (Stellmacher.omegaOneCenterAmbient I).conjBy g = Stellmacher.omegaOneCenterAmbient I := by
  apply eq_of_le_of_card_ge
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy2 := ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hy).2.1
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hg (mem_map_of_mem _ hy), ?_, ?_⟩
    · change ((MulAut.conj g) y)^2 = 1
      rw [← map_pow, hy2, map_one]
    · intro q hq
      exact congrArg Subtype.val (mul_comm' (⟨q,hq⟩ : I) ⟨_,hg (mem_map_of_mem _ hy)⟩)
  · rw [conjBy, card_map_of_injective (MulAut.conj g).injective]

omit [Finite G] in
/-- The central involutions of a marked C4-square form a subgroup of order at most four. -/
theorem omega_card_le_four (I : Subgroup G)
    (e : I ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :
    Nat.card (Stellmacher.omegaOneCenterAmbient I) ≤ 4 := by
  let f : Stellmacher.omegaOneCenterAmbient I →
      {x : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // x^2=1} := fun x =>
    ⟨e ⟨x,(Stellmacher.mem_omegaOneCenterAmbient_iff I x).mp x.property |>.1⟩, by
      rw [← map_pow]
      have he : (⟨x,(Stellmacher.mem_omegaOneCenterAmbient_iff I x).mp x.property |>.1⟩ : I)^2=1 :=
        Subtype.ext ((Stellmacher.mem_omegaOneCenterAmbient_iff I x).mp x.property).2.1
      rw [he,map_one]⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun a : I => (a : G)) (e.injective (congrArg Subtype.val h)))
  exact (Nat.card_le_card_of_injective f hf).trans_eq (by
    rw [Nat.card_eq_fintype_card]
    decide +kernel)

/-- An abelian Sylow omega subgroup controls normalized conjugates of B. -/
theorem omega_conjugator (B I : Subgroup G) [IsMulCommutative I]
    (hIN : I ≤ normalizer (B : Set G)) (hI : IsPGroup 2 I)
    (hi : ¬ 2 ∣ (I.subgroupOf (normalizer (B : Set G))).index)
    (g : G) (hn : Stellmacher.omegaOneCenterAmbient I ≤
      normalizer ((B.conjBy g : Subgroup G) : Set G)) :
    ∃ n ∈ normalizer (Stellmacher.omegaOneCenterAmbient I : Set G),
      B.conjBy n = B.conjBy g := by
  let P := (hI.comap_subtype (K := normalizer (B : Set G))).toSylow hi
  apply conjugator B (Stellmacher.omegaOneCenterAmbient I) P
    ((Stellmacher.omegaOneCenterAmbient_elementaryAbelian I).isPGroup) _ g hn
  intro a ha
  change (Stellmacher.omegaOneCenterAmbient I).conjBy a ≤
    (I.subgroupOf (normalizer (B : Set G))).map (normalizer (B : Set G)).subtype at ha
  rw [map_subgroupOf_eq_of_le hIN] at ha
  exact omega_weakly_closed I a ha
end Theory.GroupTheory.NormalizedSylowTransitivity
