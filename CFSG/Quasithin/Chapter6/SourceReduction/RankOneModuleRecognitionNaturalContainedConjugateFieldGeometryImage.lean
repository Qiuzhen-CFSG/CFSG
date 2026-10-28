module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometrySubmodule

/-!
# Natural images of the two-copy field module

A nonzero equivariant map from an irreducible natural module is injective.
Thus a nonzero map from two natural copies to a module of one-copy order
restricts to an equivalence on one summand. Unlike the subgroup version,
this also applies to a commutator line outside the original layer.

The source use is the displacement map in Aschbacher–Smith 6.1.14(5),
printed pp.671–672, with actor O²(N_L(U)).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] {K U A : Subgroup G} {m : ℕ}

/-- A nonzero equivariant map from a natural module is injective. -/
theorem natural_equivariant_injective (hnatural : IsNaturalModule K U m)
    (p : U →* A)
    (hp : ∀ (k : K) (u u' : U),
      (u' : G) = (k : G) * (u : G) * (k : G)⁻¹ →
      (p u' : G) = (k : G) * (p u : G) * (k : G)⁻¹)
    (hne : ∃ u, p u ≠ 1) : Function.Injective p := by
  have hKU : K ≤ normalizer (U : Set G) := by
    obtain ⟨_, _, _, _, _, hmodel⟩ := hnatural
    exact hmodel.normalizes
  let J := p.ker.map U.subtype
  have hJU : J ≤ U := map_subtype_le _
  have hKJ : K ≤ normalizer (J : Set G) := by
    apply le_normalizer_iff.mpr
    rintro k hk y ⟨u, hu, rfl⟩
    let u' : U := ⟨k * (u : G) * k⁻¹, (mem_normalizer_iff.mp (hKU hk) u).mp u.property⟩
    refine ⟨u', ?_, rfl⟩
    apply p.mem_ker.mpr
    apply Subtype.ext
    have hh := hp ⟨k, hk⟩ u u' rfl
    rw [p.mem_ker.mp hu] at hh
    simpa using hh
  have hJUneq : J ≠ U := by
    intro hj
    obtain ⟨u, hu⟩ := hne
    have hm : (u : G) ∈ J := hj.symm ▸ u.property
    obtain ⟨v, hv, he⟩ := hm
    exact hu ((congrArg p (Subtype.ext he)).symm.trans (p.mem_ker.mp hv))
  have hJbot := (hnatural.invariant_subgroup J hJU hKJ).resolve_right hJUneq
  apply (MonoidHom.ker_eq_bot_iff p).mp
  apply bot_unique
  intro u hu
  apply mem_bot.mpr
  apply Subtype.ext
  have hm : (u : G) ∈ J := ⟨u, hu, rfl⟩
  rwa [hJbot, mem_bot] at hm

variable [Finite G]

/-- A nonzero equivariant image of two natural copies, of one-copy order, is natural. -/
theorem natural_of_nonzero_double_image {B : Subgroup G}
    (hnatural : IsNaturalModule K U m)
    (hKA : K ≤ normalizer (A : Set G))
    (hcard : Nat.card A = Nat.card U)
    (e : B ≃* (U × U))
    (he : ∀ (k : K) (b b' : B),
      (b' : G) = (k : G) * (b : G) * (k : G)⁻¹ →
      ((e b').1 : G) = (k : G) * ((e b).1 : G) * (k : G)⁻¹ ∧
      ((e b').2 : G) = (k : G) * ((e b).2 : G) * (k : G)⁻¹)
    (hKB : K ≤ normalizer (B : Set G))
    (d : B →* A) (hd : ∃ b, d b ≠ 1)
    (hdK : ∀ (k : K) (b b' : B),
      (b' : G) = (k : G) * (b : G) * (k : G)⁻¹ →
      (d b' : G) = (k : G) * (d b : G) * (k : G)⁻¹) :
    IsNaturalModule K A m := by
  have hKU : K ≤ normalizer (U : Set G) := by
    obtain ⟨_, _, _, _, _, hmodel⟩ := hnatural
    exact hmodel.normalizes
  let p₁ : U →* A := d.comp (e.symm.toMonoidHom.comp (MonoidHom.inl U U))
  let p₂ : U →* A := d.comp (e.symm.toMonoidHom.comp (MonoidHom.inr U U))
  have heinv (k : K) (u v u' v' : U)
      (hu : (u' : G) = (k : G) * (u : G) * (k : G)⁻¹)
      (hv : (v' : G) = (k : G) * (v : G) * (k : G)⁻¹) :
      (e.symm (u',v') : G) = (k : G) * (e.symm (u,v) : G) * (k : G)⁻¹ := by
    let b := e.symm (u,v)
    let b' : B := ⟨(k : G) * (b : G) * (k : G)⁻¹,
      (mem_normalizer_iff.mp (hKB k.property) b).mp b.property⟩
    have hh := he k b b' rfl
    dsimp only [b] at hh
    rw [e.apply_symm_apply] at hh
    have heq : e b' = (u',v') := by
      apply Prod.ext
      · apply Subtype.ext
        exact hh.1.trans hu.symm
      · apply Subtype.ext
        exact hh.2.trans hv.symm
    have hh' := congrArg (fun w => (e.symm w : G)) heq
    simpa only [e.symm_apply_apply] using hh'.symm
  have hp₁ : ∀ (k : K) (u u' : U),
      (u' : G) = (k : G) * (u : G) * (k : G)⁻¹ →
      (p₁ u' : G) = (k : G) * (p₁ u : G) * (k : G)⁻¹ := by
    intro k u u' hu
    exact hdK k _ _ (heinv k u 1 u' 1 hu (by simp))
  have hp₂ : ∀ (k : K) (u u' : U),
      (u' : G) = (k : G) * (u : G) * (k : G)⁻¹ →
      (p₂ u' : G) = (k : G) * (p₂ u : G) * (k : G)⁻¹ := by
    intro k u u' hu
    exact hdK k _ _ (heinv k 1 u 1 u' (by simp) hu)
  have hp : (∃ u, p₁ u ≠ 1) ∨ ∃ u, p₂ u ≠ 1 := by
    by_contra! hz
    obtain ⟨b, ha⟩ := hd
    have hb : b = e.symm ((e b).1,1) * e.symm (1,(e b).2) := by
      rw [← map_mul]; simp
    apply ha
    rw [hb, map_mul]
    change p₁ (e b).1 * p₂ (e b).2 = 1
    rw [hz.1, hz.2, one_mul]
  have step (p : U →* A)
      (hp : ∀ (k : K) (u u' : U),
        (u' : G) = (k : G) * (u : G) * (k : G)⁻¹ →
        (p u' : G) = (k : G) * (p u : G) * (k : G)⁻¹)
      (hne : ∃ u, p u ≠ 1) : IsNaturalModule K A m := by
    have hi := natural_equivariant_injective hnatural p hp hne
    let f := MulEquiv.ofBijective p ((Nat.bijective_iff_injective_and_card p).mpr ⟨hi,hcard.symm⟩)
    apply natural_of_equivariant_equiv hnatural hKA f.symm
    intro k a a' ha
    let u := f.symm a
    let u' : U := ⟨(k : G) * (u : G) * (k : G)⁻¹,
      (mem_normalizer_iff.mp (hKU k.property) u).mp u.property⟩
    have hh := hp k u u' rfl
    have hf : f u' = a' := Subtype.ext (by
      change (f u' : G) = (k : G) * (f (f.symm a) : G) * (k : G)⁻¹ at hh
      rw [f.apply_symm_apply] at hh
      exact hh.trans ha.symm)
    have hh' := congrArg (fun w => (f.symm w : G)) hf
    simpa only [f.symm_apply_apply] using hh'.symm
  exact hp.elim (step p₁ hp₁) (step p₂ hp₂)
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
