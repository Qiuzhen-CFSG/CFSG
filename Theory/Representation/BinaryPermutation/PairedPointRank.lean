module
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five

/-!
# Point rank for a normal pair of orthogonal A₅ modules

Intersect an ambient Sylow two-subgroup with the normal A₅ × A₅ subgroup.
In each natural four-space its Sylow-fixed vectors are fixed by a cubic
element. The two cyclic groups embed independently in the point stabilizer,
giving three-rank at least two.
Source: Aschbacher–Smith 12.8.13(7), printed p.856.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryPermutationPair
private def pointFixer {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (v : V) : Subgroup D where
  carrier := {a | ρ a v = v}
  one_mem' := by change ρ 1 v = v; simp
  mul_mem' := by
    intro a b ha hb
    change ρ (a*b) v = v
    exact (congrArg (ρ a) hb).trans ha |> (by simpa only [map_mul, Module.End.mul_apply] using ·)
  inv_mem' := by
    intro a ha
    have hh := congrArg (ρ a⁻¹) ha
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at hh
    exact hh.symm

/-- A point fixed by an ambient Sylow has independent cubic stabilizers in
both orthogonal A₅ summands. -/
theorem two_le_point_rank {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (H : Subgroup D) [H.Normal]
    (e : H ≃* (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))
    (c : V ≃ₗ[ZMod 2]
      (BinaryPermutation.natural (Fin 5) × BinaryPermutation.natural (Fin 5)))
    (hact : ∀ (a : H) u, c (ρ a u) =
      (BinaryPermutation.naturalRepresentation (Fin 5) (e a).1.val (c u).1,
       BinaryPermutation.naturalRepresentation (Fin 5) (e a).2.val (c u).2))
    (S : Sylow 2 D) (v : V) (hv : ∀ a ∈ S, ρ a v = v)
    (C : Subgroup D) (hC : ∀ a, a ∈ C ↔ ρ a v = v) :
    2 ≤ primeRank 3 C := by
  let A := alternatingGroup (Fin 5)
  let τ := BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 5)
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal H
  let f : H →* A := (MonoidHom.fst A A).comp e.toMonoidHom
  let k : H →* A := (MonoidHom.snd A A).comp e.toMonoidHom
  have hf : Function.Surjective f := Prod.fst_surjective.comp e.surjective
  have hk : Function.Surjective k := Prod.snd_surjective.comp e.surjective
  let P := R.mapSurjective hf
  let Q := R.mapSurjective hk
  have hpv : (c v).1 ∈ fixedSpace τ (P : Subgroup A) := by
    rintro ⟨a,ha⟩
    obtain ⟨b,hb,rfl⟩ := ha
    have hbs : (b : D) ∈ S := show b ∈ (S : Subgroup D).subgroupOf H from hR ▸ hb
    have hh := congrArg Prod.fst (hact b v)
    rw [hv _ hbs] at hh
    exact hh.symm
  have hqv : (c v).2 ∈ fixedSpace τ (Q : Subgroup A) := by
    rintro ⟨a,ha⟩
    obtain ⟨b,hb,rfl⟩ := ha
    have hbs : (b : D) ∈ S := show b ∈ (S : Subgroup D).subgroupOf H from hR ▸ hb
    have hh := congrArg Prod.snd (hact b v)
    rw [hv _ hbs] at hh
    exact hh.symm
  have cubic (P : Sylow 2 A) (w : BinaryPermutation.natural (Fin 5))
      (hw : w ∈ fixedSpace τ (P : Subgroup A)) :
      ∃ d : A, orderOf d = 3 ∧ τ d w = w := by
    obtain ⟨d,hd,hpow,hfix⟩ := sylow_fixedSpace_enlargement_of_cubic τ
      BinaryPermutation.CubicFixedSpace.Five.klein
      BinaryPermutation.CubicFixedSpace.Five.klein_isPGroup
      BinaryPermutation.CubicFixedSpace.Five.cycle
      BinaryPermutation.CubicFixedSpace.Five.cycle_pow
      BinaryPermutation.CubicFixedSpace.Five.cycle_ne_one
      BinaryPermutation.CubicFixedSpace.Five.cycle_fixes_natural P
    refine ⟨d,?_,hfix w hw⟩
    exact ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp
      (orderOf_dvd_of_pow_eq_one hpow)).resolve_left
        (fun he => hd ((orderOf_eq_one_iff.mp he).symm ▸ P.one_mem))
  obtain ⟨a,ha,hav⟩ := cubic P _ hpv
  obtain ⟨b,hb,hbv⟩ := cubic Q _ hqv
  let A₁ := zpowers a
  let A₂ := zpowers b
  let : CommGroup A₁ := IsCyclic.commGroup
  let : CommGroup A₂ := IsCyclic.commGroup
  have hA₁ : Nat.card A₁ = 3 := (Nat.card_zpowers a).trans ha
  have hA₂ : Nat.card A₂ = 3 := (Nat.card_zpowers b).trans hb
  have hfix₁ : ∀ z : A₁, τ z (c v).1 = (c v).1 :=
    fun z => (zpowers_le.mpr (show a ∈ pointFixer τ (c v).1 from hav)) z.property
  have hfix₂ : ∀ z : A₂, τ z (c v).2 = (c v).2 :=
    fun z => (zpowers_le.mpr (show b ∈ pointFixer τ (c v).2 from hbv)) z.property
  let j : A₁ × A₂ →* D := H.subtype.comp
    (e.symm.toMonoidHom.comp (A₁.subtype.prodMap A₂.subtype))
  have hj : Function.Injective j := by
    intro x y h
    have he := e.symm.injective (Subtype.val_injective h)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he))
      (Subtype.ext (congrArg Prod.snd he))
  have hjC (z : A₁ × A₂) : j z ∈ C := by
    apply (hC _).mpr
    apply c.injective
    have hh := hact (e.symm ((z.1 : A),(z.2 : A))) v
    rw [e.apply_symm_apply] at hh
    exact hh.trans (Prod.ext (hfix₁ z.1) (hfix₂ z.2))
  apply primeRank_ge_of_elementary_embedding (A := A₁ × A₂)
    (f := j.codRestrict C hjC)
  · intro z
    apply Prod.ext
    · change z.1 ^ 3 = 1
      simpa only [hA₁] using pow_card_eq_one' (x := z.1)
    · change z.2 ^ 3 = 1
      simpa only [hA₂] using pow_card_eq_one' (x := z.2)
  · rw [Nat.card_prod,hA₁,hA₂]
    decide
  · intro x y h
    apply hj
    exact congrArg (fun z : C => (z : D)) h
end Representation.BinaryPermutationPair
