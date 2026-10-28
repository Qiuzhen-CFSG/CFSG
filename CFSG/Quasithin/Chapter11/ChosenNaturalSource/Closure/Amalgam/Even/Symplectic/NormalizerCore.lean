module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExtensionCores
public import Theory.Representation.SymplecticNaturalNormalizer.Centralizers

/-!
# The point core in the actual natural normalizer

Conjugation maps the binary natural normalizer into diagram-preserving
automorphisms of Sp₄. Its kernel consists of field scalars, so it has no
nonidentity two-elements. The local quotient-action detection theorem then
places each two-element of the point-local join core in the point local.
This proves the local core equality without discarding the scalar kernel or
assuming a normal symplectic subgroup of the full automorphism group of V.

Source: Aschbacher--Smith, F.1.12 and the radical inspection in 11.5.8,
printed pp.264 and 784. The original-group application is in Radical.
-/

public noncomputable section
open Subgroup Matrix Representation
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
open SymplecticNaturalNormalizer
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic.NormalizerCore
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
variable (hq : 2 < Nat.card F)

theorem scalar_two_power_eq_one (s : naturalNormalizer (F := F))
    (hk : conjugation hq s = 1) (k : ℕ) (hs : s ^ (2 ^ k) = 1) : s = 1 := by
  induction k generalizing s with
  | zero => simpa using hs
  | succ k ih =>
    apply eq_one_of_conjugation_eq_one_of_sq hq s hk
    apply ih (s ^ 2) (by simp [hk])
    simpa only [← pow_mul, Nat.pow_succ'] using hs

theorem eq_natural_of_two_power (s : naturalNormalizer (F := F))
    (g : Sp F) (he : conjugation hq s = MulAut.conj g)
    (htwo : ∃ k : ℕ, s ^ (2 ^ k) = 1) : s = naturalElement hq g := by
  obtain ⟨k,hk⟩ := htwo
  have hg : g ^ (2 ^ k) = 1 := by
    apply InvolutionNormalForms.inner_injective
    rw [map_pow, ← he, ← map_pow, hk, map_one, map_one]
  let t := s * (naturalElement hq g)⁻¹
  have ht : conjugation hq t = 1 := by
    dsimp only [t]
    rw [map_mul,map_inv,conjugation_naturalElement,he,mul_inv_cancel]
  have hcomm : Commute t (naturalElement hq g) := by
    apply Subtype.ext
    have he' := conjugation_apply hq t g
    rw [ht] at he'
    exact mul_inv_eq_iff_eq_mul.mp he'.symm
  have htpow : t ^ (2 ^ k) = 1 := by
    have he' : t * naturalElement hq g = s := by simp [t]
    have h := hcomm.mul_pow (2 ^ k)
    rw [he',hk,← map_pow,hg,map_one,mul_one] at h
    exact h.symm
  exact mul_inv_eq_one.mp (scalar_two_power_eq_one hq t ht k htpow)

theorem naturalElement_injective : Function.Injective (naturalElement (F := F) hq) := by
  intro g h he
  exact naturalHom_injective (congrArg Subtype.val he)

private theorem action_map (L : Subgroup (Sp F)) (g : naturalNormalizer (F := F))
    (hg : g ∈ normalizer (L.map (naturalElement hq) : Set _)) :
    L.map (conjugation hq g).toMonoidHom = L := by
  apply Subgroup.map_injective (naturalElement_injective hq)
  rw [Subgroup.map_map]
  have he : (naturalElement hq).comp (conjugation hq g).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (naturalElement hq) := by
    ext x : 1
    apply Subtype.ext
    exact conjugation_apply hq g x
  rw [he, ← Subgroup.map_map]
  exact mem_normalizer_iff_map_conj_eq.mp hg

private theorem embedded_core (L : Subgroup (Sp F)) :
    (pCore 2 (L.map (naturalElement hq))).map (L.map (naturalElement hq)).subtype =
      ((pCore 2 L).map L.subtype).map (naturalElement hq) := by
  let e := L.equivMapOfInjective (naturalElement hq) (naturalElement_injective hq)
  rw [← pCore_map_iso 2 e, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem action_difference (L : Subgroup (Sp F))
    (g : naturalNormalizer (F := F))
    (hL : L.map (conjugation hq g).toMonoidHom = L)
    (hc : ∀ l : L.map (naturalElement hq),
      ⁅g,l.val⁆ ∈ (pCore 2 (L.map (naturalElement hq))).map
        (L.map (naturalElement hq)).subtype) (l : L) :
    restrict (conjugation hq g) L hL l / l ∈ pCore 2 L := by
  let f := naturalElement hq
  have h := hc ⟨f l.val, mem_map_of_mem f l.property⟩
  rw [embedded_core] at h
  have he : f (restrict (conjugation hq g) L hL l / l).val = ⁅g,f l.val⁆ := by
    simp only [Subgroup.coe_div, map_div, restrict_apply]
    have ha : f (conjugation hq g l.val) = g * f l.val * g⁻¹ := by
      apply Subtype.ext
      exact conjugation_apply hq g l.val
    rw [ha]
    simp only [div_eq_mul_inv,commutatorElement_def]
  rw [← he] at h
  exact (Subgroup.mem_map_iff_mem L.subtype_injective).mp
    ((Subgroup.mem_map_iff_mem (naturalElement_injective hq)).mp h)

variable {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)

include hcard hn in
theorem pointLocal_join_core_eq (S : Subgroup (naturalNormalizer (F := F)))
    (hnorm : S ≤ normalizer (pointLocal.map (naturalElement hq) : Set _)) :
    (pCore 2 (pointLocal.map (naturalElement hq) ⊔ S : Subgroup _)).map
      (pointLocal.map (naturalElement hq) ⊔ S).subtype =
      (pCore 2 (pointLocal.map (naturalElement hq))).map
        (pointLocal.map (naturalElement hq)).subtype := by
  apply join_pCore_eq_of_quotient_action_detection 2 _ S hnorm
  intro g hg htwo hc
  have hgnorm : g ∈ normalizer (pointLocal.map (naturalElement hq) : Set _) :=
    (sup_le (pointLocal.map (naturalElement hq)).le_normalizer hnorm) hg
  have hL := action_map hq pointLocal g hgnorm
  have hatwo : ∃ k : ℕ, conjugation hq g ^ (2 ^ k) = 1 := by
    obtain ⟨k,hk⟩ := htwo
    exact ⟨k,by rw [← map_pow,hk,map_one]⟩
  have hact : pointSL2Action hcard hn (conjugation hq g) hL = 1 := by
    apply MulEquiv.ext
    intro A
    obtain ⟨l,rfl⟩ := pointQuotient_surjective A
    rw [pointSL2Action_quotient]
    change pointQuotient (restrict (conjugation hq g) pointLocal hL l) = pointQuotient l
    rw [← pointLocalCoreQuotientEquiv_mk hcard hn,
      ← pointLocalCoreQuotientEquiv_mk hcard hn]
    exact congrArg (pointLocalCoreQuotientEquiv hcard hn)
      (QuotientGroup.eq_iff_div_mem.mpr (action_difference hq pointLocal g hL hc l))
  obtain ⟨l,hl⟩ := pointSL2Action_kernel_of_preservesDiagram hcard hn
    (conjugation hq g) (conjugation_preservesDiagram hq g) hL hatwo hact
  rw [eq_natural_of_two_power hq g l.val hl htwo]
  exact mem_map_of_mem _ l.property
include hq in
/-- A quotient marking suffices to put each actual operator in the natural normalizer. -/
theorem operator_mem_of_quotient
    {H : Type*} [Group H] (J : Subgroup H) [J.Normal]
    (q : J →* Sp F) (hqs : Function.Surjective q)
    (ρ : Representation (ZMod 2) H (Vector F))
    (hnat : ∀ (j : J) v, ρ (j : H) v = symplecticNatural 2 (q j) v)
    (x : H) : linearAction ρ x ∈ naturalNormalizer := by
  have hj (j : J) : linearAction ρ j.val = naturalHom (q j) := by
    apply LinearEquiv.ext
    exact hnat j
  have him : J.map (linearAction ρ) = naturalDerivedImage := by
    apply le_antisymm
    · rintro _ ⟨j,hj',rfl⟩
      rw [hj ⟨j,hj'⟩]
      exact naturalHom_mem hq _
    · rintro _ ⟨b,rfl⟩
      obtain ⟨j,hj'⟩ := hqs b.val
      refine ⟨j.val,j.property,?_⟩
      rw [hj,hj']
      rfl
  change linearAction ρ x ∈ normalizer (naturalDerivedImage (F := F) : Set _)
  rw [← him]
  exact J.le_normalizer_map (linearAction ρ)
    (mem_map_of_mem _ (J.normalizer_eq_top ▸ mem_top x))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic.NormalizerCore
