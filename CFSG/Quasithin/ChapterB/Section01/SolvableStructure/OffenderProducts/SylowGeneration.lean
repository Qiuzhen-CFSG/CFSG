module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Conjugation
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Mathlib.GroupTheory.Sylow


/-!
# Sylow generation around one or two symmetric-three factors

An ambient element fixing every factor acts by an inner automorphism on
each S₃. Their actual internal product implements all those automorphisms
simultaneously, leaving an element of the product centralizer. With one or
two factors the permutation image is a two-group, so the image of any
Sylow two-subgroup fills it. The product, its centralizer and that Sylow
subgroup therefore generate the whole original group.

Source: Aschbacher–Smith, proof of 14.1.7, printed p.977.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

private theorem inner_on_factor (i : Fin d.count) (b : G)
    (hb : b ∈ normalizer (d.factor i : Set G)) :
    ∃ k : d.factor i, ∀ x : d.factor i,
      b * (x : G) * b⁻¹ = (k : G) * x * (k : G)⁻¹ := by
  obtain ⟨eS⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let e := (d.factorModel i).trans eS
  let α := (d.factor i).normalizerMonoidHom ⟨b, hb⟩
  obtain ⟨k, hk⟩ := Theory.GroupTheory.NormalSymmetricThreePairRank.symmetricThree_aut_inner
    (e.symm.trans (α.trans e))
  refine ⟨e.symm k, fun x => ?_⟩
  have he : α x = e.symm k * x * (e.symm k)⁻¹ := by
    apply e.injective
    simpa [MulAut.conj_apply, map_mul, map_inv] using DFunLike.congr_fun hk (e x)
  exact congrArg Subtype.val he

theorem factorConjugation_kernel_le :
    d.factorConjugation.ker ≤ offenderSubgroup ρ ⊔ centralizer (offenderSubgroup ρ : Set G) := by
  classical
  intro b hb
  have hn (i : Fin d.count) : b ∈ normalizer (d.factor i : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (d.factor i).map (MulAut.conj b).toMonoidHom = d.factor i
    rw [d.factor_map_conj, show d.factorConjugation b = 1 from hb]
    rfl
  choose k hk using fun i => d.inner_on_factor i b (hn i)
  let a := d.productInclusion k
  have ha : a ∈ offenderSubgroup ρ := (d.groupProduct k).property
  have hcent : a⁻¹ * b ∈ centralizer (offenderSubgroup ρ : Set G) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    have hle : offenderSubgroup ρ ≤ centralizer ({a⁻¹ * b} : Set G) := by
      rw [← d.iSup_factor]
      apply iSup_le
      intro i y hy
      apply mem_centralizer_singleton_iff.mpr
      have he := (hk i ⟨y, hy⟩).trans (d.productInclusion_conj_single k i ⟨y, hy⟩).symm
      change b * y * b⁻¹ = a * y * a⁻¹ at he
      have hh := congrArg (fun z : G => a⁻¹ * z * b) he
      simpa [mul_assoc] using hh.symm
    exact mem_centralizer_singleton_iff.mp (hle hx)
  have hh := (offenderSubgroup ρ ⊔ centralizer (offenderSubgroup ρ : Set G)).mul_mem
    (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hcent)
  simpa only [mul_inv_cancel_left] using hh

theorem sylow_factor_generation [Finite G] (hn : d.count = 1 ∨ d.count = 2)
    (S : Sylow 2 G) :
    (offenderSubgroup ρ ⊔ centralizer (offenderSubgroup ρ : Set G)) ⊔ (S : Subgroup G) = ⊤ := by
  let f := d.factorConjugation
  have hp : IsPGroup 2 (Equiv.Perm (Fin d.count)) := by
    rcases hn with h | h
    · apply IsPGroup.of_card (n := 0)
      rw [Nat.card_perm, Nat.card_fin, h]
      decide
    · apply IsPGroup.of_card (n := 1)
      rw [Nat.card_perm, Nat.card_fin, h]
      decide
  have hr : IsPGroup 2 f.range := hp.to_subgroup _
  have hs : ((S.mapSurjective f.rangeRestrict_surjective : Sylow 2 f.range) : Subgroup f.range) = ⊤ :=
    (Sylow.is_maximal' _ (hr.to_subgroup ⊤) le_top).symm
  apply top_unique
  intro g _
  have hfg : f.rangeRestrict g ∈ (S : Subgroup G).map f.rangeRestrict := by
    rw [← Sylow.coe_mapSurjective f.rangeRestrict_surjective, hs]
    trivial
  obtain ⟨s, hsS, hsg⟩ := hfg
  have he : f s = f g := congrArg Subtype.val hsg
  have hker : g * s⁻¹ ∈ f.ker := by
    change f (g * s⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hmem := ((offenderSubgroup ρ ⊔ centralizer (offenderSubgroup ρ : Set G)) ⊔
    (S : Subgroup G)).mul_mem
      (Subgroup.mem_sup_left (d.factorConjugation_kernel_le hker)) (Subgroup.mem_sup_right hsS)
  simpa only [inv_mul_cancel_right] using hmem

end CFSG.Quasithin.ChapterB.SolvableFFFactors
