module
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.CubicInverter
public import Theory.SpecificGroups.SymplecticFour.SylowFixedCubic
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Inverted cubic obstructions in lifted symplectic Borels

A solvable subgroup normalized by a Sylow two-subgroup in a two-kernel
cover of Sp₄(2ⁿ), n > 1, lies in its Sylow normalizer. Aligning that exact
Sylow with the standard unipotent subgroup gives a surjective map from its
normalizer to the two-parameter torus, with the original Sylow as kernel.
This map intertwines any compatible automorphism.

For an actor of two-power order, displacement of size at most three forces
trivial torus action. The intrinsic graph-torus calculation includes fields
of orders four and sixty-four; neither is an exception. The original
14.7.41 application uses the fixed supplement supplied by N_G(L) and the
inverted cubic image of L₁ to contradict this conclusion.

Source: Aschbacher–Smith 14.7.41(2), printed p.1061, and the intrinsic
symplectic automorphism calculation used in 13.6.6 and 13.8.20,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.InvertedCubicBorel
open EvenBorelTorus EvenBorelTorus.ActorReduction
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

private theorem torus_eq_one_of_small_displacement {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) (a : ActorReduction.stabilizer (F := F))
    (ha : ∃ k : ℕ, a^(2^k) = 1)
    (hc : Nat.card (torusDisplacement (torusAction hF a)).range ≤ 3) :
    torusAction hF a = 1 := by
  let τ := torusAction hF a
  let δ := torusDisplacement τ
  have hp : IsPGroup 2 (zpowers τ) := by
    obtain ⟨k,hk⟩ := ha
    apply IsPGroup.of_card_dvd_pow (n := k)
    rw [Nat.card_zpowers]
    apply orderOf_dvd_of_pow_eq_one
    change (torusAction hF a)^(2^k) = 1
    rw [←map_pow,hk,map_one]
  by_contra hne
  have hR : δ.range ≠ ⊥ := by
    intro hh
    apply hne
    apply MulEquiv.ext
    intro x
    have hx : δ x ∈ δ.range := ⟨x,rfl⟩
    rw [hh,mem_bot] at hx
    exact mul_inv_eq_one.mp hx
  have hgt : 1 < Nat.card δ.range := (one_lt_card_iff_ne_bot _).mpr hR
  have ho : Odd (Nat.card δ.range) :=
    Odd.of_dvd_nat (Nat.coprime_two_left.mp (torus_odd hF)) δ.range.card_subgroup_dvd_card
  have hcard : Nat.card δ.range = 3 := by
    change Nat.card δ.range ≤ 3 at hc
    rw [Nat.odd_iff] at ho
    omega
  apply hne
  apply CubicInverter.torus_eq_one_of_index_three_fixer hn hF τ
    (torusAction_mem_graph hF hn
      DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram a) hp δ.ker
  · rw [index_ker]
    exact hcard
  · intro x hx
    exact mul_inv_eq_one.mp hx

/-- Lift solvable Sylow-normalized subgroups through an arbitrary two-kernel. -/
theorem solvable_sylow_normalized_le_normalizer
    (hF : 2 < Nat.card F) (q : G →* Sp F) (hq : Function.Surjective q)
    (P : Sylow 2 G) (hk : q.ker ≤ (P : Subgroup G))
    (A : Subgroup G) [Group.IsSolvable A]
    (hnorm : (P : Subgroup G) ≤ normalizer (A : Set G)) :
    A ≤ normalizer (P : Set G) := by
  let := P.isPGroup'.isNilpotent
  let : Group.IsSolvable (A ⊔ (P : Subgroup G) : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes A P hnorm
  let H := (A ⊔ (P : Subgroup G)).map q
  have hs : Group.IsSolvable H :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  have hN := solvable_sylow_overgroup_normalizes hF (P.mapSurjective hq) H hs
    (map_mono le_sup_right)
  have hc := (map_le_iff_le_comap).mp hN
  change A ⊔ (P : Subgroup G) ≤
    (normalizer ((P : Subgroup G).map q : Set (Sp F))).comap q at hc
  rw [comap_normalizer_eq_of_surjective _ hq,comap_map_eq_self hk] at hc
  exact le_sup_left.trans hc

/-- The literal normalizer quotient and its original compatible two-power actor. -/
theorem exists_normalizer_torus_action
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (q : G →* Sp F) (hq : Function.Surjective q) (P : Sylow 2 G)
    (hk : q.ker ≤ (P : Subgroup G)) (α : MulAut G) (β : MulAut (Sp F))
    (hβ : ∃ k : ℕ, β^(2^k) = 1)
    (he : ∀ x, q (α x) = β (q x))
    (hP : (P : Subgroup G).map α.toMonoidHom = P) :
    ∃ f : normalizer (P : Set G) →* (Fˣ × Fˣ), ∃ τ : MulAut (Fˣ × Fˣ),
      Function.Surjective f ∧
      (∀ x, f x = 1 ↔ (x : G) ∈ P) ∧
      (∀ x y : normalizer (P : Set G), α x = y → f y = τ (f x)) ∧
      (Nat.card (torusDisplacement τ).range ≤ 3 → τ = 1) := by
  let Q := P.mapSurjective hq
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) Q (unipotentSylow hF hn.le)
  let e := MulAut.conj g
  let q' := e.toMonoidHom.comp q
  have hq' : Function.Surjective q' := e.surjective.comp hq
  have hU : (P : Subgroup G).map q' = unipotent := by
    rw [show q' = e.toMonoidHom.comp q from rfl,←Subgroup.map_map]
    exact congrArg Sylow.toSubgroup hg
  let N := normalizer (P : Set G)
  have hN : N.map q' = borel := by
    rw [P.normalizer_map_surjective q' hq']
    rw [hU,←borel_eq_normalizer_unipotent]
  let f₀ : N →* borel (F := F) := (q'.comp N.subtype).codRestrict borel
    (fun x => hN.le (mem_map_of_mem q' x.property))
  have hf₀ : Function.Surjective f₀ := by
    intro y
    obtain ⟨x,hx,heq⟩ := hN.ge y.property
    exact ⟨⟨x,hx⟩,Subtype.ext heq⟩
  let f := borelCharacters.comp f₀
  let β' := MulAut.congr e β
  have he' (x : G) : q' (α x) = β' (q' x) := by
    change e (q (α x)) = e (β (e.symm (e (q x))))
    rw [he,e.symm_apply_apply]
  have hstab : unipotent.map β'.toMonoidHom = unipotent := by
    have heq : β'.toMonoidHom.comp q' = q'.comp α.toMonoidHom :=
      MonoidHom.ext (fun x => (he' x).symm)
    rw [←hU,Subgroup.map_map,heq,←Subgroup.map_map,hP]
  let a : ActorReduction.stabilizer (F := F) := ⟨β',hstab⟩
  refine ⟨f,torusAction hF a,characters_surjective.comp hf₀,?_,?_,?_⟩
  · intro x
    change borelCharacters (f₀ x) = 1 ↔ _
    rw [borelCharacters_eq_one]
    change q' x ∈ unipotent ↔ _
    rw [←hU]
    change x.val ∈ ((P : Subgroup G).map q').comap q' ↔ _
    rw [comap_map_eq_self (show q'.ker ≤ (P : Subgroup G) from fun x hx =>
      hk (e.map_eq_one_iff.mp hx))]
    rfl
  · intro x y hxy
    change borelCharacters (f₀ y) = torusAction hF a (borelCharacters (f₀ x))
    rw [torusAction_characters]
    congr 1
    apply Subtype.ext
    change q' y = β' (q' x)
    rw [←hxy,he']
  · apply torus_eq_one_of_small_displacement hn hF a
    obtain ⟨k,hk⟩ := hβ
    refine ⟨k,Subtype.ext ?_⟩
    change (MulAut.congr e β)^(2^k) = 1
    rw [←map_pow,hk,map_one]

end Theory.SpecificGroups.SymplecticFour.InvertedCubicBorel
