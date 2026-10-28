module
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockResidual
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Stellmacher.MaxElementaryOffender
public import Theory.Representation.BinaryPermutation.EightTransvectionActors

/-!
# Thompson control in the four-block radical on the binary eight-point core

On the seven-dimensional augmentation core, every nontrivial subgroup A of
V4 × V4 satisfies |A| |C_V(A)| ≤ 64 < |V|. Its two coordinate projections
bound |A|; fixing a product of the disjoint block permutations is equivalent
to fixing both factors. The finite certificates inspect only the sixteen
subsets of each four-element coordinate set and the 128 core vectors.

Transport the inequality to the literal automorphism image. The maximum
elementary subgroup replacement inequality then proves that J(S) centralizes
an actual normal elementary subgroup U whenever the S-action, under the
given core coordinates, lies in this four-block radical.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.1(4), printed p.823, used in the fusion argument 12.6.19, p.828.
-/

public section
open Subgroup
open Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction
namespace BinaryPermutation.FourBlockThompson
local instance : DecidablePred (· ∈ core (Fin 8)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype (core (Fin 8)) := Subtype.fintype _

private def fixedWords (s t : Finset (Fin 4)) : Finset (core (Fin 8)) :=
  Finset.univ.filter fun v =>
    (∀ a ∈ s, ∀ i, v.val ((leftKlein a) i) = v.val i) ∧
    (∀ b ∈ t, ∀ i, v.val ((rightKlein b) i) = v.val i)

private theorem fixedWords_bound : ∀ s t : Finset (Fin 4),
    (s ≠ {0} ∨ t ≠ {0}) →
      s.card * t.card * (fixedWords s t).card ≤ 64 := by
  decide +kernel

private theorem fixed_split : ∀ (a b : Fin 4) (v : core (Fin 8)),
    (∀ i, v.val ((kleinPerm a b) i) = v.val i) ↔
      (∀ i, v.val ((leftKlein a) i) = v.val i) ∧
      (∀ i, v.val ((rightKlein b) i) = v.val i) := by
  decide +kernel


open Representation.BinaryOffender

/-- No nontrivial subgroup of the four-block radical is an offender on the core. -/
theorem core_fixed_card_bound (A : Subgroup (Equiv.Perm (Fin 8)))
    (hA : A ≤ kleinGroup) (hne : A ≠ ⊥) :
    Nat.card A * Nat.card (fixedSpace (coreRepresentation (Fin 8)) A) ≤ 64 := by
  classical
  let s : Finset (Fin 4) := Finset.univ.filter fun a => ∃ b, kleinPerm a b ∈ A
  let t : Finset (Fin 4) := Finset.univ.filter fun b => ∃ a, kleinPerm a b ∈ A
  have hs (a) : a ∈ s ↔ ∃ b, kleinPerm a b ∈ A := by simp [s]
  have ht (b) : b ∈ t ↔ ∃ a, kleinPerm a b ∈ A := by simp [t]
  have hp (x : A) : ∃ p : ↥s × ↥t,
      (x : Equiv.Perm (Fin 8)) = kleinPerm p.1 p.2 := by
    obtain ⟨a,b,he⟩ := hA x.property
    exact ⟨(⟨a,(hs a).mpr ⟨b,he ▸ x.property⟩⟩,
      ⟨b,(ht b).mpr ⟨a,he ▸ x.property⟩⟩),he⟩
  let f := fun x : A => Classical.choose (hp x)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact (Classical.choose_spec (hp x)).trans
      ((congrArg (fun p : ↥s × ↥t =>
        kleinPerm p.1 p.2) h).trans (Classical.choose_spec (hp y)).symm)
  have hcard : Nat.card A ≤ s.card * t.card := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_coe] using
      Nat.card_le_card_of_injective f hf
  have hn : s ≠ {0} ∨ t ≠ {0} := by
    by_contra! hh
    apply hne
    apply bot_unique
    intro x hx
    obtain ⟨p,hp⟩ := hp ⟨x,hx⟩
    have hl : p.1.val = 0 := by simpa only [hh.1,Finset.mem_singleton] using p.1.property
    have hr : p.2.val = 0 := by simpa only [hh.2,Finset.mem_singleton] using p.2.property
    change x = _ at hp
    rw [hp,hl,hr]
    exact one_mem _
  have hwords (v : fixedSpace (coreRepresentation (Fin 8)) A) : v.val ∈ fixedWords s t := by
    rw [fixedWords,Finset.mem_filter]
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · intro a ha
      obtain ⟨b,hb⟩ := (hs a).mp ha
      apply ((fixed_split a b v.val).mp ?_).1
      intro i
      have hv := (mem_core_fixedSpace_iff A v.val).mp v.property
        (kleinPerm a b)⁻¹ (A.inv_mem hb) i
      simpa only [Equiv.Perm.inv_def,Equiv.symm_symm] using hv
    · intro b hb
      obtain ⟨a,ha⟩ := (ht b).mp hb
      apply ((fixed_split a b v.val).mp ?_).2
      intro i
      have hv := (mem_core_fixedSpace_iff A v.val).mp v.property
        (kleinPerm a b)⁻¹ (A.inv_mem ha) i
      simpa only [Equiv.Perm.inv_def,Equiv.symm_symm] using hv
  have hfix : Nat.card (fixedSpace (coreRepresentation (Fin 8)) A) ≤ (fixedWords s t).card := by
    let j : fixedSpace (coreRepresentation (Fin 8)) A → ↥(fixedWords s t) :=
      fun v => ⟨v.val,hwords v⟩
    have hj : Function.Injective j := by
      intro x y he
      apply Subtype.ext
      exact congrArg (fun a : ↥(fixedWords s t) => a.val) he
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_le_card_of_injective j hj
  exact (Nat.mul_le_mul hcard hfix).trans (fixedWords_bound s t hn)


@[expose] noncomputable def coreAut : Equiv.Perm (Fin 8) →* MulAut (Multiplicative (core (Fin 8))) where
  toFun g := (LinearEquiv.ofBijective (coreRepresentation (Fin 8) g)
    ((coreRepresentation (Fin 8)).apply_bijective g)).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    change coreRepresentation (Fin 8) 1 v.toAdd = v.toAdd
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    change coreRepresentation (Fin 8) (g*h) v.toAdd =
      coreRepresentation (Fin 8) g (coreRepresentation (Fin 8) h v.toAdd)
    rw [map_mul,Module.End.mul_apply]

theorem coreAut_injective : Function.Injective coreAut := by
  intro g h he
  apply EightTransvectionActors.core_faithful
  apply LinearMap.ext
  intro v
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun he (Multiplicative.ofAdd v))

@[expose] noncomputable def radicalImage : Subgroup (MulAut (Multiplicative (core (Fin 8)))) :=
  kleinGroup.map coreAut

/-- The same fixed-cardinality bound on the literal automorphism image. -/
theorem core_aut_fixed_card_bound
    (A : Subgroup (MulAut (Multiplicative (core (Fin 8)))))
    (hA : A ≤ radicalImage) (hne : A ≠ ⊥) :
    Nat.card A * Nat.card {v : core (Fin 8) // ∀ a ∈ A,
      a (Multiplicative.ofAdd v) = Multiplicative.ofAdd v} ≤ 64 := by
  let B := A.comap coreAut
  have hm : B.map coreAut = A := map_comap_eq_self
    (hA.trans (map_le_range _ _))
  have hb : B ≤ kleinGroup := by
    intro b hb
    obtain ⟨x,hx,he⟩ := hA hb
    exact coreAut_injective he ▸ hx
  have hn : B ≠ ⊥ := by
    intro he
    apply hne
    rw [←hm,he,Subgroup.map_bot]
  have hc : Nat.card B = Nat.card A := by
    rw [←hm,card_map_of_injective coreAut_injective]
  have he : Nat.card {v : core (Fin 8) // ∀ a ∈ A,
      a (Multiplicative.ofAdd v) = Multiplicative.ofAdd v} =
      Nat.card (fixedSpace (coreRepresentation (Fin 8)) B) := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivProp
    funext v
    apply propext
    constructor
    · intro hv b
      exact congrArg Multiplicative.toAdd (hv _ b.property)
    · intro hv a ha
      rw [←hm] at ha
      obtain ⟨b,hb,rfl⟩ := ha
      exact congrArg Multiplicative.ofAdd (hv ⟨b,hb⟩)
  rw [he,←hc]
  exact core_fixed_card_bound B hb hn

variable {X : Type*} [Group X] [Finite X]
open Stellmacher

/-- Transport the four-block nonoffending calculation through an actual normal elementary subgroup. -/
theorem thompson_le_centralizer
    (U S : Subgroup X) [U.Normal] [IsElementaryAbelian 2 U]
    (hUS : U ≤ S) (e : U ≃* Multiplicative (core (Fin 8)))
    (a : X →* MulAut (Multiplicative (core (Fin 8))))
    (ha : ∀ x : X, ∀ u : U,
      a x (e u) = e ⟨x * u * x⁻¹, (inferInstance : U.Normal).conj_mem u u.property x⟩)
    (hk : a.ker = centralizer (U : Set X))
    (hs : S.map a ≤ radicalImage) :
    elementaryAbelianMaxJ S ≤ centralizer (U : Set X) := by
  have hU : Nat.card U = 128 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (core (Fin 8)) = 128
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),finrank_core,Nat.card_zmod,Fintype.card_fin]
    rfl
  have hfix (A : Subgroup X) (u : U) :
      (u : X) ∈ centralizer (A : Set X) ↔ ∀ x ∈ A, a x (e u) = e u := by
    constructor
    · intro hu x hx
      rw [ha]
      apply congrArg e
      apply Subtype.ext
      change x * (u : X) * x⁻¹ = (u : X)
      rw [hu x hx,mul_inv_cancel_right]
    · intro hu x hx
      have he := congrArg (fun v : U => (v : X)) (e.injective ((ha x u).symm.trans (hu x hx)))
      exact mul_inv_eq_iff_eq_mul.mp he
  have hcard (A : Subgroup X) :
      Nat.card (U ⊓ centralizer (A : Set X) : Subgroup X) =
        Nat.card {v : core (Fin 8) // ∀ b ∈ A.map a,
          b (Multiplicative.ofAdd v) = Multiplicative.ofAdd v} := by
    have hfixed (u : U) : (u : X) ∈ centralizer (A : Set X) ↔
        ∀ b ∈ A.map a, b (e u) = e u := by
      rw [hfix]
      constructor
      · rintro hh _ ⟨x,hx,rfl⟩
        exact hh x hx
      · intro hh x hx
        exact hh _ (mem_map_of_mem a hx)
    apply Nat.card_congr
    exact {
      toFun := fun u => ⟨(e ⟨u.val,u.property.1⟩).toAdd,(hfixed _).mp u.property.2⟩
      invFun := fun v => ⟨(e.symm (Multiplicative.ofAdd v.val)).val,
        (e.symm (Multiplicative.ofAdd v.val)).property,
        (hfixed _).mpr (by simpa using v.property)⟩
      left_inv := fun u => by apply Subtype.ext; simp
      right_inv := fun v => by apply Subtype.ext; simp }
  apply sSup_le
  intro A hA
  rw [←hk]
  apply (Subgroup.map_eq_bot_iff A).mp
  by_contra hn
  have hlo := maxElementary_card_le_fixed_mul_image S U A hUS hA a hk
  have hhi := core_aut_fixed_card_bound (A.map a) ((map_mono hA.1).trans hs) hn
  rw [hU,hcard,Nat.mul_comm] at hlo
  omega

end BinaryPermutation.FourBlockThompson
