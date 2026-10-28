module

public import Theory.Representation.SixLetterRadicalDisplacement
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The marked fifteen-syntheme permutation module

The coordinate action sends each partition in `synthemeTable` to its image
under a permutation of the six letters. A finite check proves closure under
transpositions, and permutation induction proves closure under the whole group.
The resulting named homomorphism is independent of the duad action on the same
`Fin 15` alias. Explicit even transporters and the exact base stabilizer identify
these coordinates equivariantly with the left cosets of the plane parabolic,
for both `S₆` and `A₆`.

The final lemma transfers annihilation of the augmentation core to triviality
of an equivariant quotient. Finite invariant-kernel calculations belong in
separate descendants; noncentrality is required to use them as obstructions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 13.8.34, printed p.968 (PDF p.985), using
13.8.4(5),(6). The syntheme tables are those of `SymmetricSix.Parabolics`.
-/

@[expose] public section

open BinaryPermutation Representation Module
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace Representation.SixLetterRadicalDisplacement.PermutationQuotients
set_option maxRecDepth 4096

/-- The partition represented by an entry of the published syntheme table. -/
def partition (s : Fin 15) : Finset (Finset (Fin 6)) :=
  (synthemeDuads s).image duadSet

theorem partition_injective : Function.Injective partition := by decide

private theorem partition_swap (i j : Fin 6) (s : Fin 15) :
    ∃ t : Fin 15, partition t = Equiv.swap i j • partition s := by
  decide +revert

private theorem partition_perm (g : S) (s : Fin 15) :
    ∃ t : Fin 15, partition t = g • partition s := by
  induction g using Equiv.Perm.swap_induction_on with
  | one => exact ⟨s, (one_smul _ _).symm⟩
  | swap_mul g i j _ ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨u, hu⟩ := partition_swap i j t
    exact ⟨u, by rw [hu, ht, mul_smul]⟩

/-- Computable action on syntheme indices; no action on the `Fin 15` alias is inferred. -/
def act (g : S) (s : Fin 15) : Fin 15 :=
  Fin.find (fun t => partition t = g • partition s) (by exact partition_perm g s)

theorem partition_act (g : S) (s : Fin 15) :
    partition (act g s) = g • partition s := Fin.find_spec (partition_perm g s)

@[simp] theorem act_one (s : Fin 15) : act 1 s = s := by
  apply partition_injective
  simp [partition_act]

@[simp] theorem act_mul (g h : S) (s : Fin 15) : act (g * h) s = act g (act h s) := by
  apply partition_injective
  simp only [partition_act, mul_smul]

/-- The actual fifteen-syntheme permutation homomorphism. -/
def synthemeHom : S →* Equiv.Perm (Fin 15) where
  toFun g :=
    { toFun := act g
      invFun := act g⁻¹
      left_inv s := by rw [← act_mul, inv_mul_cancel, act_one]
      right_inv s := by rw [← act_mul, mul_inv_cancel, act_one] }
  map_one' := by apply _root_.Equiv.ext; exact act_one
  map_mul' g h := by apply _root_.Equiv.ext; exact act_mul g h

@[simp] theorem synthemeHom_apply (g : S) (s : Fin 15) : synthemeHom g s = act g s := rfl

/-- The marked permutation module. -/
abbrev P := Full (Fin 15)
/-- Its augmentation submodule. -/
abbrev P0 := core (Fin 15)
/-- The binary representation uses the named syntheme homomorphism explicitly. -/
def rho : Representation (ZMod 2) S P :=
  (BinaryPermutation.representation (Fin 15)).comp synthemeHom

@[simp] theorem rho_apply (g : S) (v : P) (s : Fin 15) :
    rho g v s = v (act g⁻¹ s) := rfl

/-- The zero syntheme is the plane parabolic in the natural marking. -/
theorem stabilizer_zero (g : S) : act g 0 = 0 ↔ g ∈ H2 := by
  rw [← partition_injective.eq_iff, partition_act]
  change g • partition 0 = partition 0 ↔ g • baseSyntheme = baseSyntheme
  rfl

/-- Equality in the orbit is exactly equality of left cosets of the marked parabolic. -/
theorem act_zero_eq_iff (g h : S) : act g 0 = act h 0 ↔ g⁻¹ * h ∈ H2 := by
  rw [← stabilizer_zero, act_mul]
  constructor
  · intro he
    rw [← he, ← act_mul, inv_mul_cancel, act_one]
  · intro he
    have := congrArg (act g) he
    simpa only [← act_mul, mul_inv_cancel_left] using this.symm


private def representative : Fin 15 → S :=
  ![1,
    Equiv.swap 3 5 * Equiv.swap 3 4,
    Equiv.swap 4 3 * Equiv.swap 3 5,
    Equiv.swap 4 5 * Equiv.swap 1 2,
    Equiv.swap 3 4 * Equiv.swap 1 2,
    Equiv.swap 3 5 * Equiv.swap 1 2,
    Equiv.swap 2 1 * Equiv.swap 1 3,
    Equiv.swap 2 5 * Equiv.swap 2 4 * Equiv.swap 2 1 * Equiv.swap 1 3,
    Equiv.swap 4 2 * Equiv.swap 2 5 * Equiv.swap 2 1 * Equiv.swap 1 3,
    Equiv.swap 3 5 * Equiv.swap 3 2 * Equiv.swap 2 1 * Equiv.swap 1 4,
    Equiv.swap 2 1 * Equiv.swap 1 4,
    Equiv.swap 2 3 * Equiv.swap 3 5 * Equiv.swap 2 1 * Equiv.swap 1 4,
    Equiv.swap 4 3 * Equiv.swap 3 2 * Equiv.swap 2 1 * Equiv.swap 1 5,
    Equiv.swap 2 1 * Equiv.swap 1 5,
    Equiv.swap 3 2 * Equiv.swap 3 4 * Equiv.swap 2 1 * Equiv.swap 1 5]

private theorem representative_even (s : Fin 15) :
    representative s ∈ alternatingGroup (Fin 6) := by decide +revert

private theorem representative_act (s : Fin 15) : act (representative s) 0 = s := by
  apply partition_injective
  rw [partition_act]
  decide +revert

/-- Every syntheme is reached even by an alternating permutation. -/
theorem alternating_transitive (s : Fin 15) :
    ∃ g : alternatingGroup (Fin 6), act g.val 0 = s :=
  ⟨⟨representative s, representative_even s⟩, representative_act s⟩

/-- The coordinate synthemes are the actual left cosets of the marked parabolic. -/
def cosetMap : S ⧸ H2 → Fin 15 :=
  Quotient.lift (fun g => act g 0) (fun a b h =>
    (act_zero_eq_iff a b).mpr (QuotientGroup.leftRel_apply.mp h))

@[simp] theorem cosetMap_mk (g : S) : cosetMap (g : S ⧸ H2) = act g 0 := rfl

theorem cosetMap_bijective : Function.Bijective cosetMap := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        intro hab
        exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((act_zero_eq_iff a b).mp hab))
  · intro s
    exact ⟨(representative s : S ⧸ H2), representative_act s⟩

noncomputable def cosetEquiv : S ⧸ H2 ≃ Fin 15 := Equiv.ofBijective cosetMap cosetMap_bijective

@[simp] theorem cosetEquiv_mk (g : S) : cosetEquiv (g : S ⧸ H2) = act g 0 := rfl

theorem cosetEquiv_equivariant (g : S) (x : S ⧸ H2) :
    cosetEquiv (g • x) = synthemeHom g (cosetEquiv x) := by
  induction x using Quotient.inductionOn with | h h =>
    rw [MulAction.Quotient.smul_coe, cosetEquiv_mk, cosetEquiv_mk, synthemeHom_apply]
    exact act_mul g h 0

/-- Intrinsic alternating radical; its ambient image is the published `D0`. -/
abbrev alternatingRadical : Subgroup (alternatingGroup (Fin 6)) :=
  D.comap (alternatingGroup (Fin 6)).subtype

theorem mem_alternatingRadical (g : alternatingGroup (Fin 6)) :
    g ∈ alternatingRadical ↔ g.val ∈ D0 := by
  change g.val ∈ D ↔ g.val ∈ D ∧ g.val ∈ alternatingGroup (Fin 6)
  exact ⟨fun h => ⟨h, g.property⟩, And.left⟩

/-- The same coordinate model with the actor restricted to `A₆`. -/
def rhoA : Representation (ZMod 2) (alternatingGroup (Fin 6)) P :=
  rho.comp (alternatingGroup (Fin 6)).subtype

/-- Alternating cosets have the same marked coordinate set. -/
def alternatingCosetMap : alternatingGroup (Fin 6) ⧸ a6SynthemeStabilizer → Fin 15 :=
  Quotient.lift (fun g => act g.val 0) (fun a b h =>
    (act_zero_eq_iff a.val b.val).mpr (show a⁻¹ * b ∈ a6SynthemeStabilizer from
      QuotientGroup.leftRel_apply.mp h))

theorem alternatingCosetMap_bijective : Function.Bijective alternatingCosetMap := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        intro hab
        exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((act_zero_eq_iff a.val b.val).mp hab))
  · intro s
    obtain ⟨g, hg⟩ := alternating_transitive s
    exact ⟨(g : alternatingGroup (Fin 6) ⧸ a6SynthemeStabilizer), hg⟩

noncomputable def alternatingCosetEquiv :
    alternatingGroup (Fin 6) ⧸ a6SynthemeStabilizer ≃ Fin 15 :=
  Equiv.ofBijective alternatingCosetMap alternatingCosetMap_bijective

@[simp] theorem alternatingCosetEquiv_mk (g : alternatingGroup (Fin 6)) :
    alternatingCosetEquiv (g : alternatingGroup (Fin 6) ⧸ a6SynthemeStabilizer) = act g.val 0 := rfl

theorem alternatingCosetEquiv_equivariant (g : alternatingGroup (Fin 6))
    (x : alternatingGroup (Fin 6) ⧸ a6SynthemeStabilizer) :
    alternatingCosetEquiv (g • x) = synthemeHom g.val (alternatingCosetEquiv x) := by
  induction x using Quotient.inductionOn with | h h =>
    rw [MulAction.Quotient.smul_coe, alternatingCosetEquiv_mk,
      alternatingCosetEquiv_mk, synthemeHom_apply]
    exact act_mul g.val h.val 0

/-- Binary row encoding used by finite, kernel-checked certificates. -/
def row (n : ℕ) : P := fun i => if n.testBit i.val then 1 else 0

theorem P0_finrank : finrank (ZMod 2) P0 = 14 := finrank_core (Fin 15)

theorem difference_mem_P0 (g : S) (v : P) : rho g v - v ∈ P0 := by
  change augmentation (Fin 15) (rho g v - v) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (augmentation_permute (Fin 15) (synthemeHom g) v)

/-- Killing the augmentation core makes every equivariant quotient central.
The actor map allows both the symmetric action and its alternating restriction. -/
theorem quotient_trivial_of_core_le_ker {G Q : Type*} [Group G]
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (φ : G →* S) (σ : Representation (ZMod 2) G Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f)
    (heq : ∀ g v, f (rho (φ g) v) = σ g (f v))
    (hker : P0 ≤ f.ker) : ∀ g v, σ g v = v := by
  intro g v
  obtain ⟨u,rfl⟩ := hf v
  have h := hker (difference_mem_P0 (φ g) u)
  change f (rho (φ g) u - u) = 0 at h
  rw [map_sub, heq] at h
  exact sub_eq_zero.mp h

end Representation.SixLetterRadicalDisplacement.PermutationQuotients
