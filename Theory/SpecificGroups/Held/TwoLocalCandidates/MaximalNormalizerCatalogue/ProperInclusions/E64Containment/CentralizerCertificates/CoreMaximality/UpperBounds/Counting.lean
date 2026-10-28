module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreCandidates
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.WordEvaluation
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoB
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Tables2
public import Mathlib.Order.Fin.Basic

/-!
# Counting cosets of the full Held row centralizers

Every row contains the common involution. Its centralizer is contained in the
literal row-zero conjugate of max5, whose order is already proved to be 21504.
For a list of actual row generators, a signature of their conjugation images
is constant on right centralizer cosets. Distinct signatures therefore give an
injection from the selected words times the full centralizer into that max5
conjugate. The three descendant row certificates instantiate this counting
argument with 14, 14 and 168 words respectively.

The fast evaluator uses previously kernel-certified max5 and representative
permutation tables. Its equality with the literal Held words is proved here;
no generated subgroup is substituted for the ambient centralizer.

Source: GLS3 Table 5.3p (the 2B local group), original ATLAS HeG1-p2058B0 and
HeG1-max5W1, and the literal catalogue words. See `source/README.md`.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.UpperBounds
open Subgroup LocalPairs.SylowGeometry.Calculations

@[expose] public def overgroup : Subgroup He :=
  max5.map (MulAut.conj (conjugator 0)).toMonoidHom

public theorem overgroup_card : Nat.card overgroup = 21504 := by
  exact (card_map_of_injective (K := max5)
    (f := (MulAut.conj (conjugator 0)).toMonoidHom)
    (MulAut.conj (conjugator 0)).injective).trans InvolutionFixedData.TwoB.max5_card

public theorem centralizer_le_overgroup (hp : IsPGroup 2 representative) (j : Fin 22) :
    centralizer (ambient j : Set He) ≤ overgroup :=
  (ambient_centralizer_le_common j).trans (centralWord_centralizer_le hp)

private def localLetter (k : ℤ) : max5 :=
  let x : max5 := if k.natAbs = 1 then ⟨max5First, max5First_mem⟩
    else ⟨max5Second, max5Second_mem⟩
  if k < 0 then x⁻¹ else x

public def witness (w : List ℤ) : overgroup :=
  ⟨(MulAut.conj (conjugator 0)) ((w.map localLetter).prod : max5),
    mem_map.mpr ⟨(w.map localLetter).prod, ((w.map localLetter).prod).property, rfl⟩⟩

@[expose] public def fastWitness (w : List ℤ) : Equiv.Perm (Fin 2058) :=
  let q := representation (conjugator 0)
  q * (w.map (fun k =>
    let x := if k.natAbs = 1 then Cores.Tables2.p0 else Cores.Tables2.p1
    if k < 0 then x⁻¹ else x)).prod * q⁻¹

public theorem fastWitness_eq (w : List ℤ) :
    fastWitness w = representation (witness w : He) := by
  simp only [witness, MulAut.conj_apply, map_mul, map_inv, fastWitness]
  congr 2
  change _ = (representation.comp max5.subtype) ((w.map localLetter).prod)
  rw [map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro k _
  by_cases hk : k < 0 <;> by_cases ha : k.natAbs = 1 <;>
    simp only [Function.comp_apply, localLetter, hk, ha, if_true, if_false, MonoidHom.comp_apply,
      Subgroup.subtype_apply, map_inv,
      Cores.Tables2.p0_eq, Cores.Tables2.p1_eq] <;> rfl

@[expose] public def fingerprint (tests : List (List ℤ × Fin 2058)) (g : He) : ℕ :=
  (tests.map (fun t =>
    (representation ((MulAut.conj g) (word t.1 : He)) t.2).val)).foldl
      (fun a x => 2058 * a + x) 0

@[expose] public def fastFingerprint (tests : List (List ℤ × Fin 2058))
    (g : Equiv.Perm (Fin 2058)) : ℕ :=
  (tests.map (fun t => ((g * fastWord t.1 * g⁻¹) t.2).val)).foldl
    (fun a x => 2058 * a + x) 0

public theorem fastFingerprint_eq (tests : List (List ℤ × Fin 2058)) (g : He) :
    fastFingerprint tests (representation g) = fingerprint tests g := by
  simp only [fastFingerprint, fingerprint, MulAut.conj_apply, map_mul, map_inv,
    fastWord_eq]

public theorem fingerprint_mul (j : Fin 22) (tests : List (List ℤ × Fin 2058))
    (htests : ∀ t ∈ tests, t.1 ∈ generatorWords j) (g c : He)
    (hc : c ∈ centralizer (ambient j : Set He)) :
    fingerprint tests (g * c) = fingerprint tests g := by
  unfold fingerprint
  congr 1
  apply List.map_congr_left
  intro t ht
  have hw : (word t.1 : He) ∈ ambient j :=
    mem_map.mpr ⟨word t.1, word_mem_entry j t.1 (htests t ht), rfl⟩
  have he : (MulAut.conj c) (word t.1 : He) = (word t.1 : He) := by
    rw [MulAut.conj_apply, ← hc _ hw, mul_inv_cancel_right]
  have hm : (MulAut.conj (g * c)) (word t.1 : He) =
      (MulAut.conj g) (word t.1 : He) := by
    rw [map_mul]
    exact congrArg (MulAut.conj g) he
  rw [hm]

private theorem card_le_of_separated_cosets {G : Type*} [Group G] [Finite G]
    (C M : Subgroup G) (hle : C ≤ M) {n : ℕ} (r : Fin n → M)
    (key : G → ℕ) (hkey : ∀ g c, c ∈ C → key (g * c) = key g)
    (hinj : Function.Injective (fun i => key (r i : G))) :
    n * Nat.card C ≤ Nat.card M := by
  let f : Fin n × C → M := fun z => r z.1 * ⟨z.2, hle z.2.property⟩
  have hf : Function.Injective f := by
    rintro ⟨i, c⟩ ⟨k, d⟩ he
    have he' : (r i : G) * c = (r k : G) * d := congrArg (fun x : M => (x : G)) he
    have hi : i = k := hinj (by
      have h := congrArg key he'
      rwa [hkey _ _ c.property, hkey _ _ d.property] at h)
    subst k
    have hcd : c = d := Subtype.ext (mul_left_cancel he')
    subst d
    rfl
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_injective f hf

public theorem mul_card_centralizer_le (hp : IsPGroup 2 representative)
    (j : Fin 22) (tests : List (List ℤ × Fin 2058))
    (htests : ∀ t ∈ tests, t.1 ∈ generatorWords j)
    {n : ℕ} (codes : Fin n → List ℤ)
    (hinj : Function.Injective (fun i => fingerprint tests (witness (codes i) : He))) :
    n * Nat.card (centralizer (ambient j : Set He)) ≤ 21504 := by
  have h := card_le_of_separated_cosets (centralizer (ambient j : Set He)) overgroup
    (centralizer_le_overgroup hp j) (fun i => witness (codes i)) (fingerprint tests)
    (fingerprint_mul j tests htests) hinj
  rwa [overgroup_card] at h

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.UpperBounds
