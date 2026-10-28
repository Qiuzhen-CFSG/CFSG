module

public import CFSG.Quasithin.ChapterI.Section06To08.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.NoncommCoprod

/-!
# Elementary TI-pair structure

The first steps of Aschbacher--Smith I.6.2 identify the trivial intersection of
the two distinct TI-subgroups and the commutation of their mutual normalizers.
The latter follows because a commutator of mutual normalizer elements lies in
both subgroups.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma I.6.2, printed pp. 424--425.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterI.Section06To08

variable {G : Type*} [Group G]

/-- Distinctness is needed here: the literal case `V = A` in the printed
statement does not have trivial intersection. -/
theorem ti_pair_disjoint_of_distinct (V A : Subgroup G) (hVA : V ≠ A)
    (hcross : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≠ V →
      Disjoint (A.map (MulAut.conj g).toMonoidHom) V) : Disjoint V A := by
  have hmap : A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
    have hhom : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [hhom, Subgroup.map_id]
  have h := hcross 1 (by rw [hmap]; exact hVA.symm)
  rw [hmap] at h
  exact h.symm

/-- Elements lying in both mutual normalizers commute when the subgroups are
disjoint. -/
theorem ti_pair_commute_of_mutual_normalizers (V A : Subgroup G)
    (hVA : Disjoint V A) {u a : G} (huV : u ∈ V)
    (huA : u ∈ Subgroup.normalizer (A : Set G)) (haA : a ∈ A)
    (haV : a ∈ Subgroup.normalizer (V : Set G)) : Commute u a := by
  have hA : u * a * u⁻¹ * a⁻¹ ∈ A :=
    A.mul_mem ((Subgroup.mem_normalizer_iff.mp huA a).mp haA) (A.inv_mem haA)
  have hV : u * a * u⁻¹ * a⁻¹ ∈ V := by
    have h : a * u * a⁻¹ * u⁻¹ ∈ V :=
      V.mul_mem ((Subgroup.mem_normalizer_iff.mp haV u).mp huV) (V.inv_mem huV)
    convert V.inv_mem h using 1; group
  have hcomm : u * a * u⁻¹ * a⁻¹ = 1 := hVA.le_bot ⟨hV, hA⟩
  change u * a = a * u
  calc
    u * a = (u * a * u⁻¹ * a⁻¹) * (a * u) := by group
    _ = a * u := by rw [hcomm, one_mul]

/-- A nonidentity element of `N_V(A)` detects exactly `N_A(V)` by
centralization. -/
theorem ti_pair_opposite_normalizer_eq_centralizer (V A : Subgroup G)
    (hVA : Disjoint V A) (hV : IsTISubgroup V)
    {u : G} (huV : u ∈ V) (huA : u ∈ Subgroup.normalizer (A : Set G))
    (hu1 : u ≠ 1) :
    A ⊓ Subgroup.normalizer (V : Set G) =
      A ⊓ Subgroup.centralizer ({u} : Set G) := by
  apply le_antisymm
  · intro a ha
    refine ⟨ha.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (ti_pair_commute_of_mutual_normalizers V A hVA huV huA ha.1 ha.2).symm
  · intro a ha
    exact ⟨ha.1, (hV.centralizer_le_normalizer huV hu1) ha.2⟩

/-- The two mutual normalizers centralize each other. -/
theorem ti_pair_mutual_normalizers_commute (V A : Subgroup G)
    (hVA : Disjoint V A) :
    V ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.centralizer ((A ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) : Set G) := by
  intro u hu a ha
  exact (ti_pair_commute_of_mutual_normalizers V A hVA hu.1 hu.2 ha.1 ha.2).symm

/-- Multiplication realizes `Y = U B` as an internal direct product, retaining
the specified embeddings of both factors. -/
theorem ti_pair_mutual_normalizers_mulEquiv (V A : Subgroup G)
    (hVA : Disjoint V A) :
    let U := V ⊓ Subgroup.normalizer (A : Set G)
    let B := A ⊓ Subgroup.normalizer (V : Set G)
    ∃ e : U × B ≃* ↥(U ⊔ B),
      ∀ u b, (e (u, b) : G) = (u : G) * (b : G) := by
  dsimp
  let U := V ⊓ Subgroup.normalizer (A : Set G)
  let B := A ⊓ Subgroup.normalizer (V : Set G)
  have hdisj : Disjoint U B := hVA.mono inf_le_left inf_le_left
  have hc : ∀ u : U, ∀ b : B, Commute (u : G) (b : G) := by
    intro u b
    exact (ti_pair_commute_of_mutual_normalizers V A hVA u.property.1
      u.property.2 b.property.1 b.property.2)
  let f : U × B →* G := U.subtype.noncommCoprod B.subtype hc
  have hfr : f.range = U ⊔ B := by
    simpa only [Subgroup.subtype_range] using
      (MonoidHom.noncommCoprod_range U.subtype B.subtype hc)
  let g : U × B →* ↥(U ⊔ B) := f.codRestrict (U ⊔ B) (fun x => hfr ▸ ⟨x, rfl⟩)
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      exact Subgroup.mul_injective_of_disjoint hdisj (congrArg Subtype.val hxy)
    · intro c
      have hc : (c : G) ∈ f.range := by rw [hfr]; exact c.property
      obtain ⟨x, hx⟩ := hc
      exact ⟨x, Subtype.ext hx⟩
  exact ⟨MulEquiv.ofBijective g hg, fun _ _ => rfl⟩

end CFSG.Quasithin.ChapterI.Section06To08
