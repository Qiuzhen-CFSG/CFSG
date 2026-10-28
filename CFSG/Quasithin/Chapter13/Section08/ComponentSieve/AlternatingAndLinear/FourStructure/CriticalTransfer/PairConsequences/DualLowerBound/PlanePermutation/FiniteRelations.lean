module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.DualLowerBound.PlanePermutation.Model
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.DualLowerBound.PlanePermutation.Relations
public import Mathlib.FieldTheory.Finiteness


/-!
# Centralizer relations for the binary four-space plane action

For each of the two marked involutions of GL₄(2), the centralizer relation
space contains every difference of two plane basis vectors. In particular it
contains the involution's entire displacement space.

The certificate uses the actual submodules of `Fin 4 → ZMod 2`. Its 35 rows
list their four vectors as binary masks. Closure and distinctness give each
row dimension two; conversely, the two vectors of a basis of any plane occur
in one row, proving that the catalogue covers every plane.

With `Q = span{e₁,e₃}` and `c = root 2 3`, the two column matrices
`h = (8,10,6,7)` and `k = (15,10,6,7)` translate the centralizer relation
into two expressions with three common terms. Subtracting them gives the
difference of `span{e₀,e₁}` and `span{e₀,e₂}` (with the subtraction reversed
for the second involution). A table of 34 invertible maps transports this
difference along a spanning tree of the catalogue. Every finite assertion
is checked by kernel reduction; no external computation is trusted.

This supplies the finite-model input for the permutation quotient in
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), 13.8.4(5), printed p.947, its use in 13.8.11(1), p.950, and
the plane-parabolic identification in 13.8.25, pp.960–962.
-/

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.PlanePermutation
namespace FiniteCertificate

-- A mask uses the coefficient of e_i as its ith binary digit.
def vector (n : Fin 16) : Space :=
  ![(n.val : ZMod 2), ((n.val / 2 : ℕ) : ZMod 2),
    ((n.val / 4 : ℕ) : ZMod 2), ((n.val / 8 : ℕ) : ZMod 2)]

def rows : Fin 35 → Fin 4 → Fin 16 :=
  ![![0, 1, 2, 3],
    ![0, 1, 4, 5],
    ![0, 1, 6, 7],
    ![0, 1, 8, 9],
    ![0, 1, 10, 11],
    ![0, 1, 12, 13],
    ![0, 1, 14, 15],
    ![0, 2, 4, 6],
    ![0, 2, 5, 7],
    ![0, 2, 8, 10],
    ![0, 2, 9, 11],
    ![0, 2, 12, 14],
    ![0, 2, 13, 15],
    ![0, 3, 4, 7],
    ![0, 3, 5, 6],
    ![0, 3, 8, 11],
    ![0, 3, 9, 10],
    ![0, 3, 12, 15],
    ![0, 3, 13, 14],
    ![0, 4, 8, 12],
    ![0, 4, 9, 13],
    ![0, 4, 10, 14],
    ![0, 4, 11, 15],
    ![0, 5, 8, 13],
    ![0, 5, 9, 12],
    ![0, 5, 10, 15],
    ![0, 5, 11, 14],
    ![0, 6, 8, 14],
    ![0, 6, 9, 15],
    ![0, 6, 10, 12],
    ![0, 6, 11, 13],
    ![0, 7, 8, 15],
    ![0, 7, 9, 14],
    ![0, 7, 10, 13],
    ![0, 7, 11, 12]]

def Contains (i : Fin 35) (v : Space) : Prop := ∃ j, vector (rows i j) = v
instance (i : Fin 35) (v : Space) : Decidable (Contains i v) := inferInstanceAs (Decidable (∃ j, vector (rows i j) = v))

theorem closed : ∀ i : Fin 35,
    Contains i 0 ∧ (∀ j k : Fin 4,
      Contains i (vector (rows i j) + vector (rows i k))) := by
  intro i
  fin_cases i <;> decide +kernel

def subspace (i : Fin 35) : Submodule (ZMod 2) Space where
  carrier := Contains i
  zero_mem' := (closed i).1
  add_mem' := by
    rintro _ _ ⟨j, rfl⟩ ⟨k, rfl⟩
    exact (closed i).2 j k
  smul_mem' := by
    intro a v hv
    change Contains i (a • v)
    change Contains i v at hv
    have ha : a = 0 ∨ a = 1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
    rcases ha with rfl | rfl
    · simpa using (closed i).1
    · simpa using hv

theorem rows_injective : ∀ i : Fin 35, Function.Injective (fun j => vector (rows i j)) := by
  intro i
  fin_cases i <;> decide +kernel

noncomputable def rowEquiv (i : Fin 35) : Fin 4 ≃ subspace i := Equiv.ofBijective
  (fun j => ⟨vector (rows i j), ⟨j, rfl⟩⟩)
  ⟨fun _ _ h => rows_injective i (congrArg Subtype.val h), fun ⟨_, j, hj⟩ => ⟨j, Subtype.ext hj⟩⟩

theorem subspace_finrank (i : Fin 35) : Module.finrank (ZMod 2) (subspace i) = 2 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := subspace i)
  rw [← Nat.card_congr (rowEquiv i), Nat.card_fin, Nat.card_eq_fintype_card, ZMod.card] at h
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) h.symm

def plane (i : Fin 35) : Plane := ⟨subspace i, subspace_finrank i⟩

theorem vector_surjective : Function.Surjective vector := by
  intro v
  have he : v = ![v 0, v 1, v 2, v 3] := by ext i; fin_cases i <;> rfl
  rw [he]
  generalize v 0 = a, v 1 = b, v 2 = c, v 3 = d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide +kernel

theorem pair_covered : ∀ v w : Space, ∃ i : Fin 35, Contains i v ∧ Contains i w := by
  have hc : ∀ a b : Fin 16, ∃ i : Fin 35,
      Contains i (vector a) ∧ Contains i (vector b) := by
    intro a
    fin_cases a <;> decide +kernel
  intro v w
  obtain ⟨a, rfl⟩ := vector_surjective v
  obtain ⟨b, rfl⟩ := vector_surjective w
  exact hc a b

theorem plane_surjective : Function.Surjective plane := by
  intro P
  let b := Module.finBasisOfFinrankEq (ZMod 2) P.val P.property
  obtain ⟨i, hi0, hi1⟩ := pair_covered (b 0).val (b 1).val
  refine ⟨i, Subtype.ext ?_⟩
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq ?_ (P.property.trans (subspace_finrank i).symm)
  intro x hx
  have he := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
  rw [Fin.sum_univ_two] at he
  change (b.repr ⟨x, hx⟩ 0) • (b 0).val + (b.repr ⟨x, hx⟩ 1) • (b 1).val = x at he
  rw [← he]
  exact (subspace i).add_mem ((subspace i).smul_mem _ hi0) ((subspace i).smul_mem _ hi1)

-- A column matrix is interpreted on the actual coordinate space.
def linear (m : Fin 4 → Fin 16) : Space →ₗ[ZMod 2] Space :=
  Matrix.mulVecLin (fun i j => vector (m j) i)

noncomputable def actor (m : Fin 4 → Fin 16) (hm : Function.Bijective (linear m)) : Actor :=
  LinearEquiv.ofBijective (linear m) hm

theorem smul_plane_eq (g : Actor) {i j : Fin 35}
    (h : ∀ k : Fin 4, Contains j (g (vector (rows i k)))) :
    g • plane i = plane j := by
  apply Subtype.ext
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v, ⟨k, rfl⟩, rfl⟩
    exact h k
  · change Module.finrank (ZMod 2) ((subspace i).map g.toLinearMap) =
      Module.finrank (ZMod 2) (subspace j)
    rw [g.finrank_map_eq, subspace_finrank, subspace_finrank]

def hColumns : Fin 4 → Fin 16 := ![8, 10, 6, 7]
def kColumns : Fin 4 → Fin 16 := ![15, 10, 6, 7]

theorem h_bijective : Function.Bijective (linear hColumns) := by decide +kernel
theorem k_bijective : Function.Bijective (linear kColumns) := by decide +kernel
noncomputable def hActor : Actor := actor hColumns h_bijective
noncomputable def kActor : Actor := actor kColumns k_bijective

def cActor : Actor := root 2 3 (by decide)

theorem c_commutes_first : Commute cActor firstInvolution := firstInvolution_commute_root.symm

theorem c_commutes_second : Commute cActor secondInvolution :=
  c_commutes_first.mul_right (Commute.refl cActor)

-- The four entries are c*t*Q, c*Q, t*Q, Q, after each of the two translations.
theorem first_images_h :
    (hActor * cActor * firstInvolution) • plane 9 = plane 0 ∧
    (hActor * cActor) • plane 9 = plane 4 ∧
    (hActor * firstInvolution) • plane 9 = plane 8 ∧
    hActor • plane 9 = plane 33 := by
  refine ⟨smul_plane_eq _ ?_, smul_plane_eq _ ?_, smul_plane_eq _ ?_, smul_plane_eq _ ?_⟩ <;>
    decide +kernel

theorem first_images_k :
    (kActor * cActor * firstInvolution) • plane 9 = plane 1 ∧
    (kActor * cActor) • plane 9 = plane 4 ∧
    (kActor * firstInvolution) • plane 9 = plane 8 ∧
    kActor • plane 9 = plane 33 := by
  refine ⟨smul_plane_eq _ ?_, smul_plane_eq _ ?_, smul_plane_eq _ ?_, smul_plane_eq _ ?_⟩ <;>
    decide +kernel

theorem second_images_h :
    (hActor * cActor * secondInvolution) • plane 9 = plane 8 ∧
    (hActor * secondInvolution) • plane 9 = plane 0 := by
  refine ⟨smul_plane_eq _ ?_, smul_plane_eq _ ?_⟩ <;> decide +kernel

theorem second_images_k :
    (kActor * cActor * secondInvolution) • plane 9 = plane 8 ∧
    (kActor * secondInvolution) • plane 9 = plane 1 := by
  refine ⟨smul_plane_eq _ ?_, smul_plane_eq _ ?_⟩ <;> decide +kernel

theorem seed_first :
    Finsupp.single (plane 0) 1 - Finsupp.single (plane 1) 1 ∈
      centralizerRelations (X := Plane) firstInvolution := by
  have hh : relation firstInvolution hActor cActor (plane 9) ∈
      centralizerRelations (X := Plane) firstInvolution :=
    Submodule.subset_span ⟨hActor, cActor, c_commutes_first, plane 9, rfl⟩
  have hk : relation firstInvolution kActor cActor (plane 9) ∈
      centralizerRelations (X := Plane) firstInvolution :=
    Submodule.subset_span ⟨kActor, cActor, c_commutes_first, plane 9, rfl⟩
  convert (centralizerRelations (X := Plane) firstInvolution).sub_mem hh hk using 1
  simp only [relation, ← mul_smul, ← mul_assoc, first_images_h.1, first_images_h.2.1,
    first_images_h.2.2.1, first_images_h.2.2.2, first_images_k.1, first_images_k.2.1,
    first_images_k.2.2.1, first_images_k.2.2.2]
  abel

theorem seed_second :
    Finsupp.single (plane 0) 1 - Finsupp.single (plane 1) 1 ∈
      centralizerRelations (X := Plane) secondInvolution := by
  have hh : relation secondInvolution hActor cActor (plane 9) ∈
      centralizerRelations (X := Plane) secondInvolution :=
    Submodule.subset_span ⟨hActor, cActor, c_commutes_second, plane 9, rfl⟩
  have hk : relation secondInvolution kActor cActor (plane 9) ∈
      centralizerRelations (X := Plane) secondInvolution :=
    Submodule.subset_span ⟨kActor, cActor, c_commutes_second, plane 9, rfl⟩
  convert (centralizerRelations (X := Plane) secondInvolution).sub_mem hk hh using 1
  simp only [relation, ← mul_smul, ← mul_assoc, second_images_h.1, first_images_h.2.1,
    second_images_h.2, first_images_h.2.2.2, second_images_k.1, first_images_k.2.1,
    second_images_k.2, first_images_k.2.2.2]
  abel

def edgeColumns : Fin 34 → Fin 4 → Fin 16 :=
  ![![1, 4, 2, 8],
    ![1, 6, 2, 8],
    ![1, 8, 2, 4],
    ![1, 10, 2, 4],
    ![1, 12, 2, 4],
    ![1, 14, 2, 4],
    ![2, 4, 1, 8],
    ![2, 5, 1, 8],
    ![2, 8, 1, 4],
    ![2, 9, 1, 4],
    ![2, 12, 1, 4],
    ![2, 13, 1, 4],
    ![3, 4, 1, 8],
    ![3, 5, 1, 8],
    ![3, 8, 1, 4],
    ![3, 9, 1, 4],
    ![3, 12, 1, 4],
    ![3, 13, 1, 4],
    ![4, 8, 1, 2],
    ![4, 9, 1, 2],
    ![4, 10, 1, 2],
    ![4, 11, 1, 2],
    ![5, 8, 1, 2],
    ![5, 9, 1, 2],
    ![5, 10, 1, 2],
    ![5, 11, 1, 2],
    ![6, 8, 1, 2],
    ![6, 9, 1, 2],
    ![6, 10, 1, 2],
    ![6, 11, 1, 2],
    ![7, 8, 1, 2],
    ![7, 9, 1, 2],
    ![7, 10, 1, 2],
    ![7, 11, 1, 2]]

def parent : Fin 34 → Fin 35 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2]

def edgeInverse : Fin 34 → Fin 4 → Fin 16 :=
  ![![1, 4, 2, 8],
    ![1, 4, 6, 8],
    ![1, 4, 8, 2],
    ![1, 4, 8, 6],
    ![1, 4, 8, 10],
    ![1, 4, 8, 14],
    ![4, 1, 2, 8],
    ![4, 1, 6, 8],
    ![4, 1, 8, 2],
    ![4, 1, 8, 6],
    ![4, 1, 8, 10],
    ![4, 1, 8, 14],
    ![4, 5, 2, 8],
    ![4, 5, 6, 8],
    ![4, 5, 8, 2],
    ![4, 5, 8, 6],
    ![4, 5, 8, 10],
    ![4, 5, 8, 14],
    ![4, 8, 1, 2],
    ![4, 8, 1, 6],
    ![4, 8, 1, 10],
    ![4, 8, 1, 14],
    ![4, 8, 5, 2],
    ![4, 8, 5, 6],
    ![4, 8, 5, 10],
    ![4, 8, 5, 14],
    ![4, 8, 9, 2],
    ![4, 8, 9, 6],
    ![4, 8, 9, 10],
    ![4, 8, 9, 14],
    ![4, 8, 13, 2],
    ![4, 8, 13, 6],
    ![4, 8, 13, 10],
    ![4, 8, 13, 14]]

theorem bijective_of_left_inverse (m n : Fin 4 → Fin 16)
    (h : ∀ a : Fin 16, linear n (linear m (vector a)) = vector a) :
    Function.Bijective (linear m) := by
  have hl : Function.LeftInverse (linear n) (linear m) := by
    intro v
    obtain ⟨a, rfl⟩ := vector_surjective v
    exact h a
  exact ⟨hl.injective, (Finite.injective_iff_surjective).mp hl.injective⟩

theorem edge_left_inverse : ∀ (i : Fin 34) (a : Fin 16),
    linear (edgeInverse i) (linear (edgeColumns i) (vector a)) = vector a := by
  intro i
  fin_cases i <;> decide +kernel

noncomputable def edgeActor (i : Fin 34) : Actor :=
  actor (edgeColumns i) (bijective_of_left_inverse _ _ (edge_left_inverse i))

theorem edge_images : ∀ i : Fin 34,
    edgeActor i • plane 0 = plane i.succ ∧
    edgeActor i • plane 1 = plane (parent i) := by
  have hc : ∀ (i : Fin 34) (k : Fin 4),
      Contains i.succ (linear (edgeColumns i) (vector (rows 0 k))) ∧
      Contains (parent i) (linear (edgeColumns i) (vector (rows 1 k))) := by
    intro i
    fin_cases i <;> decide +kernel
  intro i
  exact ⟨smul_plane_eq _ (fun k => (hc i k).1), smul_plane_eq _ (fun k => (hc i k).2)⟩

theorem parent_lt : ∀ i : Fin 34, (parent i).val < i.succ.val := by decide +kernel

-- Transport the seed difference along the checked spanning tree.
theorem differences_from_zero (t : Actor)
    (hs : Finsupp.single (plane 0) 1 - Finsupp.single (plane 1) 1 ∈
      centralizerRelations (X := Plane) t) (i : Fin 35) :
    Finsupp.single (plane i) 1 - Finsupp.single (plane 0) 1 ∈
      centralizerRelations (X := Plane) t := by
  have h : ∀ (n : ℕ) (hn : n < 35),
      Finsupp.single (plane ⟨n, hn⟩) 1 - Finsupp.single (plane 0) 1 ∈
        centralizerRelations (X := Plane) t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hz : n = 0
      · subst n
        simp
      let e : Fin 34 := ⟨n - 1, by omega⟩
      have he : e.succ = ⟨n, hn⟩ := by ext; dsimp [e]; omega
      have hp : (parent e).val < n := by
        have hh := parent_lt e
        rw [he] at hh
        exact hh
      have hab := difference_mem_of_translate t (edgeActor e) hs
      rw [(edge_images e).1, (edge_images e).2, he] at hab
      exact difference_mem_trans t hab (ih (parent e).val hp (parent e).isLt)
  exact h i.val i.isLt

theorem all_differences (t : Actor)
    (hs : Finsupp.single (plane 0) 1 - Finsupp.single (plane 1) 1 ∈
      centralizerRelations (X := Plane) t) (P Q : Plane) :
    Finsupp.single P 1 - Finsupp.single Q 1 ∈ centralizerRelations (X := Plane) t := by
  obtain ⟨i, rfl⟩ := plane_surjective P
  obtain ⟨j, rfl⟩ := plane_surjective Q
  convert (centralizerRelations (X := Plane) t).sub_mem
    (differences_from_zero t hs i) (differences_from_zero t hs j) using 1
  abel

end FiniteCertificate

/-- The rank-one natural involution has all plane displacements in its centralizer relations. -/
public theorem first_displacementRelations : DisplacementRelations (X := Plane) firstInvolution := by
  intro P
  exact FiniteCertificate.all_differences firstInvolution FiniteCertificate.seed_first _ _

/-- The rank-two natural involution has all plane displacements in its centralizer relations. -/
public theorem second_displacementRelations : DisplacementRelations (X := Plane) secondInvolution := by
  intro P
  exact FiniteCertificate.all_differences secondInvolution FiniteCertificate.seed_second _ _

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.PlanePermutation
