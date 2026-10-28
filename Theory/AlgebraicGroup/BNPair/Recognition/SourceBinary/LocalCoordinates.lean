module
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.SolvableRadical
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# A perfect rank-one subgroup lies in a single product coordinate

A proper Sylow normalizer containing every proper Sylow overgroup normally
generates the local group by Frattini's argument. In a perfect local group,
every proper normal subgroup is solvable: adjoining its Sylow subgroup stays
proper, since a perfect two-group quotient is trivial.

Now embed such a nontrivial perfect group A in a finite direct product,
normalized by a full Sylow subgroup of that product. If every coordinate
intersection is proper, it lies in the solvable radical of A. Each coordinate
fragment of a local Sylow element belongs to the full ambient Sylow. Its
commutators with A lie in the corresponding coordinate intersection.
Consequently the local Sylow is central modulo the radical. Normal generation
makes that quotient abelian, contradicting nontrivial perfectness.

This elementary reduction supplies the single-component step in the perfect
branch of the Fong–Seitz invocation in DGS, Groups and Graphs, Part II,
pp.80–81 and224. It uses no classification of the product factors. The full
ambient Sylow normalization is essential; diagonal Sylow normalization does
not suffice. The Sylow product calculation follows the proof in
Theory.GroupTheory.SylowNormalizerCommutingFamily.FactorControl.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary

variable {A : Type*} [Group A] [Finite A]

/-- A unique proper Sylow normalizer forces normal generation by that Sylow. -/
theorem local_normalClosure_eq_top (T : Sylow 2 A)
    (hproper : normalizer (T : Set A) < ⊤)
    (hunique : ∀ M : Subgroup A, (T : Subgroup A) ≤ M → M < ⊤ →
      M ≤ normalizer (T : Set A)) : normalClosure (T : Set A) = ⊤ := by
  by_contra hn
  have hT : (T : Subgroup A) ≤ normalClosure (T : Set A) := le_normalClosure
  have hle := hunique _ hT (lt_top_iff_ne_top.mpr hn)
  exact hproper.ne (top_unique ((T.normalizer_sup_eq_top' hT) ▸ sup_le le_rfl hle))

/-- Every proper normal subgroup of the perfect local group is solvable. -/
theorem local_proper_normal_solvable [Group.IsPerfect A] (T : Sylow 2 A)
    (hunique : ∀ M : Subgroup A, (T : Subgroup A) ≤ M → M < ⊤ →
      M ≤ normalizer (T : Set A))
    (hsolv : Group.IsSolvable (normalizer (T : Set A)))
    (N : Subgroup A) [N.Normal] (hN : N ≠ ⊤) : Group.IsSolvable N := by
  have hNT : N ⊔ (T : Subgroup A) ≠ ⊤ := by
    intro he
    have hp := isPGroup_quotient_of_sup_eq_top N T T.isPGroup' he
    let : Group.IsNilpotent (A ⧸ N) := hp.isNilpotent
    exact hN (top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N))
  have hle : N ≤ normalizer (T : Set A) :=
    le_sup_left.trans (hunique _ le_sup_right (lt_top_iff_ne_top.mpr hNT))
  let := hsolv
  exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)

variable {ι : Type*} [Fintype ι] {C : ι → Type*} [∀ i, Group (C i)]
  [∀ i, Finite (C i)]

private theorem mem_pi_sylow_iff (Q : Sylow 2 (∀ i, C i)) (x : ∀ i, C i) :
    x ∈ Q ↔ ∀ i, x i ∈ Q.map (Pi.evalMonoidHom C i) := by
  let R : Subgroup (∀ i, C i) := Subgroup.pi Set.univ
    (fun i => Q.map (Pi.evalMonoidHom C i))
  have hp : IsPGroup 2 R := by
    intro y
    choose n hn using fun i =>
      (Q.mapSurjective (Function.surjective_eval i)).isPGroup'
        ⟨y.val i, y.property i (Set.mem_univ i)⟩
    refine ⟨∑ i, n i, Subtype.ext (funext fun i => ?_)⟩
    have hi : n i ≤ ∑ j, n j := Finset.single_le_sum
      (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
    have he : y.val i ^ (2 ^ n i) = 1 := congrArg Subtype.val (hn i)
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one he).trans
      (pow_dvd_pow 2 hi))
  have hQR : (Q : Subgroup (∀ i, C i)) ≤ R := by
    intro y hy i _
    exact mem_map_of_mem _ hy
  have he := Q.is_maximal' hp hQR
  change x ∈ (Q : Subgroup (∀ i, C i)) ↔ _
  conv_lhs => rw [← he]
  simp only [R, mem_pi, Set.mem_univ, forall_const]

/-- The subgroup supported in a single coordinate. -/
@[expose] def coordinate (i : ι) : Subgroup (∀ j, C j) where
  carrier := {x | ∀ j, j ≠ i → x j = 1}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb j hj; simp [ha j hj, hb j hj]
  inv_mem' := by intro a ha j hj; simp [ha j hj]

instance coordinate_normal (i : ι) : (coordinate (C := C) i).Normal where
  conj_mem := by intro a ha b j hj; simp [ha j hj]

/-- Full Sylow normalization forces a nontrivial perfect local group into one coordinate. -/
theorem local_image_in_coordinate [Nontrivial A] [Group.IsPerfect A]
    (f : A →* ∀ i, C i) (hf : Function.Injective f)
    (S : Sylow 2 (∀ i, C i)) (T : Sylow 2 A)
    (hTS : (T : Subgroup A).map f ≤ S)
    (hn : (S : Subgroup (∀ i, C i)) ≤ normalizer (f.range : Set (∀ i, C i)))
    (hgen : normalClosure (T : Set A) = ⊤)
    (hsol : ∀ N : Subgroup A, N.Normal → N ≠ ⊤ → Group.IsSolvable N) :
    ∃ i, f.range ≤ coordinate i := by
  classical
  by_contra! hno
  let R := solvableRadical A
  have hcoord (i : ι) : (coordinate i).comap f ≤ R := by
    apply le_solvableRadical _ inferInstance
    apply hsol _ inferInstance
    intro he
    apply hno i
    rintro _ ⟨a, rfl⟩
    exact (show a ∈ (coordinate i).comap f from he ▸ mem_top a)
  have hcomm (t : A) (ht : t ∈ T) (a : A) : ⁅t, a⁆ ∈ R := by
    have hft : f t ∈ S := hTS (mem_map_of_mem _ ht)
    have hs (i : ι) : Pi.mulSingle i (f t i) ∈ S := by
      apply (mem_pi_sylow_iff S _).mpr
      intro j
      by_cases hij : j = i
      · subst j
        simpa only [Pi.mulSingle_eq_same] using
          ((mem_pi_sylow_iff S (f t)).mp hft i)
      · simpa only [Pi.mulSingle_eq_of_ne hij] using
          ((S : Subgroup (∀ i, C i)).map (Pi.evalMonoidHom C j)).one_mem
    have hsingle (i : ι) : Pi.mulSingle i ((f ⁅t,a⁆) i) ∈ R.map f := by
      let s := Pi.mulSingle i (f t i)
      have hmem : ⁅s, f a⁆ ∈ f.range := by
        rw [commutatorElement_def]
        exact f.range.mul_mem
          ((mem_normalizer_iff.mp (hn (hs i)) (f a)).mp ⟨a, rfl⟩)
          (f.range.inv_mem ⟨a, rfl⟩)
      obtain ⟨b, hb⟩ := hmem
      have he : ⁅s, f a⁆ = Pi.mulSingle i ((f ⁅t,a⁆) i) := by
        ext j
        by_cases hij : j = i
        · subst j; simp [s, commutatorElement_def]
        · simp [s, commutatorElement_def, Pi.mulSingle_eq_of_ne hij]
      have hbD : b ∈ (coordinate i).comap f := by
        intro j hj
        rw [hb, he]
        exact Pi.mulSingle_eq_of_ne hj _
      exact ⟨b, hcoord i hbD, hb.trans he⟩
    have hm : f ⁅t,a⁆ ∈ R.map f := pi_mem_of_mulSingle_mem _ hsingle
    exact (comap_map_eq_self_of_injective hf R).le hm
  let q := QuotientGroup.mk' R
  have hTcenter : (T : Subgroup A) ≤ (center (A ⧸ R)).comap q := by
    intro t ht
    apply mem_center_iff.mpr
    intro b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective R b
    have he : ⁅q t, q a⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr (hcomm t ht a)
    exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  have hfull : (⊤ : Subgroup A) ≤ (center (A ⧸ R)).comap q := by
    rw [← hgen]
    exact normalClosure_le_normal hTcenter
  have hcenter : center (A ⧸ R) = ⊤ := by
    apply top_unique
    intro b _
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective R b
    exact hfull (mem_top a)
  let : IsMulCommutative (A ⧸ R) := center_eq_top_iff.mp hcenter
  let : Subsingleton (A ⧸ R) := inferInstance
  have hR : R = ⊤ := by
    apply top_unique
    intro a _
    exact (QuotientGroup.eq_one_iff _).mp (Subsingleton.elim (q a) 1)
  have : Group.IsSolvable A := by
    have hs : Group.IsSolvable (⊤ : Subgroup A) := hR ▸
      (inferInstance : Group.IsSolvable (solvableRadical A))
    exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup A).subtype)
      (fun a => ⟨⟨a, mem_top a⟩, rfl⟩)
  exact Group.IsPerfect.not_isSolvable A this

end Theory.AlgebraicGroup.TitsSystem.SourceBinary
