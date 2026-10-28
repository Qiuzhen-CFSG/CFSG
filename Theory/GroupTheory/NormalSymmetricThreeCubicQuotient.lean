module

public import Theory.GroupTheory.NormalSymmetricThree
public import Theory.GroupTheory.OddPrimeSectionCentralizers.FullCentralizer
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.PrimeRankElementary
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Cubic rank of a quotient killing a normal symmetric-three subgroup

A normal S₃ splits off its centralizer. If a quotient kills that subgroup,
the split coordinates give a surjection onto S₃ times the quotient. A
transposition moves the normal cubic in the first factor and centralizes the
whole second factor. The full A.1.31 involution-centralizer bound therefore
limits the second factor's three-rank to one.

The rank bound stays on the original covering group throughout; the kernel
of either surjection is unrestricted. In particular an actual elementary
nine in the final quotient is impossible. This is the section obstruction
needed when a normal S₃ in an auxiliary action fixes the original module.
Source: Aschbacher--Smith A.1.31(1), printed pp.27--28.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.NormalSymmetricThree
local notation "S3" => Equiv.Perm (Fin 3)
local notation "A3" => alternatingGroup (Fin 3)
variable {A B D : Type*} [Group A] [Group B] [Group D]

private theorem product_surjection (H : Subgroup A) [H.Normal]
    (j : H ≃* S3) (q : A →* D) (hq : Function.Surjective q)
    (hH : H ≤ q.ker) :
    ∃ r : A →* S3 × D, Function.Surjective r := by
  obtain ⟨e,he⟩ := exists_product_equiv H j
  let C := centralizer (H : Set A)
  let qC : C →* D := q.comp C.subtype
  have hqC : Function.Surjective qC := by
    intro y
    obtain ⟨a,ha⟩ := hq y
    refine ⟨(e.symm a).2,?_⟩
    have hh : q ((e.symm a).1 : A) = 1 := hH (e.symm a).1.property
    have hx := congrArg q (he (e.symm a).1 (e.symm a).2)
    rw [e.apply_symm_apply,map_mul,hh,one_mul] at hx
    exact hx.symm.trans ha
  let r := (MonoidHom.prodMap j.toMonoidHom qC).comp e.symm.toMonoidHom
  refine ⟨r,?_⟩
  intro y
  obtain ⟨c,hc⟩ := hqC y.2
  refine ⟨e (j.symm y.1,c),?_⟩
  change (j (e.symm (e (j.symm y.1,c))).1,qC (e.symm (e (j.symm y.1,c))).2) = y
  rw [e.symm_apply_apply,j.apply_symm_apply,hc]

private theorem quotient_rank_of_product_cover [Finite B] [Finite D]
    (hrank : primeRank 3 B ≤ 2) (f : B →* S3 × D)
    (hf : Function.Surjective f) : primeRank 3 D ≤ 1 := by
  let P : Subgroup (S3 × D) := (A3).prod ⊥
  let : P.Normal := inferInstanceAs ((A3).prod (⊥ : Subgroup D)).Normal
  have hP : IsPGroup 3 P := by
    intro x
    refine ⟨1,Subtype.ext ?_⟩
    apply Prod.ext
    · have hc : Nat.card A3 = 3 := by
        rw [nat_card_alternatingGroup,Nat.card_fin]
        decide
      have hh := congrArg Subtype.val (pow_card_eq_one' (x := (⟨x.val.1,x.property.1⟩ : A3)))
      change x.val.1 ^ Nat.card A3 = 1 at hh
      change x.val.1 ^ 3 = 1
      simpa only [hc] using hh
    · have hx : x.val.2 = 1 := x.property.2
      change x.val.2 ^ 3 = 1
      rw [hx,one_pow]
  let t : S3 × D := (Equiv.swap 0 1,1)
  have ht : orderOf t = 2 := by
    apply orderOf_eq_prime
    · apply Prod.ext
      · change (Equiv.swap (0 : Fin 3) 1) ^ 2 = 1
        decide +kernel
      · simp [t]
    · intro he
      have hh := congrArg Prod.fst he
      exact (by decide : (Equiv.swap (0 : Fin 3) 1) ≠ 1) hh
  have hmove : t ∉ centralizer (P : Set (S3 × D)) := by
    intro hc
    let a : S3 := Equiv.swap 0 1 * Equiv.swap 1 2
    have ha : a ∈ A3 := by
      simp only [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    have hh := congrArg Prod.fst (hc (a,1) ⟨ha,(⊥ : Subgroup D).one_mem⟩)
    exact (by decide +kernel : a * Equiv.swap 0 1 ≠ Equiv.swap 0 1 * a) hh
  let C := centralizer ({t} : Set (S3 × D))
  have hC : primeRank 3 C ≤ 1 :=
    primeRank_involutionCentralizer_le_one_of_surjective_rank_le_two
      (by decide) f hf hrank P hP t ht hmove
  let i : D →* C := {
    toFun d := ⟨(1,d),by
      apply mem_centralizer_singleton_iff.mpr
      simp [t]⟩
    map_one' := rfl
    map_mul' _ _ := by apply Subtype.ext; simp }
  have hi : Function.Injective i := by
    intro x y h
    exact congrArg (fun c : C => c.val.2) h
  exact (primeRank_le_of_injective 3 i hi).trans hC

/-- A quotient killing a normal S₃ has three-rank at most one when the
original cover has three-rank at most two. Neither kernel is restricted. -/
theorem three_rank_le_one_of_killing_normal_symmetricThree [Finite B] [Finite D]
    (hrank : primeRank 3 B ≤ 2) (f : B →* A) (hf : Function.Surjective f)
    (H : Subgroup A) [H.Normal] (j : H ≃* S3)
    (q : A →* D) (hq : Function.Surjective q) (hH : H ≤ q.ker) :
    primeRank 3 D ≤ 1 := by
  obtain ⟨r,hr⟩ := product_surjection H j q hq hH
  exact quotient_rank_of_product_cover hrank (r.comp f) (hr.comp hf)

/-- An actual elementary nine excludes a quotient killing a normal S₃. -/
theorem not_killing_normal_symmetricThree_of_elementary_nine [Finite B] [Finite D]
    (hrank : primeRank 3 B ≤ 2) (f : B →* A) (hf : Function.Surjective f)
    (H : Subgroup A) [H.Normal] (j : H ≃* S3)
    (q : A →* D) (hq : Function.Surjective q) (hH : H ≤ q.ker)
    (R : Subgroup D) [IsElementaryAbelian 3 R] (hR : Nat.card R = 9) : False := by
  have hr := three_rank_le_one_of_killing_normal_symmetricThree hrank f hf H j q hq hH
  have hc := (primeRank_le_iff_elementary_card_le D).mp hr R inferInstance
  norm_num [hR] at hc

end Theory.GroupTheory.NormalSymmetricThree
