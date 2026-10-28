module
public import Theory.GroupTheory.NormalCubicSylowProduct
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Faithful cubic sections and prime-to-three kernels

An elementary subgroup attaining the prime rank inside an abelian Sylow
subgroup leaves no room for a nontrivial kernel at that prime. In particular,
a detected normal cubic and a detected nonnormal cubic in an S₃-square
quotient force the kernel to have order prime to three when the original
three-rank is at most two. The normal cubic supplies the abelian Sylows.

The source application uses the literal star quotient in the cyclic branch
of Aschbacher--Smith 15.2.21(3), printed p.1114, refs/quasithin.pdf.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G D : Type*} [Group G] [Finite G] [Group D]

/-- A faithful elementary subgroup attaining the rank of an abelian Sylow
forces the homomorphism kernel to have order prime to that Sylow prime. -/
theorem coprime_kernel_of_abelian_sylow_section
    {p : ℕ} [Fact p.Prime] (f : G →* D) (r : ℕ)
    (hr : primeRank p G ≤ r)
    (hab : ∀ P : Sylow p G, IsMulCommutative P)
    (E : Subgroup G) (hE : IsElementaryAbelian p E)
    (hc : Nat.card E = p ^ r) (hi : Function.Injective (f.comp E.subtype)) :
    Nat.Coprime p (Nat.card f.ker) := by
  let := hE
  obtain ⟨P,hEP⟩ := (IsElementaryAbelian.isPGroup p E).exists_le_sylow
  let := hab P
  let A := E.subgroupOf (P : Subgroup G)
  let C := f.ker.subgroupOf (P : Subgroup G)
  have hAr : r ≤ primeRank p A := by
    let : IsElementaryAbelian p A := IsElementaryAbelian.subgroupOf hEP
    have hAc : Nat.card A = p ^ r :=
      (Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv).trans hc
    exact primeRank_ge_of_elementary_embedding
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p A)) hAc
      (MonoidHom.id A) Function.injective_id
  have hd : Disjoint A C := by
    apply disjoint_def.mpr
    intro x hx hk
    have he : (⟨(x : G),hx⟩ : E) = 1 := hi (by
      change f (x : G) = f 1
      rw [map_one]
      exact hk)
    exact Subtype.ext (congrArg (fun e : E => (e : G)) he)
  have hcomm : A ≤ centralizer (C : Set P) := by
    intro a _ c _
    exact mul_comm c a
  have hCr : primeRank p C = 0 := by
    have he := primeRank_sup_eq_add_of_disjoint_commuting A C hd hcomm p
    have hb := (primeRank_le_of_injective p (A ⊔ C).subtype (A ⊔ C).subtype_injective).trans
      ((primeRank_le_of_injective p (P : Subgroup G).subtype (P : Subgroup G).subtype_injective).trans hr)
    omega
  have hCcard : Nat.card C = 1 :=
    (P.isPGroup'.to_subgroup C).card_eq_or_dvd.resolve_right
      (PrimeRank.eq_zero_iff_not_dvd_card.mp hCr)
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_normal f.ker
  have hQcard : Nat.card Q = 1 := by
    rw [Nat.card_congr (MulEquiv.subgroupCongr hQ).toEquiv]
    let e : (P : Subgroup G).subgroupOf f.ker ≃* C :=
      { toFun := fun x => ⟨⟨x, x.property⟩, x.val.property⟩
        invFun := fun x => ⟨⟨x, x.property⟩, x.val.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    exact (Nat.card_congr e.toEquiv).trans hCcard
  have hindex := Q.not_dvd_index
  have he := (Q : Subgroup f.ker).index_mul_card
  rw [hQcard,mul_one] at he
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (he ▸ hindex)
private theorem disjoint_cubic_of_ne (A B : Subgroup G)
    (hA : Nat.card A = 3) (hB : Nat.card B = 3) (hne : A ≠ B) : Disjoint A B := by
  rcases (Nat.dvd_prime Nat.prime_three).mp
    (show Nat.card (A ⊓ B : Subgroup G) ∣ 3 from hA ▸ card_dvd_of_le inf_le_left) with hc | hc
  · exact disjoint_iff.mpr (card_eq_one.mp hc)
  · have ha := eq_of_le_of_card_ge (inf_le_left : A ⊓ B ≤ A) (by rw [hc,hA])
    have hb := eq_of_le_of_card_ge (inf_le_right : A ⊓ B ≤ B) (by rw [hc,hB])
    exact (hne (ha.symm.trans hb)).elim

/-- Two independent detected cubics, one normal, exhaust the three-part of
an S₃-square quotient in a group of three-rank at most two. -/
theorem coprime_kernel_of_normal_and_nonnormal_cubics
    (hr : primeRank 3 G ≤ 2)
    (f : G →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (A B : Subgroup G) [A.Normal]
    (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hfA : Nat.card (A.map f) = 3) (hfB : Nat.card (B.map f) = 3)
    (hn : ¬ (B.map f).Normal) : Nat.Coprime 3 (Nat.card f.ker) := by
  have hne : A.map f ≠ B.map f := by
    intro he
    apply hn
    rw [←he]
    exact Normal.map inferInstance f hf
  have hd := disjoint_cubic_of_ne A B hA hB (fun he => hne (congrArg (map f) he))
  have hdf := disjoint_cubic_of_ne (A.map f) (B.map f) hfA hfB hne
  have hcomm : A ≤ centralizer (B : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_odd_normalizes_card_three A B hA
        (by rw [hB]; decide) le_normalizer_of_normal)
  let : IsCyclic A := isCyclic_of_prime_card hA
  let : IsCyclic B := isCyclic_of_prime_card hB
  let : IsElementaryAbelian 3 A := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun a => hA ▸ pow_card_eq_one' (x := a)) }
  let : IsElementaryAbelian 3 B := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun b => hB ▸ pow_card_eq_one' (x := b)) }
  let E := A ⊔ B
  have hE : IsElementaryAbelian 3 E :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hcomm)
  have hEc : Nat.card E = 3 ^ 2 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A B le_normalizer_of_normal hd,hA,hB]
    rfl
  have hEf : Nat.card (E.map f) = 3 ^ 2 := by
    rw [Subgroup.map_sup,card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((map_mono (show B ≤ normalizer (A : Set G) from le_normalizer_of_normal)).trans
        (le_normalizer_map f)) hdf,hfA,hfB]
    rfl
  have hi : Function.Injective (f.comp E.subtype) := by
    intro x y hh
    exact ((f.subgroupMap_surjective E).bijective_of_nat_card_le
      (by rw [hEc,hEf])).1 (Subtype.ext hh)
  apply coprime_kernel_of_abelian_sylow_section f 2 hr ?_ E hE hEc hi
  intro P
  have hiA : Function.Injective (f.comp A.subtype) := by
    intro x y hh
    exact ((f.subgroupMap_surjective A).bijective_of_nat_card_le
      (by rw [hA,hfA])).1 (Subtype.ext hh)
  obtain ⟨n,_,⟨e⟩⟩ := normal_cubic_sylow_three_product hr A hA f hf hiA P
  exact ⟨⟨fun x y => e.injective (by simp only [map_mul]; exact mul_comm _ _)⟩⟩
end Theory.GroupTheory
