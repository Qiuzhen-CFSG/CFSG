module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Inputs
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Subgroup

/-!
# Reduction of max4 conjugacy to Sylow-overgroup exhaustion

The source list suggests three types of maximal overgroups of a Sylow
2-subgroup of J₄: max1, the 2A involution centralizer, and max4. The
exhaustion assertion below concerns every actual proper overgroup; it is an
unproved input, not a consequence of defining those three subgroups.

A max4 quotient S₅ × SL₃(2) supplies an element of order 35 and a nontrivial
sign character. Thus a max4-type subgroup is proper in a perfect ambient
group. Excluding order 35 from the first two overgroup types leaves
containment in a conjugate of max4. Equality then follows from the given
isomorphism and finiteness.

Source motivation: the maximal-subgroup list at
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ and Kleidman–Wilson,
*The maximal subgroups of J₄*, Proc. London Math. Soc. 56 (1988), 484–510.
An–O'Brien–Wilson, LMS J. Comput. Math. 6 (2003), §§3–4, also describes the
four maximal 2-local types. The max3 type has even index in the source
list; the exhaustive Sylow-overgroup input must justify its exclusion.
The application on printed p.511 of `refs/quasithin.pdf` cites Aschbacher
(1986), but does not itself assert the conjugacy contract.
-/

public section

open Subgroup Janko4.LocalStructure.SymmetricLinear

attribute [local irreducible] max4Subgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy

/-- The actual max4 quotient provides an element of order 35. -/
theorem exists_orderOf_thirtyFive (hQ : MaximalFourQuotient) :
    ∃ x : max4Subgroup, orderOf x = 35 := by
  obtain ⟨e⟩ := hQ
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Equiv.Perm (Fin 5)) 5 (by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm])
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card'
    (G := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) 7 (by
      rw [Atlas.Comparisons.Exceptional.sl3Two_card]
      decide)
  let f : max4Subgroup →* QuotientModel :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 max4Subgroup))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨x, hx⟩ := hf (u, v)
  have hx35 : 35 ∣ orderOf x := by
    have h := orderOf_map_dvd f x
    rw [hx, Prod.orderOf_mk, hu, hv] at h
    exact h
  exact ⟨x ^ (orderOf x / 35), orderOf_pow_orderOf_div
    (isOfFinOrder_of_finite x).orderOf_pos.ne' hx35⟩

/-- Its sign quotient obstructs perfectness of the literal max4 carrier. -/
theorem not_perfect (hQ : MaximalFourQuotient) : ¬ Group.IsPerfect max4Subgroup := by
  intro hperfect
  let := hperfect
  obtain ⟨e⟩ := hQ
  let f : max4Subgroup →* ℤˣ := Equiv.Perm.sign.comp
    ((MonoidHom.fst _ _).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 max4Subgroup))))
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨p, hp⟩ := Equiv.Perm.sign_surjective (Fin 5) z
    obtain ⟨x, hx⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) (p, 1)
    refine ⟨x, ?_⟩
    change Equiv.Perm.sign (e (QuotientGroup.mk' _ x)).1 = z
    change e (QuotientGroup.mk' _ x) = (p, 1) at hx
    rw [hx]
    exact hp
  obtain ⟨x, hx⟩ := hf (-1)
  have hx1 : f x = 1 :=
    Abelianization.commutator_subset_ker f (Group.IsPerfect.mem_commutator (g := x))
  rw [hx] at hx1
  exact (by decide : (-1 : ℤˣ) ≠ 1) hx1

/-- Exhaustion by the three actual ambient subgroup types, including all
proper subgroups containing an ambient Sylow subgroup. -/
@[expose] def ProperSylowOvergroupCover : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model) (H : Subgroup Janko4.Model),
    S.toSubgroup ≤ H → H ≠ ⊤ → ∃ g : Janko4.Model,
      H ≤ (Janko4.Cardinality.max1Subgroup
        Janko4.matrixA_mul_self Janko4.matrixB_pow_four).map (MulAut.conj g).toMonoidHom ∨
      H ≤ (centralizer ({Janko4.a} : Set Janko4.Model)).map (MulAut.conj g).toMonoidHom ∨
      H ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom

/-- Only this element-order exclusion is needed from the full 2A centralizer.
A calculation inside a proposed generating subgroup is insufficient. -/
@[expose] def InvolutionCentralizerOmitsThirtyFive : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (x : centralizer ({Janko4.a} : Set Janko4.Model)), orderOf x ≠ 35

private theorem no_embedding {G : Type*} [Group G] {M L : Subgroup G}
    (hL : ∀ x : L, orderOf x ≠ 35) (g : G)
    (hML : M ≤ L.map (MulAut.conj g).toMonoidHom)
    (x : M) (hx : orderOf x = 35) : False := by
  let e := ((MulAut.conj g).subgroupMap L).symm
  let f := e.toMonoidHom.comp (inclusion hML)
  exact hL (f x) ((orderOf_injective f
    (e.injective.comp (inclusion_injective hML)) x).trans hx)

private theorem subgroup_ne_top_of_not_perfect {G : Type*} [Group G]
    [Group.IsPerfect G] (M L : Subgroup G) (e : M ≃* L)
    (hH : ¬ Group.IsPerfect L) : M ≠ ⊤ := by
  intro hM
  subst M
  exact hH (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)

private theorem exists_orderOf_of_equiv {G : Type*} [Group G]
    (M L : Subgroup G) (e : M ≃* L)
    (h : ∃ x : L, orderOf x = 35) : ∃ x : M, orderOf x = 35 := by
  obtain ⟨x, hx⟩ := h
  exact ⟨e.symm x, (e.symm.orderOf_eq x).trans hx⟩

private theorem eq_map_of_le_of_equiv {G : Type*} [Group G] [Finite G]
    (M L : Subgroup G) (e : M ≃* L) (g : G)
    (hML : M ≤ L.map (MulAut.conj g).toMonoidHom) :
    M = L.map (MulAut.conj g).toMonoidHom := by
  apply eq_of_le_of_card_ge hML
  exact le_of_eq ((Nat.card_congr ((MulAut.conj g).subgroupMap L).toEquiv).symm.trans
    (Nat.card_congr e.toEquiv).symm)

/-- Every actual max4-type Sylow overgroup is a conjugate of max4, conditional
on exhaustion and the two intrinsic element-order exclusions. -/
theorem eq_conjugate (hQ : MaximalFourQuotient) (hcover : ProperSylowOvergroupCover)
    (h1 : ∀ x : Janko4.Cardinality.max1Subgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four, orderOf x ≠ 35)
    (h2 : InvolutionCentralizerOmitsThirtyFive)
    [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model) (M : Subgroup Janko4.Model)
    (hSM : S.toSubgroup ≤ M) (hM : Nonempty (M ≃* max4Subgroup)) :
    ∃ g : Janko4.Model, M = max4Subgroup.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨e⟩ := hM
  have hMtop : M ≠ ⊤ := subgroup_ne_top_of_not_perfect
    (G := Janko4.Model) M max4Subgroup e (not_perfect hQ)
  obtain ⟨x, hxM⟩ := exists_orderOf_of_equiv
    (G := Janko4.Model) M max4Subgroup e (exists_orderOf_thirtyFive hQ)
  obtain ⟨g, hg | hg | hg⟩ := hcover S M hSM hMtop
  · exact (no_embedding (G := Janko4.Model) (M := M)
      (L := Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
      h1 g hg x hxM).elim
  · exact (no_embedding (G := Janko4.Model) (M := M)
      (L := centralizer ({Janko4.a} : Set Janko4.Model)) h2 g hg x hxM).elim
  · exact ⟨g, eq_map_of_le_of_equiv (G := Janko4.Model) M max4Subgroup e g hg⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy
