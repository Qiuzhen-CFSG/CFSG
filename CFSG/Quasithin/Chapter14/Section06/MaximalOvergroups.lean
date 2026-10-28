module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Preorder.Finite

/-!
# The maximal-intersection choices in §14.6

For a family `ℋ` of local subgroups, `outsideOvergroups ℋ S A B` consists of
its members containing `S` and contained in neither `A` nor `B`. In the source,
`S = Tᵤ`, `A = G₁`, and `B = M`. Members of `IStar` have maximal intersection
with `T`; members of `IMin` are inclusion-minimal among these.

Maximality transfers to any member containing the original intersection.
Finiteness supplies both successive choices. For an inclusion-minimal choice,
every proper intermediate local subgroup lies in one of the two excluded
overgroups. These are the order-theoretic steps of Lemmas 14.6.4–5 and the
maximal-overgroup argument in 14.6.6(5).

Reference: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, pp. 1022–1023. The local family is an explicit parameter;
none of the group-theoretic hypotheses or conclusions of 14.6.25 is assumed here.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter14.Section06

variable {G : Type*} [Group G]

/-- The source family `I(T,u)`, with the local family and `Tᵤ` supplied explicitly. -/
def outsideOvergroups (ℋ : Set (Subgroup G)) (S A B : Subgroup G) : Set (Subgroup G) :=
  {I | I ∈ ℋ ∧ S ≤ I ∧ ¬ I ≤ A ∧ ¬ I ≤ B}

/-- The source `I⁎`: maximality concerns `T ∩ I`, not `I`. -/
def IStar (T : Subgroup G) (ℐ : Set (Subgroup G)) : Set (Subgroup G) :=
  {I | MaximalFor (· ∈ ℐ) (fun J => T ⊓ J) I}

/-- The source `I_*`: inclusion-minimal members of `I⁎`. -/
def IMin (T : Subgroup G) (ℐ : Set (Subgroup G)) : Set (Subgroup G) :=
  {I | Minimal (· ∈ IStar T ℐ) I}

variable {ℋ ℐ : Set (Subgroup G)} {S T A B I J : Subgroup G}

/-- Lemma 14.6.4: containment of the intersection transfers maximality. -/
theorem lemma14_6_4 (hI : I ∈ IStar T ℐ) (hJ : J ∈ ℐ) (hIJ : T ⊓ I ≤ J) :
    J ∈ IStar T ℐ ∧ T ⊓ J = T ⊓ I := by
  have hle : T ⊓ I ≤ T ⊓ J := le_inf inf_le_left hIJ
  have heq : T ⊓ J = T ⊓ I := le_antisymm (hI.2 hJ hle) hle
  refine ⟨⟨hJ, ?_⟩, heq⟩
  intro K hK hJK
  change T ⊓ J ≤ T ⊓ K at hJK
  change T ⊓ K ≤ T ⊓ J
  rw [heq] at hJK ⊢
  exact hI.2 hK hJK

/-- The first assertion of Lemma 14.6.5. Membership in the local family must
be retained when passing to an overgroup. -/
theorem lemma14_6_5_mem (hI : I ∈ outsideOvergroups ℋ S A B)
    (hIJ : I ≤ J) (hJ : J ∈ ℋ) : J ∈ outsideOvergroups ℋ S A B :=
  ⟨hJ, hI.2.1.trans hIJ, fun h => hI.2.2.1 (hIJ.trans h),
    fun h => hI.2.2.2 (hIJ.trans h)⟩

/-- The second assertion of Lemma 14.6.5. -/
theorem lemma14_6_5 (hI : I ∈ IStar T (outsideOvergroups ℋ S A B))
    (hIJ : I ≤ J) (hJ : J ∈ ℋ) :
    J ∈ IStar T (outsideOvergroups ℋ S A B) ∧ T ⊓ J = T ⊓ I :=
  lemma14_6_4 hI (lemma14_6_5_mem hI.1 hIJ hJ) (inf_le_right.trans hIJ)

/-- A nonempty finite family has a member with maximal intersection with `T`. -/
theorem iStar_nonempty_of_finite (hfin : ℐ.Finite) (hne : ℐ.Nonempty) :
    (IStar T ℐ).Nonempty :=
  hfin.exists_maximalFor (fun J => T ⊓ J) ℐ hne

/-- The finite-group version used after 14.6.17(4) and 14.6.24(4). -/
theorem iStar_nonempty [Finite G] (hne : ℐ.Nonempty) : (IStar T ℐ).Nonempty := by
  let : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  exact iStar_nonempty_of_finite ℐ.toFinite hne

/-- Every finite maximal-intersection choice contains an inclusion-minimal one. -/
theorem exists_iMin_le (hfin : ℐ.Finite) (hI : I ∈ IStar T ℐ) :
    ∃ J, J ≤ I ∧ J ∈ IMin T ℐ := by
  have hstar : (IStar T ℐ).Finite := hfin.subset (fun _ h => h.1)
  exact hstar.exists_le_minimal hI

/-- Such a minimal choice retains the same intersection with `T`. -/
theorem exists_iMin_le_same_intersection (hfin : ℐ.Finite)
    (hI : I ∈ IStar T ℐ) :
    ∃ J, J ≤ I ∧ J ∈ IMin T ℐ ∧ T ⊓ J = T ⊓ I := by
  obtain ⟨J, hJI, hJ⟩ := exists_iMin_le hfin hI
  have heq := (lemma14_6_4 hJ.1 hI.1 (inf_le_right.trans hJI)).2
  exact ⟨J, hJI, hJ, heq.symm⟩

/-- The subgroup choice in both final contradictions: if a maximal intersection
equals `S`, use a prescribed member `C` containing `S` instead. -/
theorem exists_iStar_preferred (hfin : ℐ.Finite) {C : Subgroup G}
    (hC : C ∈ ℐ) (hSC : S ≤ C) :
    ∃ I, I ∈ IStar T ℐ ∧ (T ⊓ I = S → I = C) := by
  classical
  by_cases h : ∃ J, J ∈ IStar T ℐ ∧ T ⊓ J = S
  · obtain ⟨J, hJ, hJS⟩ := h
    have hJC : T ⊓ J ≤ C := hJS ▸ hSC
    exact ⟨C, (lemma14_6_4 hJ hC hJC).1, fun _ => rfl⟩
  · obtain ⟨I, hI⟩ := iStar_nonempty_of_finite (T := T) hfin ⟨C, hC⟩
    exact ⟨I, hI, fun hIS => (h ⟨I, hI, hIS⟩).elim⟩

/-- The minimality step of 14.6.6(5). -/
theorem intermediate_le_one_of_iMin
    (hI : I ∈ IMin T (outsideOvergroups ℋ S A B)) (hST : S ≤ T)
    (hJ : J ∈ ℋ) (hTJ : T ⊓ I ≤ J) (hJI : J < I) : J ≤ A ∨ J ≤ B := by
  classical
  by_contra h
  have hJA : ¬ J ≤ A := fun hJA => h (Or.inl hJA)
  have hJB : ¬ J ≤ B := fun hJB => h (Or.inr hJB)
  have hSJ : S ≤ J := (le_inf hST hI.1.1.2.1).trans hTJ
  have hJstar := (lemma14_6_4 hI.1 ⟨hJ, hSJ, hJA, hJB⟩ hTJ).1
  exact hJI.not_ge (hI.2 hJstar hJI.le)

/-- A maximal proper intermediate subgroup is one of `I ∩ A`, `I ∩ B`.
This is the order-theoretic dichotomy in 14.6.6(5), before 14.6.6(3) is used. -/
theorem maximal_intermediate_eq_inf_of_iMin
    (hI : I ∈ IMin T (outsideOvergroups ℋ S A B)) (hST : S ≤ T)
    (hJ : J ∈ ℋ) (hTJ : T ⊓ I ≤ J)
    (hmax : Maximal (fun Y : Subgroup G => Y < I) J) :
    J = I ⊓ A ∨ J = I ⊓ B := by
  have eq_inf (D : Subgroup G) (hID : ¬ I ≤ D) (hJD : J ≤ D) : J = I ⊓ D := by
    have hlt : I ⊓ D < I := lt_of_le_not_ge inf_le_left (fun h => hID (h.trans inf_le_right))
    exact le_antisymm (le_inf hmax.1.le hJD) (hmax.2 hlt (le_inf hmax.1.le hJD))
  rcases intermediate_le_one_of_iMin hI hST hJ hTJ hmax.1 with hJA | hJB
  · exact Or.inl (eq_inf A hI.1.1.2.2.1 hJA)
  · exact Or.inr (eq_inf B hI.1.1.2.2.2 hJB)

/-- In the non-factorization branch of 14.6.6(5), `I ∩ B ≤ A` makes `I ∩ A`
the unique maximal subgroup of `I` containing `T ∩ I`. The local-family
hypothesis is needed only for proper intermediate overgroups of `T ∩ I`. -/
theorem unique_maximal_over_intersection_of_iMin
    (hI : I ∈ IMin T (outsideOvergroups ℋ S A B)) (hST : S ≤ T)
    (hTA : T ≤ A) (hIB : I ⊓ B ≤ A)
    (hlocal : ∀ J : Subgroup G, T ⊓ I ≤ J → J < I → J ∈ ℋ) :
    T ⊓ I ≤ I ⊓ A ∧ Maximal (fun Y : Subgroup G => Y < I) (I ⊓ A) ∧
      ∀ J : Subgroup G, T ⊓ I ≤ J →
        Maximal (fun Y : Subgroup G => Y < I) J → J = I ⊓ A := by
  have hTI : T ⊓ I ≤ I ⊓ A := le_inf inf_le_right (inf_le_left.trans hTA)
  have hlt : I ⊓ A < I :=
    lt_of_le_not_ge inf_le_left (fun h => hI.1.1.2.2.1 (h.trans inf_le_right))
  have bound (J : Subgroup G) (hTJ : T ⊓ I ≤ J) (hJI : J < I) : J ≤ I ⊓ A := by
    refine le_inf hJI.le ?_
    rcases intermediate_le_one_of_iMin hI hST (hlocal J hTJ hJI) hTJ hJI with hJA | hJB
    · exact hJA
    · exact (le_inf hJI.le hJB).trans hIB
  refine ⟨hTI, ⟨hlt, fun J hJI hIJ => bound J (hTI.trans hIJ) hJI⟩, ?_⟩
  intro J hTJ hJ
  exact hJ.eq_of_le hlt (bound J hTJ hJ.1)

end CFSG.Quasithin.Chapter14.Section06
