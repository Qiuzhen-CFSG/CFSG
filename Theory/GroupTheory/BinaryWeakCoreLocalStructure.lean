module

public import Theory.GroupTheory.BinaryWeakCoreIsolatedGeometry
public import Theory.GroupTheory.PGroup.UniqueInvolutionClassification
public import Theory.GroupTheory.PGroup.NoNormalFourClassification
public import Theory.GroupTheory.DihedralUniqueInvolutionProduct

/-!
# The two local factors in the isolated binary weak-core case

Write `C = C_S(Q)`. The isolated-four geometry identifies the unique
involution of the ambient centralizer with an involution in `Q ∩ C`.
Thus `C` itself has a unique involution. The rank-three weak overgroup
makes `C` noncyclic, so it is also nonabelian. Absence of normal four-groups
in `Q` gives a cyclic normal self-centralizing subgroup of `Q`.
The shared involution also excludes the dihedral alternative: its commuting
product with `C` has elementary binary rank at most two. Consequently `C` is
generalized quaternion, and `Q` is cyclic, generalized quaternion, or
semidihedral. If `Q` contains a four-group, only the semidihedral case remains.
Every Sylow two-subgroup of the ambient centralizer is also generalized
quaternion, by embedding the noncyclic local centralizer and using Sylow
conjugacy; this does not identify the local centralizer with a Sylow subgroup.

These statements implement the local classification reductions for the binary
fusion remark after GLS2, Proposition 22.4, using GLS2, Lemma 10.11 and
Lemma 10.21(iii), and Huppert III.8.2.
-/

namespace Subgroup

/-- The local centralizer has a unique involution, provided an isolated
four-group in Q identifies the ambient involution inside S. -/
public theorem existsUnique_involution_centralizer_of_isolated_four
    {G : Type*} [Group G] [Finite G] (S A Q E : Subgroup G)
    (hS : IsPGroup 2 S) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E]
    (hA : 8 ≤ Nat.card A) (hE : Nat.card E = 4)
    (hAS : A ≤ S) (hQS : Q ≤ S) (hEQ : E ≤ Q)
    (hiso : ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ S → W ≤ centralizer (E : Set G) → W = E)
    (hunique : ∃! t : centralizer (Q : Set G), orderOf t = 2) :
    ∃! t : (S ⊓ centralizer (Q : Set G) : Subgroup G), orderOf t = 2 := by
  obtain ⟨z, hz, -, hzQ, hzS, -⟩ :=
    central_involution_of_isolated_four_of_unique_centralizer S A Q E hS
      hA hE hAS hQS hEQ hiso hunique
  have hzC : z ∈ centralizer (Q : Set G) := centralizer_le hQS hzS
  let zS : (S ⊓ centralizer (Q : Set G) : Subgroup G) :=
    ⟨z, ⟨hQS hzQ, hzC⟩⟩
  have hzSorder : orderOf zS = 2 := by
    rw [← orderOf_coe]
    exact hz
  refine ⟨zS, hzSorder, ?_⟩
  intro t ht
  have htC : orderOf (⟨t, t.property.2⟩ : centralizer (Q : Set G)) = 2 := by
    rw [← orderOf_coe]
    simpa only [orderOf_coe] using ht
  have heq := hunique.unique htC (show orderOf (⟨z, hzC⟩ : centralizer (Q : Set G)) = 2 by
    rw [← orderOf_coe]
    exact hz)
  apply Subtype.ext
  exact congrArg (fun x : centralizer (Q : Set G) => (x : G)) heq

/-- In the isolated weak-rank case, the local centralizer is nonabelian.
Together with its unique involution, this selects the quaternion branch
of the unique-involution classification. -/
public theorem not_isMulCommutative_centralizer_of_isolated_fours_of_weak_rank
    {G : Type*} [Group G] [Finite G] (S Q B : Subgroup G)
    (hS : IsPGroup 2 S) [IsElementaryAbelian 2 B]
    (hB : 8 ≤ Nat.card B) (hQS : Q ≤ S)
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (hiso : ∀ V : Subgroup G, IsElementaryAbelian 2 V → Nat.card V = 4 → V ≤ Q →
      ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
        W ≤ S → W ≤ centralizer (V : Set G) → W = V)
    (hunique : ∃! t : (S ⊓ centralizer (Q : Set G) : Subgroup G), orderOf t = 2) :
    ¬ IsMulCommutative (S ⊓ centralizer (Q : Set G) : Subgroup G) := by
  intro hcomm
  let : IsMulCommutative (S ⊓ centralizer (Q : Set G) : Subgroup G) := hcomm
  have hC : IsPGroup 2 (S ⊓ centralizer (Q : Set G) : Subgroup G) :=
    hS.of_injective (inclusion inf_le_left) (inclusion_injective _)
  exact not_isCyclic_centralizer_of_isolated_fours_of_weak_rank S Q B hB hQS hBweak hiso
    (hC.isCyclic_of_unique_involution_of_isMulCommutative hunique)

/-- The dihedral alternative is impossible in the isolated binary weak-core
case. One isolated four-group identifies the shared involution; the commuting
product then has elementary binary rank at most two. -/
public theorem not_dihedral_of_isolated_four_of_weak_rank
    {G : Type*} [Group G] [Finite G] (S Q B E : Subgroup G)
    (hS : IsPGroup 2 S) [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 E]
    (hB : 8 ≤ Nat.card B) (hE : Nat.card E = 4)
    (hQS : Q ≤ S) (hEQ : E ≤ Q)
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (hiso : ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ S → W ≤ centralizer (E : Set G) → W = E)
    (hunique : ∃! t : centralizer (Q : Set G), orderOf t = 2)
    (n : ℕ) : ¬ Nonempty (Q ≃* DihedralGroup n) := by
  rintro ⟨e⟩
  have hBS : B ≤ S := hBweak.trans (sup_le hQS inf_le_left)
  have hc := Nat.card_congr e.toEquiv
  rw [DihedralGroup.nat_card] at hc
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have hn : n ≠ 0 := by omega
  let : NeZero n := ⟨hn⟩
  let C := S ⊓ centralizer (Q : Set G)
  have hCu : ∃! t : C, orderOf t = 2 :=
    existsUnique_involution_centralizer_of_isolated_four S B Q E hS hB hE
      hBS hQS hEQ hiso hunique
  obtain ⟨z, hz, -, hzQ, hzS, -⟩ :=
    central_involution_of_isolated_four_of_unique_centralizer S B Q E hS
      hB hE hBS hQS hEQ hiso hunique
  have hzC : z ∈ C := ⟨hQS hzQ, centralizer_le hQS hzS⟩
  have hoverlap : ∃ z : C, orderOf z = 2 ∧ (z : G) ∈ Q :=
    ⟨⟨z, hzC⟩, by simpa only [← orderOf_coe] using hz, hzQ⟩
  have hbound := card_elementary_le_four_of_dihedral_unique_involution_sup Q C B e
    (hS.of_injective (inclusion inf_le_left) (inclusion_injective _)) hCu hoverlap
    inf_le_right hBweak
  omega

/-- A noncyclic local two-centralizer is generalized quaternion if involutions
in the ambient centralizer are unique. No isolation assumption is needed. -/
public theorem exists_quaternion_centralizer_of_unique_involution
    {G : Type*} [Group G] [Finite G] (S Q : Subgroup G)
    (hS : IsPGroup 2 S)
    (hunique : ∃! t : centralizer (Q : Set G), orderOf t = 2)
    (hnot : ¬ IsCyclic (S ⊓ centralizer (Q : Set G) : Subgroup G)) :
    ∃ n : ℕ, 3 ≤ n ∧ Nonempty
      ((S ⊓ centralizer (Q : Set G) : Subgroup G) ≃* QuaternionGroup (2 ^ (n - 2))) := by
  let C := S ⊓ centralizer (Q : Set G)
  have hC : IsPGroup 2 C :=
    hS.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hdiv : 2 ∣ Nat.card C := by
    rcases hC.card_eq_or_dvd with h | h
    · have hsub : Subsingleton C := (Nat.card_eq_one_iff_unique.mp h).1
      exact (hnot (@isCyclic_of_subsingleton C _ hsub)).elim
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hdiv
  have hu : ∃! z : C, orderOf z = 2 := by
    refine ⟨z, hz, fun t ht => ?_⟩
    let f : C →* centralizer (Q : Set G) := inclusion inf_le_right
    apply inclusion_injective (show C ≤ centralizer (Q : Set G) from inf_le_right)
    exact hunique.unique
      ((orderOf_injective f (inclusion_injective _) t).trans ht)
      ((orderOf_injective f (inclusion_injective _) z).trans hz)
  exact (hC.isCyclic_or_quaternion_of_unique_involution hu).resolve_left hnot

/-- Every Sylow two-subgroup of the ambient centralizer is generalized
quaternion in the isolated weak-rank configuration. The local centralizer
need not itself be Sylow: embed it in one Sylow subgroup and transport its
noncyclicity by Sylow conjugacy. -/
public theorem exists_quaternion_sylow_centralizer_of_isolated_fours_of_weak_rank
    {G : Type*} [Group G] [Finite G] (S Q B : Subgroup G)
    (hS : IsPGroup 2 S) [IsElementaryAbelian 2 B]
    (hB : 8 ≤ Nat.card B) (hQS : Q ≤ S)
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (hiso : ∀ V : Subgroup G, IsElementaryAbelian 2 V → Nat.card V = 4 → V ≤ Q →
      ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
        W ≤ S → W ≤ centralizer (V : Set G) → W = V)
    (hunique : ∃! t : centralizer (Q : Set G), orderOf t = 2)
    (T : Sylow 2 (centralizer (Q : Set G))) :
    ∃ n : ℕ, 3 ≤ n ∧ Nonempty (T ≃* QuaternionGroup (2 ^ (n - 2))) := by
  let C := centralizer (Q : Set G)
  let D := S ⊓ C
  have hDC : D ≤ C := inf_le_right
  have hD : IsPGroup 2 D := hS.to_le inf_le_left
  have hnot := not_isCyclic_centralizer_of_isolated_fours_of_weak_rank
    S Q B hB hQS hBweak hiso
  have hD' : IsPGroup 2 (D.subgroupOf C) :=
    hD.of_equiv (subgroupOfEquivOfLe hDC).symm
  obtain ⟨U, hDU⟩ := hD'.exists_le_sylow
  let f : D →* T := (U.equiv T).toMonoidHom.comp
    ((inclusion hDU).comp (subgroupOfEquivOfLe hDC).symm.toMonoidHom)
  have hf : Function.Injective f := (U.equiv T).injective.comp
    ((inclusion_injective hDU).comp (subgroupOfEquivOfLe hDC).symm.injective)
  have hTnot : ¬ IsCyclic T := by
    intro hcyc
    let : IsCyclic T := hcyc
    exact hnot (isCyclic_of_injective f hf)
  have hdiv : 2 ∣ Nat.card T := by
    rcases T.isPGroup'.card_eq_or_dvd with h | h
    · have hsub : Subsingleton T := (Nat.card_eq_one_iff_unique.mp h).1
      exact (hTnot (@isCyclic_of_subsingleton T _ hsub)).elim
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 hdiv
  have hu : ∃! t : T, orderOf t = 2 := by
    refine ⟨z, hz, fun t ht => ?_⟩
    apply Subtype.ext
    exact hunique.unique
      ((orderOf_injective (T : Subgroup C).subtype Subtype.coe_injective t).trans ht)
      ((orderOf_injective (T : Subgroup C).subtype Subtype.coe_injective z).trans hz)
  exact (T.isPGroup'.isCyclic_or_quaternion_of_unique_involution hu).resolve_left hTnot

/-- With an isolated four-group in Q, absence of normal four-groups and the
weak rank-three overgroup force an explicit semidihedral presentation of Q. -/
public theorem exists_semidihedral_of_isolated_four_of_weak_rank
    {G : Type*} [Group G] [Finite G] (S Q B E : Subgroup G)
    (hS : IsPGroup 2 S) [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 E]
    (hB : 8 ≤ Nat.card B) (hE : Nat.card E = 4)
    (hQS : Q ≤ S) (hEQ : E ≤ Q)
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (hiso : ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ S → W ≤ centralizer (E : Set G) → W = E)
    (hunique : ∃! t : centralizer (Q : Set G), orderOf t = 2)
    (hno : ¬ ∃ F : Subgroup G, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
      F ≤ Q ∧ Q ≤ normalizer (F : Set G)) :
    ∃ n : ℕ, 4 ≤ n ∧ Nat.card Q = 2 ^ n ∧
      ∃ a b : Q, orderOf a = 2 ^ (n - 1) ∧ orderOf b = 2 ∧
        b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧
        closure ({a, b} : Set Q) = ⊤ := by
  have hQ := hS.of_injective (inclusion hQS) (inclusion_injective hQS)
  let : IsElementaryAbelian 2 (E.subgroupOf Q) := IsElementaryAbelian.subgroupOf hEQ
  have hEQcard : Nat.card (E.subgroupOf Q) = 4 := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hEQ).toEquiv]
  rcases hQ.exists_dihedral_or_semidihedral_of_no_normal_four
    (no_normal_four_of_no_normalized_four Q hno) (E.subgroupOf Q) hEQcard with h | h
  · obtain ⟨n, hn⟩ := h
    exact (not_dihedral_of_isolated_four_of_weak_rank S Q B E hS hB hE hQS hEQ
      hBweak hiso hunique n hn).elim
  · exact h

/-- The two factors in the isolated weak-rank case: the local centralizer is
generalized quaternion, while Q is cyclic, generalized quaternion, or
semidihedral. The dihedral alternative has been excluded. -/
public theorem local_structure_of_isolated_fours_of_weak_rank
    {G : Type*} [Group G] [Finite G] (S Q B : Subgroup G)
    (hS : IsPGroup 2 S) [IsElementaryAbelian 2 B]
    (hB : 8 ≤ Nat.card B) (hQS : Q ≤ S)
    (hBweak : B ≤ Q ⊔ (S ⊓ centralizer (Q : Set G)))
    (hiso : ∀ V : Subgroup G, IsElementaryAbelian 2 V → Nat.card V = 4 → V ≤ Q →
      ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
        W ≤ S → W ≤ centralizer (V : Set G) → W = V)
    (hunique : ∃! t : centralizer (Q : Set G), orderOf t = 2)
    (hno : ¬ ∃ F : Subgroup G, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
      F ≤ Q ∧ Q ≤ normalizer (F : Set G)) :
    (∃ n : ℕ, 3 ≤ n ∧ Nonempty
      ((S ⊓ centralizer (Q : Set G) : Subgroup G) ≃* QuaternionGroup (2 ^ (n - 2)))) ∧
    (IsCyclic Q ∨
      (∃ n : ℕ, 3 ≤ n ∧ Nonempty (Q ≃* QuaternionGroup (2 ^ (n - 2)))) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nat.card Q = 2 ^ n ∧
        ∃ a b : Q, orderOf a = 2 ^ (n - 1) ∧ orderOf b = 2 ∧
          b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧
          closure ({a, b} : Set Q) = ⊤)) := by
  refine ⟨exists_quaternion_centralizer_of_unique_involution S Q hS hunique
    (not_isCyclic_centralizer_of_isolated_fours_of_weak_rank S Q B hB hQS hBweak hiso), ?_⟩
  by_cases hfour : ∃ E : Subgroup Q, IsElementaryAbelian 2 E ∧ Nat.card E = 4
  · obtain ⟨E, hEe, hE⟩ := hfour
    let : IsElementaryAbelian 2 E := hEe
    let V := E.map Q.subtype
    let : IsElementaryAbelian 2 V := IsElementaryAbelian.map_subtype
    have hV : Nat.card V = 4 := by
      simpa only [V, card_map_of_injective Q.subtype_injective] using hE
    have hVQ : V ≤ Q := map_subtype_le _
    exact Or.inr (Or.inr (exists_semidihedral_of_isolated_four_of_weak_rank S Q B V
      hS hB hV hQS hVQ hBweak (hiso V inferInstance hV hVQ) hunique hno))
  · have hQ := hS.of_injective (inclusion hQS) (inclusion_injective hQS)
    rcases hQ.isCyclic_or_quaternion_of_no_elementary_four
      (fun E hEe hE => hfour ⟨E, hEe, hE⟩) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end Subgroup
