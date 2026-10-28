module

public import Theory.GroupTheory.PGroup.RankOneInvolution
public import Theory.GroupTheory.SpecificGroups.GeneralizedQuaternionAut
public import Theory.GroupTheory.Fitting.PCoreAutomorphisms
public import Theory.GroupTheory.PGroup.UniqueInvolutionClassification

/-!
# The two-core of a solvable rank-one centralizer

A finite solvable group with trivial odd core and no elementary four is a
two-group unless its two-core is quaternion of order eight. The Fitting
subgroup equals the two-core and is self-centralizing. The absence of
an elementary four gives a unique involution in that core, so Huppert
III.8.2 makes it cyclic or generalized quaternion. In the cyclic case and
in quaternion orders greater than eight, its automorphism group is a
two-group, forcing the whole group to be a two-group.

This is the intrinsic group-theoretic structure step in the binary
centralizer rank-one reduction (GLS, Number 2, Proposition 22.4).
-/

namespace Group

/-- A solvable group with trivial odd core and no elementary four is a
two-group, or its two-core is quaternion of order eight. -/
public theorem isPGroup_or_pCore_quaternion_of_rank_one
    {C : Type*} [Group C] [Finite C]
    (hsolv : Group.IsSolvable C) (hodd : pPrimeCore 2 C = ⊥)
    (hrank : ∀ F : Subgroup C, IsElementaryAbelian 2 F → Nat.card F < 4) :
    IsPGroup 2 C ∨ Nonempty (pCore 2 C ≃* QuaternionGroup 2) := by
  classical
  let P := pCore 2 C
  have hP : IsPGroup 2 P := pCore_isPGroup
  have hcollapse (haut : IsPGroup 2 (MulAut P)) : IsPGroup 2 C :=
    isPGroup_of_pPrimeCore_eq_bot_of_mulAut_pCore hsolv hodd haut
  rcases subsingleton_or_nontrivial P with htriv | hnontriv
  · let := htriv
    let : Subsingleton (MulAut P) := ⟨fun f g => MulEquiv.ext fun _ => Subsingleton.elim _ _⟩
    exact Or.inl (hcollapse (IsPGroup.of_subsingleton 2 (MulAut P)))
  let := hnontriv
  have hfour : ∀ V : Subgroup P, IsElementaryAbelian 2 V → Nat.card V ≠ 4 := by
    intro V hV
    let := hV
    have hlt := hrank (V.map P.subtype) IsElementaryAbelian.map_subtype
    rw [Subgroup.card_map_of_injective P.subtype_injective] at hlt
    omega
  rcases hP.isCyclic_or_quaternion_of_no_elementary_four hfour with hcyclic | ⟨n, hn, ⟨e⟩⟩
  · let := hcyclic
    exact Or.inl (hcollapse hP.mulAut_of_isCyclic_two)
  by_cases hn3 : n = 3
  · subst n
    exact Or.inr ⟨e⟩
  left
  apply hcollapse
  have hlarge : 2 < 2 ^ (n - 2) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ < 2 ^ (n - 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact (QuaternionGroup.isPGroup_mulAut_of_two_lt hlarge (hP.of_equiv e)).of_equiv
    (MulAut.congr e.symm)

end Group
