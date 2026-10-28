module

public import GorensteinWalter.PGL2InnerAction
public import Mathlib.GroupTheory.Nilpotent

/-!
# Recognition of simple nonsolvable D-groups

A finite simple nonsolvable D-group of even order is isomorphic to `A₇`
or to `PSL₂(K)` over an odd finite field in the same universe. This is the
simple-group elimination of Bender's D-group alternatives recorded in
`GorensteinWalter.Classification`, for use after the Gorenstein--Walter
classification supplies the D-group hypothesis.

Simplicity and even order kill the odd core. The two-group alternative is
nilpotent and hence solvable. In the linear alternative, a normal subgroup
of odd index must be the whole group: the trivial subgroup has even index.
Finally, the canonical `PSL₂` image in `PGL₂` has index two. Simplicity
would make that image trivial or full; these force order two or index one,
respectively, and both contradict the hypotheses.
-/

noncomputable section

namespace GorensteinWalter

universe u

/-- The nonsolvable simple members of the even-order D-group class are actual
`A₇` or odd-field `PSL₂` models. -/
public theorem simple_dgroup_recognition
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (heven : Even (Nat.card G))
    (hD : IsDGroup G) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
      ∃ (K : Type u) (instK : Field K) (_ : Finite K),
        let : Field K := instK
        Odd (Nat.card K) ∧ Nonempty (G ≃* PSL2 K) := by
  have hcore := pPrimeCore_eq_bot_of_simple_of_even (G := G) heven.two_dvd
  let eQ : G ≃* (G ⧸ pPrimeCore 2 G) :=
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans
      (QuotientGroup.quotientBot (G := G))).symm
  let : IsSimpleGroup (G ⧸ pPrimeCore 2 G) := eQ.symm.isSimpleGroup
  rcases hD with ⟨_, htwo⟩ | ⟨_, ⟨eA⟩⟩ |
    ⟨_, K, hK, L, hLnormal, hLindex, hLmodel⟩
  · have hGtwo : IsPGroup 2 G := htwo.of_equiv eQ.symm
    let : Group.IsNilpotent G := hGtwo.isNilpotent
    exact (hns inferInstance).elim
  · exact Or.inl ⟨eQ.trans eA⟩
  · have hLtop : L = ⊤ := by
      rcases hLnormal.eq_bot_or_eq_top with hbot | htop
      · have hodd : Odd (Nat.card G) := by
          rw [hbot, Subgroup.index_bot] at hLindex
          rwa [← Nat.card_congr eQ.toEquiv] at hLindex
        exact (hodd.not_two_dvd_nat heven.two_dvd).elim
      · exact htop
    let eL : G ≃* L := eQ.trans
      ((Subgroup.topEquiv : (⊤ : Subgroup (G ⧸ pPrimeCore 2 G)) ≃*
        (G ⧸ pPrimeCore 2 G)).symm.trans (MulEquiv.subgroupCongr hLtop.symm))
    rcases hLmodel with hPSL | hPGL
    · refine Or.inr ⟨K, inferInstance, inferInstance, ?_, ⟨eL.trans hPSL.some⟩⟩
      rcases hK with ⟨p, n, _, hpodd, _, hcard⟩
      rw [hcard]
      exact hpodd.pow
    · let e : G ≃* PGL2 K := eL.trans hPGL.some
      let : IsSimpleGroup (PGL2 K) := e.symm.isSimpleGroup
      let H : Subgroup (PGL2 K) :=
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range
      have hHindex : H.index = 2 := pgl2_psl2Range_index_eq_two K hK
      have hHnormal : H.Normal := H.normal_of_index_eq_two hHindex
      rcases hHnormal.eq_bot_or_eq_top with hbot | htop
      · have hcard : Nat.card G = 2 := by
          rw [hbot, Subgroup.index_bot] at hHindex
          exact (Nat.card_congr e.toEquiv).trans hHindex
        have hGtwo : IsPGroup 2 G := IsPGroup.of_card (n := 1) (by simpa using hcard)
        let : Group.IsNilpotent G := hGtwo.isNilpotent
        exact (hns inferInstance).elim
      · rw [htop, Subgroup.index_top] at hHindex
        norm_num at hHindex

end GorensteinWalter
