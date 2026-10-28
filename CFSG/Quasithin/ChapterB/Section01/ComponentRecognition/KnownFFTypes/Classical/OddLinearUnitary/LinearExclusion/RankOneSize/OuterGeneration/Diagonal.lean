module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration.Models
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration.Diagonal.Maximal
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration.Diagonal.Generation
public import GorensteinWalter.PGL2LowTorus
public import GorensteinWalter.ReflectedCyclicIndexTwoSubgroup
public import GorensteinWalter.PGL2CanonicalOuterInvolutionFusion
public import Theory.GroupTheory.ThreeConjugateGeneration

/-!
# Four inner conjugates of a diagonal outer involution

Choose the split or nonsplit PGL₂ torus whose order is twice an odd number.
Its exterior involution centralizes the inner dihedral normalizer. This
normalizer is maximal in PSL₂ at the prime and quadratic parameters here.
Multiplying its two generating involutions by the torus involution gives
three exterior involutions. Fusion supplies a fourth that fails to commute
with the first, so the four generate a subgroup containing PSL₂.

Index two permits every fusion conjugator to be chosen in the literal PSL₂
range. The last theorem transports these witnesses through the canonical
linear inclusion into PGammaL₂, proving the exact contract in Models.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.1,
manuscript pp.8--9; Aschbacher--Smith K.2, printed p.453. The torus and
maximality inputs use Huppert II.8.4 and II.8.27.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration
open Subgroup GorensteinWalter
universe u

/-- The calculation in PGL₂ retains the canonical PSL₂ subgroup as its
conjugator type. Both torus orientations are covered by the same construction. -/
theorem diagonal_four_pgl {F : Type u} [Field F] [Finite F]
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e = 1 ∨ e = 2)
    (hF : Nat.card F = p ^ e) (hlarge : 25 < p ^ e)
    (t : PGL2 F)
    (htN : t ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := F)).range) (ht2 : t ^ 2 = 1) :
    ∃ c : Fin 4 → (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := F)).range,
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := F)).range ≤ closure (Set.range fun j =>
          (c j : PGL2 F) * t * (c j : PGL2 F)⁻¹) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  have hK : IsOddPrimePower (Nat.card F) := ⟨p, e, hp, ho, by omega, hF⟩
  have hcard : 3 < Nat.card F := by omega
  let N : Subgroup (PGL2 F) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
  have hindex : N.index = 2 := pgl2_psl2Range_index_eq_two F hK
  have hcomm : commutator (PGL2 F) = N :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three F hK hcard
  obtain ⟨U, s, w, _, hUcyc, hUhalf, hUorder, hsU, hsN, hsne, hs2,
    hwN, hwU, hw2, hwinv, _⟩ := pgl2_low_two_part_torus_reflection_data F hK hcard
  rw [hcomm] at hsN hwN
  have hUtwo : Nat.card U = 2 * (Nat.card U / 2) := by
    have hqodd : Odd (Nat.card F) := hF ▸ ho.pow
    obtain ⟨k, hk⟩ := hqodd
    rcases hUorder with h | h <;> omega
  obtain ⟨D, hDeq, hDN, _, hDcard, ⟨eD⟩⟩ :=
    exists_dihedral_subgroup_le_index_two_of_reflected_cyclic N U hindex hUcyc
      (Nat.card U / 2) hUtwo (fun h => hsN (h hsU)) w hwN hwU hw2 hwinv
  let eN : PSL2 F ≃* N := psl2EquivToPGLRange F
  let D0 : Subgroup (PSL2 F) := (D.subgroupOf N).map eN.symm.toMonoidHom
  have hD0card : Nat.card D0 = Nat.card D := by
    calc
      Nat.card D0 = Nat.card (D.subgroupOf N) :=
        (Nat.card_congr (Subgroup.equivMapOfInjective (D.subgroupOf N)
          eN.symm.toMonoidHom eN.symm.injective).toEquiv).symm
      _ = Nat.card D := Nat.card_congr (subgroupOfEquivOfLe hDN).toEquiv
  have hmax0 : IsCoatom D0 := Diagonal.low_torus_isCoatom ho he hF hlarge D0
    (by rwa [hD0card, hDcard]) (by rwa [hD0card, hDcard])
  have hmax : IsCoatom (D.subgroupOf N) :=
    (OrderIso.isCoatom_iff eN.symm.mapSubgroup (D.subgroupOf N)).mp hmax0
  let R : Subgroup (PGL2 F) := U ⊓ N
  let : IsCyclic U := hUcyc
  let : IsCyclic R := Subgroup.isCyclic_of_le (show R ≤ U from inf_le_left)
  obtain ⟨a, b, _, ha2, _, hb2, habgen⟩ :=
    Theory.GroupTheory.ThreeConjugateGeneration.pair_of_cyclic_inverter R w
      (fun hw => hwU hw.1) (by simpa only [pow_two] using hw2)
      (fun x hx => hwinv x hx.1)
  have habD : closure ({a, b} : Set (PGL2 F)) = D := habgen.trans hDeq.symm
  have haD : a ∈ D := habD ▸ subset_closure (by simp)
  have hbD : b ∈ D := habD ▸ subset_closure (by simp)
  have hDcent : D ≤ centralizer ({s} : Set (PGL2 F)) := by
    rw [hDeq]
    apply sup_le
    · intro x hx
      let : CommGroup U := IsCyclic.commGroup
      exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (mul_comm (⟨x, hx.1⟩ : U) (⟨s, hsU⟩ : U)))
    · apply zpowers_le.mpr
      apply mem_centralizer_singleton_iff.mpr
      have hh := hwinv s hsU
      rw [inv_eq_of_mul_eq_one_right hs2] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
  have hab : ¬ Commute a b := by
    intro hab
    have hpair : IsMulCommutative (closure ({a, b} : Set (PGL2 F))) :=
      Subgroup.isMulCommutative_closure (by
        intro x hx y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · rfl
        · exact hab.eq
        · exact hab.symm.eq
        · rfl)
    let : IsMulCommutative D := habD ▸ hpair
    have hmodel : IsMulCommutative (DihedralGroup (Nat.card U / 2)) :=
      IsMulCommutative.of_comm (fun x y => by
        apply eD.symm.injective
        simp only [map_mul]
        exact mul_comm' _ _)
    have hUlarge : 24 < Nat.card U := by rcases hUorder with h | h <;> omega
    exact DihedralGroup.not_commutative (by omega) (by omega) hmodel
  have hfuse (x y : PGL2 F) (hxN : x ∉ N) (hx2 : x ^ 2 = 1)
      (hyN : y ∉ N) (hy2 : y ^ 2 = 1) : IsConj x y :=
    pgl2_outer_involutions_conjugate_of_odd_prime_power F hK
      ⟨fun h => hxN (by simpa only [h] using N.one_mem), by simpa only [pow_two] using hx2⟩
      ⟨fun h => hyN (by simpa only [h] using N.one_mem), by simpa only [pow_two] using hy2⟩ hxN hyN
  exact Diagonal.four_of_maximal_centralized_pair N hindex hfuse s a b hsN
    (by simpa only [pow_two] using hs2) (hDN haD) ha2 (hDN hbD) hb2
    (mem_centralizer_singleton_iff.mp (hDcent haD)).symm
    (mem_centralizer_singleton_iff.mp (hDcent hbD)).symm hab
    (by rwa [habD]) t htN ht2

/-- Four PSL₂ conjugates of every diagonal outer involution contain the
literal canonical PSL₂ range in PGammaL₂. -/
theorem diagonalFourGeneration : DiagonalFourGeneration.{u} := by
  intro F _ _ p e hp ho he hF hlarge t htN ht2 hright
  let i : PGL2 F →* PGammaL2 F := SemidirectProduct.inl
  have htlin : i t.left = t := SemidirectProduct.ext rfl hright.symm
  have htleftN : t.left ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := F)).range := by
    rintro ⟨x, hx⟩
    apply htN
    exact ⟨x, (congrArg i hx).trans htlin⟩
  have htleft2 : t.left ^ 2 = 1 := by
    apply SemidirectProduct.inl_injective (φ := pgl2FieldAut F)
    change i (t.left ^ 2) = i 1
    rw [map_pow, htlin, ht2, map_one]
  obtain ⟨c, hc⟩ := diagonal_four_pgl hp ho he hF hlarge t.left htleftN htleft2
  let E := psl2EquivToPGLRange F
  have hval (j : Fin 4) : Matrix.ProjectiveSpecialLinearGroup.toPGL (E.symm (c j)) =
      (c j : PGL2 F) := by
    calc
      Matrix.ProjectiveSpecialLinearGroup.toPGL (E.symm (c j)) =
          (E (E.symm (c j))).val := (psl2EquivToPGLRange_val F _).symm
      _ = (c j).val := congrArg Subtype.val (E.apply_symm_apply (c j))
  refine ⟨fun j => E.symm (c j), ?_⟩
  have hh := Subgroup.map_mono (f := i) hc
  simpa only [pGammaL2PSLRange, MonoidHom.range_comp, MonoidHom.map_closure,
    ← Set.range_comp, Function.comp_def, map_mul, map_inv, hval, htlin] using hh

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration
