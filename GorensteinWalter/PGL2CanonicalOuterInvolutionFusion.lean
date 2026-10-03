module

public import GorensteinWalter.DihedralOuterInvolutionConjugacy
public import GorensteinWalter.PGL2DihedralSylowParameter
public import GorensteinWalter.PSL2DihedralSylow
public import GorensteinWalter.PGL2InnerAction
public import BenderSuzuki.External.Hall.Basic
public import Mathlib.Tactic

/-!
# Outer involution conjugacy for all odd projective fields

For every finite field of odd prime-power order, involutions outside the
canonical PSL2 image in PGL2 form one conjugacy class, including orders
three and nine. The subgroup is the actual range of the canonical map.

Place both involutions into one Sylow two-subgroup by conjugacy. Its
intersection with the canonical PSL2 image is normal of index two and
noncyclic: the corresponding PSL2 Sylow subgroup is dihedral of order at
least four. The proved dihedral reflection-class theorem therefore fuses
the two exterior involutions. This generalizes the previous commutator
formulation without using a lower bound on field order.

This supplies the exterior-involution alignment in Alperin--Brauer--
Gorenstein II.3 Proposition3, article p27 (PDF page28). The historical
large-field commutator theorem is retained in PGL2OuterInvolutionFusion
as a wrapper using the proved equality with the canonical image.
-/

noncomputable section

namespace GorensteinWalter

open Matrix
open scoped MatrixGroups Pointwise

universe u

/-- Over every finite odd field, involutions outside the canonical PSL2 image are conjugate. -/
public theorem pgl2_outer_involutions_conjugate_of_odd_prime_power
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    {a b : PGL2 K} (ha : IsInvolution a) (hb : IsInvolution b)
    (haJ : a ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range)
    (hbJ : b ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range) :
    IsConj a b := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haord : orderOf a = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using ha.2) ha.1
  have hbord : orderOf b = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hb.2) hb.1
  have hA2 : IsPGroup 2 (Subgroup.zpowers a) := by
    apply IsPGroup.of_card (n := 1)
    simp [Nat.card_zpowers, haord]
  have hB2 : IsPGroup 2 (Subgroup.zpowers b) := by
    apply IsPGroup.of_card (n := 1)
    simp [Nat.card_zpowers, hbord]
  obtain ⟨Sa, hASa⟩ := IsPGroup.exists_le_sylow hA2
  obtain ⟨Sb, hBSb⟩ := IsPGroup.exists_le_sylow hB2
  have haSa : a ∈ (Sa : Subgroup (PGL2 K)) :=
    hASa (Subgroup.mem_zpowers a)
  have hbSb : b ∈ (Sb : Subgroup (PGL2 K)) :=
    hBSb (Subgroup.mem_zpowers b)
  obtain ⟨g, hg⟩ :=
    @MulAction.IsPretransitive.exists_smul_eq (PGL2 K)
      (Sylow 2 (PGL2 K)) inferInstance inferInstance Sb Sa
  let b' : PGL2 K := g * b * g⁻¹
  have hb'Sa : b' ∈ (Sa : Subgroup (PGL2 K)) := by
    change (MulAut.conj g) b ∈ (Sa : Subgroup (PGL2 K))
    rw [← hg]
    change (MulAut.conj g) b ∈
      (Sb : Subgroup (PGL2 K)).map (MulAut.conj g).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨b, hbSb, rfl⟩
  have hb'I : IsInvolution b' := by
    constructor
    · intro hb'one
      apply hb.1
      calc
        b = g⁻¹ * b' * g := by simp [b']; group
        _ = 1 := by rw [hb'one]; simp
    · simpa [b'] using congrArg (MulAut.conj g) hb.2
  let J : Subgroup (PGL2 K) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range
  let H : Subgroup Sa := J.subgroupOf (Sa : Subgroup (PGL2 K))
  have hJindex : J.index = 2 := pgl2_psl2Range_index_eq_two K hK
  let : J.Normal := J.normal_of_index_eq_two hJindex
  have hHindex : H.index = 2 := by
    have hdvd : H.index ∣ 2 := by
      change J.relIndex (Sa : Subgroup (PGL2 K)) ∣ 2
      simpa [hJindex] using
        (Subgroup.relIndex_dvd_index_of_normal
          (H := J) (K := (Sa : Subgroup (PGL2 K))))
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo
    · exfalso
      have htop : H = ⊤ := Subgroup.index_eq_one.mp hone
      apply haJ
      have haH : (⟨a, haSa⟩ : Sa) ∈ H := by rw [htop]; trivial
      exact haH
    · exact htwo
  have hHnoncyclic : ¬ IsCyclic H := by
    intro hHcyclic
    let T : Sylow 2 J :=
      BenderSuzuki.External.hallSylowSubgroupOfNormal Sa J
    let eHT : H ≃* T :=
      { toFun := fun x =>
          ⟨⟨((x : Sa) : PGL2 K), x.property⟩, by
            rw [BenderSuzuki.External.hallSylowSubgroupOfNormal_coe]
            exact (x : Sa).property⟩
        invFun := fun y =>
          ⟨⟨((y : J) : PGL2 K), by
              let yJ : J := y
              have hy : yJ ∈ (T : Subgroup J) := y.property
              rw [BenderSuzuki.External.hallSylowSubgroupOfNormal_coe] at hy
              exact hy⟩,
            (y : J).property⟩
        left_inv := by intro x; rfl
        right_inv := by intro y; rfl
        map_mul' := by intro x y; rfl }
    have hTcyclic : IsCyclic T := eHT.isCyclic.mp hHcyclic
    let eJ : J ≃* PSL2 K := (psl2EquivToPGLRange K).symm
    let Tmodel : Sylow 2 (PSL2 K) :=
      T.mapSurjective (f := eJ.toMonoidHom) eJ.surjective
    have hTmodelCyclic : IsCyclic Tmodel := by
      let eTmap : T ≃* (T : Subgroup J).map eJ.toMonoidHom :=
        Subgroup.equivMapOfInjective
          (T : Subgroup J) eJ.toMonoidHom eJ.injective
      have hcoe : (T : Subgroup J).map eJ.toMonoidHom =
          (Tmodel : Subgroup (PSL2 K)) := by
        symm
        exact Sylow.coe_mapSurjective
          (f := eJ.toMonoidHom) eJ.surjective T
      let eT : T ≃* Tmodel :=
        eTmap.trans (MulEquiv.subgroupCongr hcoe)
      exact eT.isCyclic.mp hTcyclic
    obtain ⟨n, hn, ⟨eD⟩⟩ :=
      psl2_odd_hasDihedralSylowTwo_model K hK Tmodel
    have hDcyclic : IsCyclic (DihedralGroup (2 ^ n)) :=
      eD.isCyclic.mp hTmodelCyclic
    apply DihedralGroup.not_isCyclic
      (show 2 ^ n ≠ 1 by
        exact ne_of_gt
          (Nat.one_lt_pow (by omega : n ≠ 0) (by norm_num : 1 < 2)))
    exact hDcyclic
  obtain ⟨m, _hm, ⟨eSa⟩⟩ :=
    pgl2_odd_hasDihedralSylowTwo_model K hK Sa
  have hm2 : 2 ≤ m :=
    pgl2_dihedral_sylow_parameter_ge_two K hK Sa eSa
  have hb'J : b' ∉ J := by
    intro hb'mem
    apply hbJ
    have hback : g⁻¹ * b' * (g⁻¹)⁻¹ ∈ J :=
      (inferInstance : J.Normal).conj_mem b' hb'mem g⁻¹
    have heq : g⁻¹ * b' * (g⁻¹)⁻¹ = b := by simp [b']; group
    rwa [heq] at hback
  let aS : Sa := ⟨a, haSa⟩
  let bS : Sa := ⟨b', hb'Sa⟩
  have haSI : IsInvolution aS := by
    exact ⟨fun h => ha.1 (congrArg Subtype.val h), Subtype.ext ha.2⟩
  have hbSI : IsInvolution bS := by
    exact ⟨fun h => hb'I.1 (congrArg Subtype.val h), Subtype.ext hb'I.2⟩
  have haSH : aS ∉ H := haJ
  have hbSH : bS ∉ H := hb'J
  have hconjS : IsConj aS bS :=
    dihedral_involutions_not_mem_noncyclic_index_two_isConj
      hm2 eSa H hHindex hHnoncyclic haSI hbSI haSH hbSH
  have hconjAmbient :=
    MonoidHom.map_isConj (Sa : Subgroup (PGL2 K)).subtype hconjS
  change IsConj a b' at hconjAmbient
  have hbb' : IsConj b b' := isConj_iff.mpr ⟨g, rfl⟩
  exact hconjAmbient.trans hbb'.symm

end GorensteinWalter
