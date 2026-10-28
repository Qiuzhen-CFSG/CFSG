module

public import ABG.ChapterII.Section1.WreathedFusion
public import Theory.GroupTheory.WreathedThirtyTwo
public import Theory.GroupTheory.PGroup.TrivialImage
public import Theory.GroupTheory.PResidual.NormalComplement
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The two-residual of a group with Sylow C4 wreath C2

The four proved wreathed fusion cases identify the actual two-residual:
it is the whole group, has odd order, has generalized quaternion Sylow
subgroups, or has Sylow subgroup C4 times C4. In the two kernel cases,
absence of a further normal subgroup of index two identifies the fusion
kernel with the residual through its literal quotient map.

Source: Alperin--Brauer--Gorenstein II.1 Proposition 2, article pp.11--13;
the height-two specialization used in Aschbacher--Smith F.6.18, p.310.
-/

public noncomputable section
open Subgroup ABG
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem residual_eq_of_no_index_two (K : Subgroup G) [K.Normal]
    (hq : IsPGroup 2 (G ⧸ K)) (hno : HasNoNormalIndexTwoSubgroup K) :
    pResidual 2 G = K := by
  refine le_antisymm (sInf_le ⟨inferInstance, hq⟩) ?_
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  exact MonoidHom.eq_one_of_no_normal_index_prime hno
    (isPGroup_quotient_pResidual 2)
    ((QuotientGroup.mk' (pResidual 2 G)).comp K.subtype) ⟨x, hx⟩

private theorem residual_top_of_no_index_two (hno : HasNoNormalIndexTwoSubgroup G) :
    pResidual 2 G = ⊤ := by
  apply top_unique
  intro x _
  apply (QuotientGroup.eq_one_iff x).mp
  exact MonoidHom.eq_one_of_no_normal_index_prime hno
    (isPGroup_quotient_pResidual 2) (QuotientGroup.mk' (pResidual 2 G)) x

theorem wreathedThirtyTwo_twoResidual_cases (S : Sylow 2 G) (eS : S ≃* WreathedThirtyTwo) :
    pResidual 2 G = ⊤ ∨ Odd (Nat.card (pResidual 2 G)) ∨
      HasGeneralizedQuaternionSylowTwo (pResidual 2 G) ∨
      ∃ R : Sylow 2 (pResidual 2 G),
        Nonempty (R ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  have hS : IsWreathedOfHeight S 2 :=
    wreathed_equiv eS.symm RegularWreathHeightTwo.isWreathedOfHeight
  obtain ⟨P⟩ := Wreathed.nonempty_presentation hS
  let U := P.U.map (S : Subgroup G).subtype
  let V := P.V.map (S : Subgroup G).subtype
  have hf := P.fusionFrame S
  have hF := Wreathed.focal_subgroup_cases S P
  rcases Wreathed.u_automizer_index S 2 U V hf with hU | hU <;>
    rcases Wreathed.v_outer_automizer_index S 2 U V hf with hV | hV
  · have hc : HasNormalPComplement 2 G :=
      hasNormalTwoComplement_of_cyclic_focalSubgroupOf S (by
        rw [hF.1 hU hV]
        exact P.derived_structure.2.1)
    right; left
    rw [pResidual_eq_pPrimeCore_of_hasNormalPComplement hc]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  · have he := hF.2.1 hU hV
    let : P.Y.Normal := P.quaternion_subgroup.2.2
    let : IsCyclic (S ⧸ (S : Subgroup G).focalSubgroupOf) := by
      let : IsCyclic (S ⧸ P.Y) := P.quaternion_quotient.1
      exact isCyclic_of_injective
        (QuotientGroup.quotientMulEquivOfEq he).toMonoidHom
        (QuotientGroup.quotientMulEquivOfEq he).injective
    obtain ⟨K, hK, hi, hno, _, R, _, ⟨a⟩⟩ :=
      exists_normal_sylow_of_cyclic_focal_quotient S
    let : K.Normal := hK
    have hi' : K.index = 2 ^ 2 := by rw [hi, he]; exact P.quaternion_quotient.2
    have hres := residual_eq_of_no_index_two K (IsPGroup.of_card hi') hno
    right; right; left
    rw [hres]
    obtain ⟨n, hn, ⟨b⟩⟩ := P.quaternion_subgroup.1
    exact ⟨R, n, hn, ⟨a.trans ((MulEquiv.subgroupCongr he).trans b)⟩⟩
  · obtain ⟨K, hK, hi, hno, R, _, ⟨a⟩⟩ :=
      exists_normal_index_two_sylow_of_focalSubgroupOf S P.U P.index_U (hF.2.2.1 hU hV)
    let : K.Normal := hK
    have hres := residual_eq_of_no_index_two K (IsPGroup.of_card (n := 1) (by
      change Nat.card (G ⧸ K) = 2 at hi
      simpa only [pow_one] using hi)) hno
    right; right; right
    rw [hres]
    exact ⟨R, ⟨a.trans P.baseEquiv⟩⟩
  · exact Or.inl (residual_top_of_no_index_two
      (no_normal_index_two_of_focal_top S (hF.2.2.2 hU hV)))

end Theory.GroupTheory
