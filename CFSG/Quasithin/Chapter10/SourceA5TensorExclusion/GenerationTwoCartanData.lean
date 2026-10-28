module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoData
public import Theory.SpecificGroups.SL2.CubicFixedVectors

/-!
# Cartan containment in the original generation-two overgroup

A nonidentity cubic in the original component fixes no nonidentity vector
of the tensor module. Consequently the Hall cubic centralizing the tensor
line differs from the Cartan cubic in the component. Their orders force
them to generate the order-nine Cartan, placing that Cartan in the actual
join of the component and old residual. The existing H-star member supplies
the outside-overgroup guard and hence the tensor line in the Omega orbit.

Source: Aschbacher--Smith 9.2.7 and 9.3.6, printed pp.731--734.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

include m in
private theorem component_cubic_fixed_eq_one
    (b : L) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (v : D.fullModule) (hv : (b : G) * v = (v : G) * b) : v = 1 := by
  let q := m.firstMarking.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  have hq1 : q b ≠ 1 := by
    intro hh
    have hb : b ∈ pCore 2 L := by
      change m.firstMarking (e (QuotientGroup.mk' (pCore 2 L) b)) = 1 at hh
      exact (QuotientGroup.eq_one_iff (N := pCore 2 L) b).mp
        (e.map_eq_one_iff.mp (m.firstMarking.map_eq_one_iff.mp hh))
    have hc : (⟨b,hb⟩ : pCore 2 L) ^ 3 = 1 := Subtype.ext hb3
    have he := ((pCore_isPGroup (p := 2) (G := L)).powEquiv
      (by decide : Nat.Coprime 2 3)).injective (hc.trans (one_pow 3).symm)
    exact hb1 (congrArg Subtype.val he)
  have hord : orderOf (q b) = 3 := orderOf_eq_prime (by rw [←map_pow,hb3,map_one]) hq1
  have hf := m.sectionData.equivariant ⟨b,le_componentOrbit L T b.property⟩ v
  have he : (⟨(b : G)*v*(b : G)⁻¹,
      (mem_normalizer_iff.mp (m.sectionData.normalized (le_componentOrbit L T b.property)) v).mp v.property⟩ : D.fullModule) = v := by
    apply Subtype.ext
    change (b : G)*v*(b : G)⁻¹ = v
    rw [hv,mul_inv_cancel_right]
  change (m.sectionData.coordinates ⟨(b : G)*v*(b : G)⁻¹, _⟩).toAdd =
      Binary.action (m.quotient ⟨b,le_componentOrbit L T b.property⟩)
        (m.sectionData.coordinates v).toAdd at hf
  rw [he,m.first_factor] at hf
  have hact : Binary.action (q b,1) (m.sectionData.coordinates v).toAdd =
      (m.sectionData.coordinates v).toAdd := by
    exact hf.symm
  have hl : (q b).val * (m.sectionData.coordinates v).toAdd =
      (m.sectionData.coordinates v).toAdd := by
    simpa only [Binary.action_apply,inv_one,Matrix.SpecialLinearGroup.coe_one,mul_one] using hact
  have hz : (m.sectionData.coordinates v).toAdd = 0 := by
    funext i j
    exact congrFun (Matrix.SL2.cubic_fixed_eq_zero (q b) hord
      (fun k => (m.sectionData.coordinates v).toAdd k j) (by
        funext k
        exact congrArg (fun A : Binary.V => A k j) hl)) i
  apply Subtype.ext
  exact (m.sectionData.coordinates_eq_one_iff v).mp (Multiplicative.toAdd.injective hz)

namespace GenerationTwoOvergroup
variable {m} (c : m.GenerationTwoOvergroup)

/-- The source diagonal Hall cubic and the original component generate the Cartan. -/
theorem cartan_le_component_sup_residual : c.A ≤ L ⊔ (pResidual 2 c.H).map c.H.subtype := by
  obtain ⟨C,hCA,hCL,hC3⟩ := m.old_residual_cartan_component_cubic c.A c.borel c.card_cartan
  have hBC : c.B ≠ C := by
    intro he
    have hn : C ≠ ⊥ := by intro hz; rw [hz,card_bot] at hC3; omega
    obtain ⟨b,hb⟩ := ne_bot_iff_exists_ne_one.mp hn
    obtain ⟨z,hz2,hzU,_⟩ := m.exists_central_involution_tensorLine
    have hfix := m.component_cubic_fixed_eq_one ⟨b,hCL b.property⟩
      (Subtype.ext (congrArg (fun x : C => (x : G)) (show b^3 = 1 from hC3 ▸ pow_card_eq_one')))
      (fun hh => hb (Subtype.ext (congrArg (fun x : L => (x : G)) hh)))
      ⟨z,m.tensorLine_le_fullModule hzU⟩
      ((show (b : G) ∈ centralizer (m.tensorLine : Set G) from
        (c.hall_centralizer ▸ (show (b : G) ∈ c.B from he ▸ b.property)).2) z hzU).symm
    have hz1 : z = 1 := congrArg Subtype.val hfix
    rw [hz1,orderOf_one] at hz2
    omega
  have hlt : C < C ⊔ c.B := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro he
    have hle : c.B ≤ C := he ▸ le_sup_right
    exact hBC (eq_of_le_of_card_ge hle (by rw [hC3,c.card_hall]))
  have hsup : C ⊔ c.B = c.A := by
    apply eq_of_le_of_card_ge (sup_le hCA c.hall_le_cartan)
    have hd : Nat.card (C ⊔ c.B : Subgroup G) ∣ 9 :=
      c.card_cartan ▸ card_dvd_of_le (sup_le hCA c.hall_le_cartan)
    have hl : 3 < Nat.card (C ⊔ c.B : Subgroup G) := by
      by_contra! hn
      exact hlt.ne (eq_of_le_of_card_ge le_sup_left (by rwa [hC3]))
    have hd' : Nat.card (C ⊔ c.B : Subgroup G) = 9 := by
      obtain ⟨k,hk,hke⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (show Nat.card (C ⊔ c.B : Subgroup G) ∣ 3^2 from hd)
      interval_cases k <;> norm_num only [Nat.reducePow] at hke <;> omega
    rw [hd',c.card_cartan]
  rw [←hsup]
  exact sup_le (hCL.trans le_sup_left) (c.hall_le_residual.trans le_sup_right)

/-- The original Cartan lies in the actual generated overgroup. -/
theorem cartan_le : c.A ≤ c.M :=
  c.cartan_le_component_sup_residual.trans (c.generated ▸ le_sup_left)

include c in
/-- An existing H-star member supplies the standing outside-maximal-local guard. -/
theorem hasMaximalOutside : Chapter3.HasMaximalOutside T D.maximalLocal := by
  have hc : pCore 2 c.H ≠ ⊥ := by
    intro he
    apply c.hstar.1.1.1
    change (pCore 2 c.H).map c.H.subtype = ⊥
    rw [he,Subgroup.map_bot]
  obtain ⟨N,hN,hHN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot c.H hc
  exact Chapter3.hasMaximalOutside_of_two_distinct
    (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      D.simpleQTKE T D.maximal).normalizer_maximal hN
    (le_normalizer_componentOrbit L T) (c.hstar.1.1.2.trans hHN)
    (fun he => c.hstar.1.2 (he ▸ hHN))

/-- The tensor line lies in the literal Omega orbit used by the row contract. -/
theorem tensorLine_le_omegaOrbit : m.tensorLine.subgroupOf c.M ≤
    ChapterC.MSCentralOrbit.omegaOrbit
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M) := by
  obtain ⟨_,_,_,_,hr,hUW,_⟩ := c.fourField_models c.hasMaximalOutside
  exact hUW

end GenerationTwoOvergroup
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
