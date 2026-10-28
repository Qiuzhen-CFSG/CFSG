module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.ModelTransport
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.FourComponent.Lifting
public import Theory.GroupTheory.CubicThetaSimpleSection
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# A source local component above a linear-three quotient

Let Y be an overgroup of L₁T inside H containing O₂(H), with
Y/O₂(Y) identified with PSL₃(2). The component correspondence constructs
a normal C-component K₁ of Y containing O²(Y). Two-perfectness places L₁
inside K₁, and the Sylow supplement gives Y = K₁T. Since H/K is a
two-group, perfectness also places K₁ inside the original K.

The cubic theta obstruction proves Y is outside M; O₂(H) supplies its
nontrivial two-core. These establish all clauses of the literal family Hz.
The equivalence of the intrinsic quotient of K₁ retains the original
quotient map on every representative.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.25,
printed p.959 (PDF p.976). The cubic quotient and theta identity are
explicit algebraic premises, to be discharged by the source assembly.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open Chapter1
variable {G : Type*} [Group G] [Finite G]

/-- Construct the local component and prove every Hz clause from the
specified whole quotient, the Sylow subgroup and the source theta identity. -/
theorem source_component_of_linear_three_quotient
    (H K L₁ T G₁ M Y : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M)
    (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal) (hgen : H = K ⊔ T)
    (hSyl : IsSylowIn 2 T H)
    (hYH : Y ≤ H) (hbase : L₁ ⊔ T ≤ Y) (hcore : Source.QH H ≤ Y)
    (hL : IsPPerfect 2 L₁) (hcard : Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (eY : (Y ⧸ pCore 2 Y) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    ∃ (K₁ : Subgroup G) (hK₁Y : K₁ ≤ Y),
      K₁ ≤ K ∧ L₁ ≤ K₁ ∧ Y ≤ normalizer (K₁ : Set G) ∧
      Y = K₁ ⊔ T ∧ (K₁.subgroupOf Y).IsCComponent ∧ Y ∈ Source.Hz L₁ T G₁ M ∧
      ∃ eK : (K₁ ⧸ pCore 2 K₁) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2),
        ∀ k : K₁, eK (QuotientGroup.mk' _ k) =
          eY (QuotientGroup.mk' _ (⟨k.val, hK₁Y k.property⟩ : Y)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTY : T ≤ Y := le_sup_right.trans hbase
  have hLY : L₁ ≤ Y := le_sup_left.trans hbase
  obtain ⟨K₁, hK₁Y, hC, hn, hr, eK, heK⟩ :=
    BinaryLinear.SmallParabolicLevi.FourComponent.exists_component_of_twoCoreQuotient Y eY
  have hLK₁ : L₁ ≤ K₁ := by
    have hp : IsPPerfect 2 (L₁.subgroupOf Y) := hL.of_surjective
      (subgroupOfEquivOfLe hLY).symm.toMonoidHom (subgroupOfEquivOfLe hLY).symm.surjective
    have h := map_mono (f := Y.subtype) (le_pResidual_of_isPPerfect (L₁.subgroupOf Y) hp)
    rw [map_subgroupOf_eq_of_le hLY] at h
    exact h.trans hr
  have hjoin : Y = K₁ ⊔ T := by
    obtain ⟨S, hS⟩ := hSyl.restrict hTY hYH
    have hres := congrArg (map Y.subtype) (pResidual_sup_sylow_eq_top S)
    rw [Subgroup.map_sup, hS, ← MonoidHom.range_eq_map, range_subtype] at hres
    exact le_antisymm (hres.symm.le.trans (sup_le_sup_right hr T)) (sup_le hK₁Y hTY)
  have hK₁K : K₁ ≤ K := by
    let : (K.subgroupOf H).Normal := hKn
    let : Group.IsPerfect (K₁.subgroupOf Y) := hC.perfect
    let : Group.IsPerfect K₁ := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hK₁Y).toMonoidHom) (subgroupOfEquivOfLe hK₁Y).surjective
    let : Group.IsPerfect (K₁.subgroupOf H) := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (hK₁Y.trans hYH)).symm.toMonoidHom)
      (subgroupOfEquivOfLe (hK₁Y.trans hYH)).symm.surjective
    have hsup : K.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
      apply map_injective H.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKH,
        map_subgroupOf_eq_of_le (hTY.trans hYH), ← hgen,
        ← MonoidHom.range_eq_map, range_subtype]
    have hp := isPGroup_quotient_of_sup_eq_top (K.subgroupOf H) (T.subgroupOf H)
      (isSylowIn_iff.mp hSyl).1.comap_subtype hsup
    let : Group.IsNilpotent (H ⧸ K.subgroupOf H) := hp.isNilpotent
    have h := le_of_isPerfect_of_solvable_quotient (K₁.subgroupOf H) (K.subgroupOf H)
    have hm := map_mono (f := H.subtype) h
    simpa only [map_subgroupOf_eq_of_le (hK₁Y.trans hYH),
      map_subgroupOf_eq_of_le hKH] using hm
  have hnot : ¬ Y ≤ M := by
    let S := Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)
    let : IsSimpleGroup S := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
    let : Group.IsPerfect (BinaryLinear.OuterCyclic.LinearGroup 3) :=
      BinaryLinear.linearGroup_isPerfect 3 (by decide)
    let : Group.IsPerfect S := Group.IsPerfect.ofSurjective
      (f := BinaryLinear.SmallParabolicLevi.linearThreeEquivProjective.toMonoidHom)
      BinaryLinear.SmallParabolicLevi.linearThreeEquivProjective.surjective
    let f := eY.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Y))
    have hf : Function.Surjective f := eY.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : IsPGroup 2 f.ker := by
      rw [MonoidHom.ker_comp_of_injective _ _ eY.injective, QuotientGroup.ker_mk']
      exact pCore_isPGroup
    intro hYM
    exact not_le_cubic_theta_of_simple_two_section L₁ (H ⊓ M) Y htheta hLY hcard f hf hk
      (le_inf hYH hYM)
  have hHz : Y ∈ Source.Hz L₁ T G₁ M := by
    refine ⟨⟨?_, hbase⟩, hYH.trans hH.2.1, hnot⟩
    change Y.pCoreIn 2 ≠ ⊥
    have hncore : H ≤ normalizer (Source.QH H : Set G) := by
      apply (normal_subgroupOf_iff_le_normalizer (pCoreIn_le 2 H)).mp
      have he : (Source.QH H).subgroupOf H = pCore 2 H :=
        comap_map_eq_self_of_injective H.subtype_injective _
      change ((Source.QH H).subgroupOf H).Normal
      rw [he]
      infer_instance
    have hc := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) hcore (hYH.trans hncore)
    intro he
    exact hH.1.1 (le_bot_iff.mp (hc.trans he.le))
  exact ⟨K₁, hK₁Y, hK₁K, hLK₁, hn, hjoin, hC, hHz, eK, heK⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource

end
