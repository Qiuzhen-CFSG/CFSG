module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ExchangedActorKernel
public import Theory.SpecificGroups.PSL2.QuinticBorelInner
public import Theory.GroupTheory.NormalizerQuotientOuterPair

/-!
# Inner two-core actions on the actual exchanged PSL₂(16) components

For an element of O₂(H) normalizing a component K, the checked intersection
K ∩ H has order divisible by five and preserves K ∩ T. Normality of O₂(H)
puts its Borel displacements in K ∩ O₂(H) = K ∩ T. The quintic Borel
detector therefore makes the literal action on K/O₂(K) inner.

The final consumer constructs both inner actions from Context and the
proved component-normalizer control, with no new premise. These remove
the field-action obstruction in the exchanged branch. The paired-action kernel comparison in
`ExchangedQuotientExclusion` places O₂(H) in K_z O₂(Mc) and contradicts the
orders of the resulting quotients. The original 14.6.12 factor-join
index remains an allowed earlier-source premise owned by
qt-e-14612-singleton; 14.6.13--14 retain their named producers and final
suitable-choice discharge.
Source: Aschbacher--Smith 14.6.14(4)--15, printed pp.1033--1034.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentExclusion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
    (b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T))

include s b in
theorem source_exchanged_core_action_inner {K : Subgroup G}
    (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.SixteenWreathComponents.L))
    (hKz : K ≤ residualClosure H Mc)
    (x : normalizer (K : Set G)) (hx : (x : G) ∈ H.pCoreIn 2) :
    normalizerPCoreQuotientAction K x ∈ MulAut.innerSubgroup (K ⧸ pCore 2 K) := by
  have hTM : (T : Subgroup G) ≤ Mc := by
    rw [partner_eq_centralizer s]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  let eK := subgroupOfEquivOfLe hKM
  obtain ⟨R,hR⟩ := (T.subtype hTM).exists_subgroupOf_eq_of_subnormal
    (K.subgroupOf Mc) hK.subnormal
  let P : Sylow 2 K := R.mapSurjective (f := eK.toMonoidHom) eK.surjective
  have hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      rw [hR] at hz
      exact hz
    · intro hy
      refine ⟨eK.symm y,?_,eK.apply_symm_apply y⟩
      rw [hR]
      exact hy
  let B := H.subgroupOf K
  have hB : B ≤ normalizer (P : Set K) := by
    have hc := source_exchanged_component_intersection_core s hKM hK em
    have hh : K ⊓ H ≤ normalizer ((K ⊓ (T : Subgroup G) : Subgroup G) : Set G) := by
      rw [←hc]
      exact (K ⊓ H).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (K ⊓ H : Subgroup G)))
    intro y hy
    apply mem_normalizer_iff.mpr
    intro z
    change z ∈ (P : Subgroup K) ↔ y * z * y⁻¹ ∈ (P : Subgroup K)
    rw [hP]
    constructor
    · intro hz
      exact ((mem_normalizer_iff.mp (hh ⟨y.property,hy⟩)) (z : G)).mp ⟨z.property,hz⟩ |>.2
    · intro hz
      exact ((mem_normalizer_iff.mp (hh ⟨y.property,hy⟩)) (z : G)).mpr
        ⟨(y * z * y⁻¹).property,hz⟩ |>.2
  have h5 : 5 ∣ Nat.card B := by
    have hh := source_exchanged_intersection_five_dvd s hKM hK em
    have hm : B.map K.subtype = K ⊓ H := by rw [subgroupOf_map_subtype,inf_comm]
    rwa [←hm,card_map_of_injective K.subtype_injective] at hh
  let α := K.normalizerMonoidHom x
  have hα : (P : Subgroup K).map α.toMonoidHom = P := by
    have hxN : (x : G) ∈ normalizer ((K ⊓ (T : Subgroup G) : Subgroup G) : Set G) :=
      source_exchanged_component_borel_control s hKM hK em
        ⟨pCoreIn_le 2 H hx,x.property⟩
    apply le_antisymm
    · rintro _ ⟨y,hy,rfl⟩
      rw [hP] at hy ⊢
      exact ((mem_normalizer_iff.mp hxN) (y : G)).mp ⟨y.property,hy⟩ |>.2
    · intro y hy
      refine ⟨α.symm y,?_,α.apply_symm_apply y⟩
      rw [hP] at hy ⊢
      exact ((mem_normalizer_iff.mp (inv_mem hxN)) (y : G)).mp ⟨y.property,hy⟩ |>.2
  have hdisp : ∀ y ∈ B, y⁻¹ * α y ∈ (P : Subgroup K) := by
    intro y hy
    have hcoreN : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
      H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
    have hd : (y : G)⁻¹ * (x : G) * (y : G) * (x : G)⁻¹ ∈ H.pCoreIn 2 := by
      have hc := ((mem_normalizer_iff.mp (hcoreN (H.inv_mem hy))) (x : G)).mp hx
      change (y : G)⁻¹ * (x : G) * ((y : G)⁻¹)⁻¹ ∈ H.pCoreIn 2 at hc
      rw [inv_inv] at hc
      exact mul_mem hc (inv_mem hx)
    have hh : ((y⁻¹ * α y : K) : G) ∈ K ⊓ H.pCoreIn 2 :=
      ⟨(y⁻¹ * α y).property,by
        change (y : G)⁻¹ * ((x : G) * (y : G) * (x : G)⁻¹) ∈ H.pCoreIn 2
        simpa only [mul_assoc] using hd⟩
    rw [source_exchanged_component_core_intersection s b hKz] at hh
    rw [hP]
    exact hh.2
  let e := em.some
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let β := MulAut.congr e (normalizerPCoreQuotientAction K x)
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have he : ∀ y, q (α y) = β (q y) := by
    intro y
    change e (QuotientGroup.mk' _ (α y)) =
      e (quotientAut (pCore 2 K) α (e.symm (e (QuotientGroup.mk' _ y))))
    rw [e.symm_apply_apply,quotientAut_apply_mk]
  obtain ⟨z,hz⟩ := Theory.PSL2.inner_of_quintic_cover_displacements
    (F := GaloisField 2 4) (by simpa using GaloisField.card 2 4 (by decide))
    q hq hk P B hB h5 α β he hα hdisp
  refine ⟨e.symm z,?_⟩
  apply (MulAut.congr e).injective
  rw [MulAut.congr_conj,e.apply_symm_apply]
  exact hz

include s in
theorem source_exchanged_core_actions_inner :
    ∃ b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T),
      ∀ x ∈ H.pCoreIn 2,
        (∃ hx : x ∈ normalizer (b.K1 : Set G),
          normalizerPCoreQuotientAction b.K1 ⟨x,hx⟩ ∈
            MulAut.innerSubgroup (b.K1 ⧸ pCore 2 b.K1)) ∧
        (∃ hx : x ∈ normalizer (b.K2 : Set G),
          normalizerPCoreQuotientAction b.K2 ⟨x,hx⟩ ∈
            MulAut.innerSubgroup (b.K2 ⧸ pCore 2 b.K2)) := by
  obtain ⟨b⟩ := source_exchanged_factor_data s
  have hn := source_exchanged_core_normalizes_factors s b
  refine ⟨b,fun x hx => ⟨⟨hn.1 hx,?_⟩,⟨hn.2 hx,?_⟩⟩⟩
  · exact source_exchanged_core_action_inner s b b.first_le b.first_component b.first_model
      ((le_sup_left : b.K1 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq) ⟨x,hn.1 hx⟩ hx
  · exact source_exchanged_core_action_inner s b b.second_le b.second_component b.second_model
      ((le_sup_right : b.K2 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq) ⟨x,hn.2 hx⟩ hx

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
