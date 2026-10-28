module

public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicGeneration
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.GeneralizedFitting.PrimeCoreNormalized

/-!
# The second parabolic of 14.6.6(6)

For Tᵤ ≤ S ≤ T₀ and H₂ inside the centralizer of u modulo the central
point, its two-residual centralizes u. The two possible choices of S
therefore give a Sylow subgroup of I₂ = O²(H₂)S. The equality
T₀ = O₂(H)Tᵤ makes I₂ supplement O₂(H) in H₂. This supplies the literal
S₃ quotient. Moreover O₂(H) normalizes I₂, so characteristic two of H
passes to I₂. Neither the generated group nor its core is involved.

Source: Aschbacher–Smith, 14.6.6(6), printed pp.1023–1024.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]

private theorem characteristic_of_ambient_core_normalizes
    (H P : Subgroup G) (hPH : P ≤ H)
    (hchar : generalizedFitting H = pCore 2 H)
    (hn : H.pCoreIn 2 ≤ normalizer (P : Set G)) :
    generalizedFitting P = pCore 2 P := by
  have hn' : pCore 2 H ≤ normalizer (P.subgroupOf H : Set H) := by
    rw [←subgroupOf_normalizer_eq hPH]
    exact fun x hx => hn (mem_map_of_mem H.subtype hx)
  have hc := generalizedFitting_eq_pCore_of_normalized_by_pCore
    (P.subgroupOf H) hchar hn'
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hPH)).mp
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hc))

/-- The second-parabolic calculation from the original F.9 setup and U1.
It supplies all local data before any assertion about the generated group. -/
theorem suitable_second_parabolic_data
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (u : G) (hu : u ∈ D.UH) (H2 S : Subgroup G)
    (hTuS : suitableCentralizer (D := D) u ≤ S)
    (hS0 : S ≤ suitableQuotientCentralizer h u)
    (hi : (suitableCentralizer (D := D) u).relIndex
      (suitableQuotientCentralizer h u) = 2)
    (hjoin : suitableQuotientCentralizer h u = D.QH ⊔ suitableCentralizer (D := D) u)
    (h0Syl : Chapter1.IsSylowIn 2 (suitableQuotientCentralizer h u) H2)
    (hH2 : H2 ≤ h.kernel (zpowers u))
    (hq : Nonempty ((H2 ⧸ pCore 2 H2) ≃* Equiv.Perm (Fin 3)))
    (huSyl : Chapter1.IsSylowIn 2 (suitableCentralizer (D := D) u)
      (D.H ⊓ centralizer ({u} : Set G))) :
    let I2 := (pResidual 2 H2).map H2.subtype ⊔ S
    Chapter1.IsSylowIn 2 S I2 ∧
      Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)) ∧
      generalizedFitting I2 = pCore 2 I2 := by
  let Tu := suitableCentralizer (D := D) u
  let T0 := suitableQuotientCentralizer h u
  let R := (pResidual 2 H2).map H2.subtype
  let P := R ⊔ S
  change T0 = D.QH ⊔ Tu at hjoin
  have h0H2 := (Chapter1.isSylowIn_iff.mp h0Syl).2.1
  have huH : zpowers u ≤ D.H := zpowers_le.mpr (h.UH_le_H hu)
  have hH2H : H2 ≤ D.H := fun x hx => ((h.mem_kernel_iff huH).mp (hH2 hx)).1
  have hPH2 : P ≤ H2 := sup_le (map_subtype_le _) (hS0.trans h0H2)
  have hQ0 : D.QH ≤ T0 := by rw [hjoin]; exact le_sup_left
  have hTu0 : Tu ≤ T0 := by rw [hjoin]; exact le_sup_right
  have hcase : S = Tu ∨ S = T0 := by
    have hp : (Tu.relIndex S * S.relIndex T0).Prime := by
      rw [relIndex_mul_relIndex Tu S T0 hTuS hS0,hi]
      exact Nat.prime_two
    rcases Nat.prime_mul_iff.mp hp with ⟨_,he⟩ | ⟨_,he⟩
    · exact Or.inr (le_antisymm hS0 (relIndex_eq_one.mp he))
    · exact Or.inl (le_antisymm (relIndex_eq_one.mp he) hTuS)
  have h0NS : T0 ≤ normalizer (S : Set G) := by
    rcases hcase with rfl | rfl
    · exact (normal_subgroupOf_iff_le_normalizer hTu0).mp (normal_of_index_eq_two hi)
    · exact T0.le_normalizer
  have hRC : R ≤ centralizer ({u} : Set G) := by
    have hc := residual_centralizes_of_two_layer H2 (zpowers u) D.V₁
      (IsPGroup.of_card (p := 2) (n := 1) (by simpa using h.point_card))
      (hH2H.trans h.H_centralizes) (by
        rw [commutator_comm]
        exact commutator_le.mpr (fun x hx y hy =>
          ((h.mem_kernel_iff huH).mp (hH2 hy)).2 x hx))
    exact hc.trans (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers u)))
  have hSyl : Chapter1.IsSylowIn 2 S P := by
    rcases hcase with he | he
    · have hSC : S ≤ centralizer ({u} : Set G) := he.le.trans inf_le_right
      rw [he]
      exact huSyl.restrict (hTuS.trans le_sup_right)
        (sup_le (le_inf ((map_subtype_le _).trans hH2H) hRC)
          (le_inf (hS0.trans (h0H2.trans hH2H)) hSC))
    · rw [he]
      exact h0Syl.restrict (he.ge.trans le_sup_right) hPH2
  have hcover : R ⊔ T0 = H2 := by
    obtain ⟨A,hA⟩ := h0Syl
    have hh := congrArg (Subgroup.map H2.subtype) (pResidual_sup_sylow_eq_top A)
    simpa only [Subgroup.map_sup,hA,←MonoidHom.range_eq_map,range_subtype] using hh
  have hPQ : P ⊔ D.QH = H2 := by
    apply le_antisymm (sup_le hPH2 (hQ0.trans h0H2))
    rw [←hcover,hjoin]
    exact sup_le (le_sup_left.trans le_sup_left)
      (sup_le le_sup_right (hTuS.trans (le_sup_right.trans le_sup_left)))
  have hQH2 : D.QH ≤ H2.pCoreIn 2 := by
    exact (le_inf (hQ0.trans h0H2) le_rfl).trans (inf_pCoreIn_le_of_le 2 hH2H)
  obtain ⟨e⟩ := hq
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H2))
  have hk : f.ker = pCore 2 H2 := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have himage : (P.subgroupOf H2).map f = ⊤ := by
    have hs : P.subgroupOf H2 ⊔ D.QH.subgroupOf H2 = ⊤ := by
      rw [←subgroupOf_sup hPH2 (hQ0.trans h0H2),hPQ,subgroupOf_self]
    have hzero : (D.QH.subgroupOf H2).map f = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [hk]
      intro x hx
      obtain ⟨a,ha,he⟩ := hQH2 hx
      exact (Subtype.ext he : a = x) ▸ ha
    have hh := congrArg (Subgroup.map f) hs
    rw [Subgroup.map_sup,hzero,sup_bot_eq,←MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (e.surjective.comp (QuotientGroup.mk'_surjective _))] at hh
    exact hh
  obtain ⟨_,⟨eP⟩⟩ := product_twoCore_of_permThree f (P.subgroupOf H2) himage
    (by rw [hk]; exact pCore_isPGroup.to_le inf_le_right)
  let ep := (subgroupOfEquivOfLe hPH2).symm
  let epq := ep.toMonoidHom.pCoreQuotientEquiv (p := 2) ep.surjective
    (IsPGroup.ker_isPGroup_of_injective ep.injective)
  refine ⟨hSyl,⟨epq.trans eP⟩,?_⟩
  apply characteristic_of_ambient_core_normalizes D.H P (hPH2.trans hH2H) h.characteristic_H
  have hNR : H2 ≤ normalizer (R : Set G) := H2.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H2 (pResidual 2 H2))
  exact (le_inf ((hQ0.trans h0H2).trans hNR) (hQ0.trans h0NS)).trans
    (normalizer_inf_normalizer_le_normalizer_sup R S)

end CFSG.Quasithin.Chapter14.Section06
