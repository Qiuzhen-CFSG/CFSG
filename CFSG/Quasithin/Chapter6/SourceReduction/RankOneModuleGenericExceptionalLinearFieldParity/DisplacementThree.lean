module
public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.SevenProduct
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.DisplacementConstituents
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.DisplacementDegree

/-!
# The literal degree-three displacement bound

The genuine seed supplies the faithful action on U/Z₁. The odd quotient
product and natural Cartan action give the hypotheses of the PSL₃(4)
order-seven calculation. An element whose square is in O₂(H) becomes an
involution in the quotient, so the proof never requires an involution lift.
The fixed-codimension comparison returns the bound to the original subgroup
index, and the odd-product reduction covers all actors in H D_L.

Source: Aschbacher–Smith 5.1.17, printed p.641 (refs/quasithin.pdf).
The seed remains explicit; its global TI/F.8 construction and 5.1.16(2)
remain with final assembly owner qt-d-1222-linear-field-parity.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups MonoidAlgebra IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
/-- The degree-three displacement calculation on the literal quotient U/Z₁,
including actors whose representatives need not be involutions. -/
theorem degree_three_largeDisplacement
    (h : Input KnownSimple.IsKnownSimple T L W 3)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (s : Seed T L H A 3) : LargeDisplacement (setup T L s.V H A) := by
  apply (largeDisplacement_iff_on_outside_of_odd h hH c (by decide) hK hnf hm s.V).mpr
  intro y hy hy2 hyQ
  let E := setup T L s.V H A
  let := point_normal_in_span s.f8
  let := ChapterF.Section08.Setup.lemma_F_8_5_two s.f8
  let : IsElementaryAbelian 2 (E.U ⧸ E.V₁.subgroupOf E.U) :=
    IsElementaryAbelian.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  obtain ⟨ρ,d,hρ,_⟩ := exists_faithful_action s.f8
  obtain ⟨e,he⟩ := odd_join_quotient_product h hH c (by decide) hK hnf hm
  obtain ⟨F,_,_,hF,⟨f⟩⟩ := residual_coreQuotient_fitting_model hH.1.1.2 hm
  let : Fintype F := Fintype.ofFinite F
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let a : Matrix.PSL3Four.F ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF,Matrix.PSL3Four.card_F])
  let f' := (Atlas.fieldEquivPSL 3 a).trans f.symm
  have hcard : Nat.card A = 7 := by
    simpa using (c.left_cyclic_and_card h.sylow_normalizes h.linear).2
  have hfree (a : A) (ha : a ≠ 1) (v)
      (hv : (ρ.comp e.toMonoidHom) (1,a) v = v) : v = 0 := by
    apply s.cartan_fixedFree c ρ d a ha v
    have he' : e (1,a) = QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))
        ⟨a,mem_sup_right a.property⟩ := by simpa using he 1 a
    change ρ (e (1,a)) v = v at hv
    rwa [he'] at hv
  let t := QuotientGroup.mk' (pCore 2 H) (⟨y,hy⟩ : H)
  have ht2 : t ^ 2 = 1 := by
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨z,hz,he⟩ := hy2
    exact (Subtype.ext he : z = (⟨y,hy⟩ : H)^2) ▸ hz
  have ht0 : t ≠ 1 := by
    intro hh
    exact hyQ (mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff _).mp hh))
  have hb := ChapterH.Section01To04.L3Four.seven_product_displacement f'
    (ρ.comp e.toMonoidHom) (hρ.comp e.injective) hcard hfree t
    (orderOf_eq_prime ht2 ht0)
  rw [displacement_eq_residualFactor_fixedCodim s.f8 e he ρ d hy,residualFactorAction_eq]
  unfold fixedCodim at hb ⊢
  rw [fixedSpace_comp_map,MonoidHom.map_zpowers] at hb ⊢
  exact hb
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
