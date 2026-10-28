module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FieldAction
public import Theory.SpecificGroups.PSL2.EightExtraspecialAction
public import Theory.GroupTheory.PrimeOrderLift
public import Theory.GroupTheory.PRegularLift
/-!
# The exact partner action kernel and cubic supplement

Transport the original first core to the partner core, retaining the ambient
conjugation square. The eight-dimensional extraspecial action has trivial
centralizer, so the rank-one action kernel equals O₂(Mc). The genuine field
projection consequently has kernel H. In the proper case its pure cubic
field automorphism lifts with order three, by removing the two-part of a
preimage. That element supplements H in Mc.

Source: Aschbacher--Smith 14.2.18, p.987. The marked amalgam is an explicit
earlier input. `CubicExtension` places the supplement in the original overlap;
ambient recognition and terminal exclusion remain with this source owner.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)


/-- The two intrinsic cores, identified through their common ambient image. -/
def sourceFirstPartnerCoreEquiv (r : MarkedTriality T M Mc H) : pCore 2 H ≃* pCore 2 Mc :=
  ((pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (sourcePartnerCoreEquiv hG hempty hM hu hmany hcard e hH r).symm

theorem sourceFirstPartnerCoreEquiv_val (r : MarkedTriality T M Mc H) (q : pCore 2 H) :
    ((sourceFirstPartnerCoreEquiv hG hempty hM hu hmany hcard e hH r q : Mc) : G) = q := by
  exact congrArg (fun x : H.pCoreIn 2 => (x : G))
    ((sourcePartnerCoreEquiv hG hempty hM hu hmany hcard e hH r).apply_symm_apply
      ((pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective q))

include hG hempty hM hu hmany hcard e hH

theorem source_firstCoreAction_centralizer_eq_bot (r : MarkedTriality T M Mc H) :
    centralizer ((firstCoreAction hG hempty hM hu hmany hcard e hH).range :
      Set (MulAut (PartnerCoreModule Mc))) = ⊥ := by
  let f := sourceFirstPartnerCoreEquiv hG hempty hM hu hmany hcard e hH r
  let a := firstCoreAction hG hempty hM hu hmany hcard e hH
  let c := (QuotientGroup.mk' (center (pCore 2 Mc))).comp f.toMonoidHom
  let : Group.IsPerfect H := first_perfect r
  let : IsExtraspecial 2 (pCore 2 H) := IsExtraspecial.of_mulEquiv f.symm
    (source_partner_core_extraspecial hG hempty hM hu hmany hcard e hH r)
  let := (source_partner_core_module hG hempty hM hu hmany hcard e hH r).1
  have hs : Function.Surjective c := (QuotientGroup.mk'_surjective _).comp f.surjective
  have hk : c.ker = center (pCore 2 H) := by
    ext q
    change QuotientGroup.mk' (center (pCore 2 Mc)) (f q) = 1 ↔ q ∈ center (pCore 2 H)
    constructor
    · intro hq
      have hz := (QuotientGroup.eq_one_iff (f q)).mp hq
      have hh : f.symm (f q) ∈ center (pCore 2 H) := (centerCongr f.symm ⟨f q,hz⟩).property
      rwa [f.symm_apply_apply] at hh
    · intro hq
      exact (QuotientGroup.eq_one_iff (f q)).mpr (centerCongr f ⟨q,hq⟩).property
  have ha (h : H) (q : pCore 2 H) : c (MulAut.conjNormal h q) = a h (c q) := by
    change QuotientGroup.mk' (center (pCore 2 Mc)) (f (MulAut.conjNormal h q)) =
      quotientAut (center (pCore 2 Mc)) (MulAut.conjNormal
        (inclusion (source_first_le_partner hG hempty hM hu hmany hcard e hH) h))
        (QuotientGroup.mk' (center (pCore 2 Mc)) (f q))
    rw [quotientAut_apply_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    rw [sourceFirstPartnerCoreEquiv_val]
    simp only [MulAut.conjNormal_apply, coe_mul, coe_inv]
    rw [sourceFirstPartnerCoreEquiv_val]
    rfl
  exact Theory.SpecificGroups.PSL2Eight.extraspecial_action_centralizer_eq_bot
    (firstQuotientEquiv r) c hs hk a ha
    (source_partner_core_module hG hempty hM hu hmany hcard e hH r).2

theorem source_rankOneAction_kernel_eq (r : MarkedTriality T M Mc H) :
    (sourceRankOneAction hG hempty hM hu hmany hcard e hH r).ker = pCore 2 Mc :=
  source_rankOneAction_kernel_eq_of_core_centralizer hG hempty hM hu hmany hcard e hH r
    (source_firstCoreAction_centralizer_eq_bot hG hempty hM hu hmany hcard e hH r)

theorem source_partner_quotient (r : MarkedTriality T M Mc H) :
    Nonempty ((Mc ⧸ pCore 2 Mc) ≃* Theory.PSL2.BinaryGroup 3) ∨
      Nonempty ((Mc ⧸ pCore 2 Mc) ≃* MulAut (Theory.PSL2.BinaryGroup 3)) :=
  source_partner_quotient_of_core_centralizer hG hempty hM hu hmany hcard e hH r
    (source_firstCoreAction_centralizer_eq_bot hG hempty hM hu hmany hcard e hH r)

/-- There is no extra odd kernel in the original field action. -/
theorem source_fieldAction_kernel_eq_first (r : MarkedTriality T M Mc H) :
    (sourceFieldAction hG hempty hM hu hmany hcard e hH r).ker = H.subgroupOf Mc := by
  rw [source_fieldAction_kernel,source_rankOneAction_kernel_eq]
  apply sup_eq_left.mpr
  intro q hq
  apply pCoreIn_le 2 H
  rw [←source_partner_core_eq hG hempty hM hu hmany hcard e hH r]
  exact ⟨q,hq,rfl⟩

/-- A proper partner has the full coefficient-field image. -/
theorem source_fieldAction_range_eq_top (r : MarkedTriality T M Mc H) (hne : Mc ≠ H) :
    (sourceFieldAction hG hempty hM hu hmany hcard e hH r).range = ⊤ := by
  rcases source_fieldAction_range hG hempty hM hu hmany hcard e hH r with hz | ht
  · exfalso
    apply hne
    apply le_antisymm ?_ (source_first_le_partner hG hempty hM hu hmany hcard e hH)
    intro x hx
    have hk : (⟨x,hx⟩ : Mc) ∈ (sourceFieldAction hG hempty hM hu hmany hcard e hH r).ker := by
      have hh : sourceFieldAction hG hempty hM hu hmany hcard e hH r ⟨x,hx⟩ ∈
          (sourceFieldAction hG hempty hM hu hmany hcard e hH r).range := ⟨_,rfl⟩
      rw [hz, mem_bot] at hh
      exact hh
    rw [source_fieldAction_kernel_eq_first] at hk
    exact hk
  · exact ht

/-- The pure cubic coefficient automorphism has an actual order-three lift
in the original partner. This keeps the marked quotient coordinates. -/
theorem source_cubic_field_lift (r : MarkedTriality T M Mc H) (hne : Mc ≠ H) :
    ∃ (σ : Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) (x : Mc),
      orderOf σ = 3 ∧ orderOf x = 3 ∧
      sourceRankOneAction hG hempty hM hu hmany hcard e hH r x = Theory.PSL2.fieldAut σ := by
  let a := sourceRankOneAction hG hempty hM hu hmany hcard e hH r
  have hn : (sourceFieldAction hG hempty hM hu hmany hcard e hH r).range ≠ ⊥ := by
    rw [source_fieldAction_range_eq_top hG hempty hM hu hmany hcard e hH r hne]
    have hc : Nat.card (Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) = 3 :=
      GaloisField.card_ringAut 2 3 (by decide)
    let : Finite (Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) :=
      Nat.finite_of_card_ne_zero (by omega)
    have : Nontrivial (Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact top_ne_bot
  obtain ⟨σ,x,hσ,hx,ho⟩ :=
    source_rankOneAction_field_witness hG hempty hM hu hmany hcard e hH r hn
  let v : a.range := ⟨a x,⟨x,rfl⟩⟩
  have hv : orderOf v = 3 := (Subgroup.orderOf_coe v).symm.trans ho
  obtain ⟨y,hy,hey⟩ := a.rangeRestrict.exists_pRegular_lift a.rangeRestrict_surjective
    2 Nat.prime_two v (by rw [hv]; decide)
  have hay : a y = Theory.PSL2.fieldAut σ := (congrArg Subtype.val hey).trans hx
  have hker : IsPGroup 2 a.ker := by
    rw [source_rankOneAction_kernel_eq hG hempty hM hu hmany hcard e hH r]
    exact pCore_isPGroup
  have horder : orderOf y = 3 := by
    rw [←a.orderOf_map_eq_of_coprime_of_isPGroup_ker hker y
      (Nat.prime_two.coprime_iff_not_dvd.mpr hy), hay, Theory.PSL2.orderOf_fieldAut,hσ]
  exact ⟨σ,y,hσ,horder,hay⟩

/-- The same literal cubic lift supplements the first endpoint. Placement in
the original Sylow normalizer is the next source step, not assumed here. -/
theorem source_cubic_supplement (r : MarkedTriality T M Mc H) (hne : Mc ≠ H) :
    ∃ (σ : Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) (x : Mc),
      orderOf σ = 3 ∧ orderOf x = 3 ∧
      sourceRankOneAction hG hempty hM hu hmany hcard e hH r x = Theory.PSL2.fieldAut σ ∧
      Mc = H ⊔ zpowers (x : G) ∧ Nat.card (zpowers (x : G)) = 3 := by
  obtain ⟨σ,x,hσ,hx,hact⟩ := source_cubic_field_lift hG hempty hM hu hmany hcard e hH r hne
  let b := sourceFieldAction hG hempty hM hu hmany hcard e hH r
  have hbx : b x = σ := by
    change Theory.PSL2.fieldProjection _ (sourceRankOneAction hG hempty hM hu hmany hcard e hH r x) = σ
    rw [hact,Theory.PSL2.fieldProjection_fieldAut]
  have hmap : (zpowers x).map b = ⊤ := by
    rw [MonoidHom.map_zpowers, hbx]
    apply zpowers_eq_top_of_prime_card (GaloisField.card_ringAut 2 3 (by decide))
    intro he
    rw [he,orderOf_one] at hσ
    contradiction
  have hsup : zpowers x ⊔ H.subgroupOf Mc = ⊤ := by
    rw [←source_fieldAction_kernel_eq_first hG hempty hM hu hmany hcard e hH r,
      ←comap_map_eq, hmap, comap_top]
  have hamb := congrArg (Subgroup.map Mc.subtype) hsup
  rw [Subgroup.map_sup,MonoidHom.map_zpowers,map_subgroupOf_eq_of_le
    (source_first_le_partner hG hempty hM hu hmany hcard e hH),
    ←MonoidHom.range_eq_map,range_subtype,sup_comm] at hamb
  refine ⟨σ,x,hσ,hx,hact,hamb.symm,?_⟩
  rw [Nat.card_zpowers,Subgroup.orderOf_coe,hx]
end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
