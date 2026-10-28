module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveDecomposition.Displacement
public import CFSG.Quasithin.ChapterJ.Section04To05.Setup.Flag
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# The actual plane commutator in J.4.1(6)

For the selected conjugate, Dα = Uα ∩ Q has an image of order two in H/U.
The plane V₂ = ZZα makes C_Q(V₂) normalize Uα, so its commutator with Uα
lies in Dα. Evaluation at the generator of Zα gives C_Q(V₂) index at most
two in Q. If its Uα commutator vanished modulo U, the selected v would
fix a hyperplane in the native Q/HC module. The absence of binary
transvections and faithfulness would force v into Q, a contradiction.
Thus the commutator has the whole order-two image of Dα. The preceding
five-displacement theorem places this line in Q₅/U for the same chosen B₅.

Every subgroup, quotient, conjugator and actor is the original source one.
No rank or displacement equality is assumed.

Source: Aschbacher–Smith J.4.1(6), printed p.440 (PDF p.451).
-/

public section
noncomputable section

open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} {p : Plane d}

abbrev Plane.CQ₂ (p : Plane d) : Subgroup G :=
  d.toTypeRuSetup.Q ⊓ centralizer (p.group : Set G)

abbrev SourceChoice.Dα (s : SourceChoice p) : Subgroup G := s.Uα ⊓ d.toTypeRuSetup.Q

theorem SourceChoice.hat_Dα_card (s : SourceChoice p) : Nat.card (hat d s.Dα) = 2 := by
  have hD : Nat.card s.Dα = 16 := by
    have hh := ConjugateIntersections.card_star_mul_card_inf_Q d s.Uα
      (s.Uα_le_K.trans d.toTypeRuSetup.K_le_H)
    have hs : Nat.card ((s.Uα.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap) = 2 :=
      s.conjugate_properties.2.1
    have hu : Nat.card s.Uα = 32 := ConjugateIntersections.card_conjugateU d s.g
    rw [hs,hu] at hh
    change 2 * Nat.card s.Dα = 32 at hh
    omega
  have hi : s.Dα ⊓ d.toTypeRuSetup.U = d.V := by
    apply le_antisymm
    · intro x hx
      exact s.conjugate_properties.2.2 ▸ ⟨hx.1.1,d.U_le_HC hx.2⟩
    · intro x hx
      have hu := (le_conjugateSpan d.toTypeRuSetup.H d.V) hx
      exact ⟨⟨(ConjugateIntersections.V_le_conjugateU d s.g (p.L₂_le_L s.in_residual)) hx,
        d.ru2.six.kernel_le hu⟩,hu⟩
  have hc := hat_card d s.Dα (inf_le_right.trans (pCoreIn_le 2 _))
  rw [hi,d.ru1.card_V,hD] at hc
  omega

theorem SourceChoice.commutator_CQ₂_le_Dα (s : SourceChoice p) :
    ⁅p.CQ₂,s.Uα⁆ ≤ s.Dα := by
  refine le_inf ?_ ?_
  · apply le_normalizer_iff_commutator_le_right.mp
    exact (inf_le_right.trans (centralizer_le s.conjugate_point_le)).trans
      (ConjugateIntersections.conjugateU_normalized d s.g)
  · rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp
        (s.Uα_le_K.trans (d.toTypeRuSetup.K_le_H.trans d.ru2.six.normalized)))

private def pointEvaluation (z : d.toTypeRuSetup.U) :
    d.toTypeRuSetup.Q →* d.toTypeRuSetup.Z where
  toFun q := ⟨⁅(q:G),(z:G)⁆,d.toTypeRuSetup.commutator_Q_U_le_Z
    (commutator_mem_commutator q.property z.property)⟩
  map_one' := Subtype.ext (commutatorElement_one_left _)
  map_mul' a b := by
    apply Subtype.ext
    change ⁅(a:G)*(b:G),(z:G)⁆ = ⁅(a:G),(z:G)⁆ * ⁅(b:G),(z:G)⁆
    have ha := d.toTypeRuSetup.commutator_Q_U_le_Z
      (commutator_mem_commutator a.property z.property)
    have hb := d.toTypeRuSetup.commutator_Q_U_le_Z
      (commutator_mem_commutator b.property z.property)
    have hc := (pCoreIn_le 2 d.toTypeRuSetup.H a.property) _ hb
    rw [commutatorElement_mul_left_eq_conj_mul,← hc,mul_inv_cancel_right]
    exact (d.ru2.natural.section_le (d.ru2.natural.kernel_le ha)) _ hb

/-- The plane centralizer has index at most two in Q. -/
theorem SourceChoice.card_CQ₂_lower (s : SourceChoice p) : 1024 ≤ Nat.card p.CQ₂ := by
  let Zα := d.toTypeRuSetup.Z.conjBy s.g
  have hzcard : Nat.card Zα = 2 := by
    change Nat.card (d.toTypeRuSetup.Z.map (MulAut.conj s.g).toMonoidHom) = 2
    rw [card_map_of_injective (MulAut.conj s.g).injective,d.card_Z]
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G:=Zα) 2 (by rw [hzcard])
  have hzg : Zα = zpowers (z:G) := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr z.property) ?_).symm
    rw [Nat.card_zpowers,Subgroup.orderOf_coe,hz,hzcard]
  have hzU : (z:G) ∈ d.toTypeRuSetup.U :=
    (ConjugateIntersections.conjugateZ_le_V d s.g (p.L₂_le_L s.in_residual)).trans
      (le_conjugateSpan d.toTypeRuSetup.H d.V) z.property
  let ev := pointEvaluation (d:=d) ⟨z,hzU⟩
  have hk : ev.ker ≤ p.CQ₂.subgroupOf d.toTypeRuSetup.Q := by
    intro q hq
    refine ⟨q.property,?_⟩
    have he : ⁅(q:G),(z:G)⁆ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hq)
    have hC : p.group ≤ centralizer ({(q:G)}:Set G) := by
      rw [s.plane_eq_join_points]
      change d.toTypeRuSetup.Z ⊔ Zα ≤ _
      rw [hzg]
      refine sup_le ?_ (zpowers_le.mpr ?_)
      · intro a ha
        exact mem_centralizer_singleton_iff.mpr (pCoreIn_le 2 d.toTypeRuSetup.H q.property a ha)
      · exact mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp he).symm
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hC ha)
  have hr : Nat.card ev.range ≤ 2 :=
    (Nat.card_le_card_of_injective _ ev.range.subtype_injective).trans_eq d.card_Z
  have hc := ev.ker.index_mul_card
  rw [index_ker,d.ru2.card_Q d.card_Z] at hc
  have hh := Nat.mul_le_mul_right (Nat.card ev.ker) hr
  rw [hc] at hh
  have hb : 1024 ≤ Nat.card ev.ker := by omega
  have hkcard := card_le_of_le hk
  rw [Nat.card_congr (subgroupOfEquivOfLe (show p.CQ₂ ≤ d.toTypeRuSetup.Q from inf_le_left)).toEquiv] at hkcard
  exact hb.trans hkcard

private theorem zero_of_small_displacement
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (f : Module.End (ZMod 2) W)
    (hc : Nat.card (LinearMap.range f) ≤ 2)
    (hn : Module.finrank (ZMod 2) (LinearMap.range f) ≠ 1) : f = 0 := by
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range f)
  rw [Nat.card_zmod] at hpow
  have hdim : Module.finrank (ZMod 2) (LinearMap.range f) ≤ 1 := by
    by_contra h
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega :
      2 ≤ Module.finrank (ZMod 2) (LinearMap.range f))
    rw [← hpow] at hh
    omega
  exact LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp (by omega))

/-- The selected conjugate acts nontrivially on the plane centralizer modulo U. -/
theorem SourceChoice.commutator_CQ₂_not_le_U (s : SourceChoice p) :
    ¬ ⁅p.CQ₂,s.Uα⁆ ≤ d.toTypeRuSetup.U := by
  intro hzero
  let vH : d.toTypeRuSetup.H := ⟨s.v,d.toTypeRuSetup.K_le_H s.v_mem_K⟩
  let head := d.fusionNaturalHead
  let f : Module.End (ZMod 2) FourSpace :=
    head.action.action (d.ru2.quotientMap vH) - LinearMap.id
  let δ : d.toTypeRuSetup.Q →* Multiplicative FourSpace :=
    (AddMonoidHom.toMultiplicative f.toAddMonoidHom).comp head.sectionData.coordinates
  have hfix := head.sectionData.fixed_on_imageSpace_of_commutator_le s.Uα p.CQ₂
    (by rw [commutator_comm]; exact hzero.trans d.U_le_HC) vH s.v_mem
  have hk : p.CQ₂.subgroupOf d.toTypeRuSetup.Q ≤ δ.ker := by
    intro q hq
    have he := hfix (head.sectionData.coordinates q).toAdd
      ((head.sectionData.mem_imageSpace_iff p.CQ₂ _).mpr ⟨q,hq,rfl⟩)
    change f (head.sectionData.coordinates q).toAdd = 0
    exact sub_eq_zero.mpr he
  have hkcard : 1024 ≤ Nat.card δ.ker := by
    have hh := card_le_of_le hk
    rw [Nat.card_congr (subgroupOfEquivOfLe (show p.CQ₂ ≤ d.toTypeRuSetup.Q from inf_le_left)).toEquiv] at hh
    exact s.card_CQ₂_lower.trans hh
  have hr : Nat.card δ.range ≤ 2 := by
    have hh := δ.ker.index_mul_card
    rw [index_ker,d.ru2.card_Q d.card_Z] at hh
    have hb := Nat.mul_le_mul_left (Nat.card δ.range) hkcard
    rw [hh] at hb
    omega
  have hfc : Nat.card (LinearMap.range f) = Nat.card δ.range := by
    let e : δ.range ≃ LinearMap.range f := {
      toFun x := ⟨x.val.toAdd,by
        obtain ⟨q,hq⟩ := x.property
        exact ⟨(head.sectionData.coordinates q).toAdd,congrArg Multiplicative.toAdd hq⟩⟩
      invFun x := ⟨Multiplicative.ofAdd x.val,by
        obtain ⟨v,hv⟩ := x.property
        obtain ⟨q,hq⟩ := head.sectionData.onto (Multiplicative.ofAdd v)
        exact ⟨q,by change Multiplicative.ofAdd (f _) = _; rw [hq]; exact congrArg Multiplicative.ofAdd hv⟩⟩
      left_inv _ := by apply Subtype.ext; rfl
      right_inv _ := by apply Subtype.ext; rfl }
    exact (Nat.card_congr e).symm
  have hf : f=0 := zero_of_small_displacement f (hfc.symm ▸ hr)
    (head.action.no_rank_one (d.ru2.quotientMap vH))
  have ha : head.action.action (d.ru2.quotientMap vH) = 1 := sub_eq_zero.mp hf
  have hv : d.ru2.quotientMap vH = 1 := head.action.injective
    (by simpa only [map_one] using ha)
  have hh : vH ∈ d.ru2.quotientMap.ker := hv
  rw [d.ru2.quotient_kernel] at hh
  exact s.v_not_Q hh

/-- The exact commutator line of J.4.1(6), before choosing a five-subgroup. -/
theorem SourceChoice.hat_plane_commutator (s : SourceChoice p) :
    ⁅hat d p.CQ₂,hat d s.Uα⁆ = hat d s.Dα := by
  rw [← hat_commutator d (inf_le_left.trans (pCoreIn_le 2 _))
    (s.Uα_le_K.trans d.toTypeRuSetup.K_le_H)]
  have hle := hat_mono d s.commutator_CQ₂_le_Dα
  apply eq_of_le_of_card_ge hle
  have hn : hat d ⁅p.CQ₂,s.Uα⁆ ≠ ⊥ := by
    intro he
    apply s.commutator_CQ₂_not_le_U
    intro x hx
    have hxH := (s.commutator_CQ₂_le_Dα.trans (inf_le_right.trans (pCoreIn_le 2 _))) hx
    have hm : hatMap d ⟨x,hxH⟩ ∈ hat d ⁅p.CQ₂,s.Uα⁆ := mem_map.mpr ⟨⟨x,hxH⟩,hx,rfl⟩
    rw [he,mem_bot] at hm
    exact (hatMap_eq_one d _).mp hm
  let : Nontrivial (hat d ⁅p.CQ₂,s.Uα⁆) := (nontrivial_iff_ne_bot _).mpr hn
  have hh := Finite.one_lt_card (α := hat d ⁅p.CQ₂,s.Uα⁆)
  rw [s.hat_Dα_card]
  omega

/-- J.4.1(6), with the literal selected five-subgroup. -/
theorem SourceChoice.hat_Dα_le_Q₅ (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    hat d s.Dα ≤ hat d (Q₅ d B5) := by
  rw [← s.hat_plane_commutator]
  exact (commutator_mono (hat_mono d inf_le_left) le_rfl).trans
    (s.hat_commutator_le_Q₅ B5 hi)

/-- The same source choice supplies the five-subgroup and both displacement conclusions. -/
theorem SourceChoice.source_six_seven (s : SourceChoice p) :
    ∃ B5 : Sylow 5 d.toTypeRuSetup.H,
      (∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) ∧
      hat d s.Dα = ⁅hat d p.CQ₂,hat d s.Uα⁆ ∧
      Nat.card (hat d s.Dα) = 2 ∧ hat d s.Dα ≤ hat d (Q₅ d B5) ∧
      ⁅hat d d.toTypeRuSetup.Q,hat d s.Uα⁆ ≤ hat d (Q₅ d B5) := by
  obtain ⟨B5,hi⟩ := s.inverts_sylow_five
  exact ⟨B5,hi,s.hat_plane_commutator.symm,s.hat_Dα_card,
    s.hat_Dα_le_Q₅ B5 hi,s.hat_commutator_le_Q₅ B5 hi⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
