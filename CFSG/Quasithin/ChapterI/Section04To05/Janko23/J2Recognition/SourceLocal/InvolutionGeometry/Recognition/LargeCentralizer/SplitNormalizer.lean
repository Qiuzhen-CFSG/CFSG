module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SplitNormalizer.Inputs
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SplitNormalizer.CubicFour
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SplitNormalizer.LiftedFive
public import Theory.SpecificGroups.Alternating.FiveSubgroupExtension
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.ElementaryAbelian.PrimePlane
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.SpecificGroups.Alternating.FiveInvolutionFusion
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Splitting and marking the large involution centralizer

A normal A₅ lift containing E X₁ determines all the required centralizer
markings. The frame gives |E X₁| = 12 and U centralizes this Borel. Rigidity
of restriction to an order-twelve subgroup of A₅ then forces U to centralize
the entire lift. Trivial intersection and the quotient order calculation
identify C_G(t) as U × A₅. Sylow conjugacy and the source fusion census give
the involution marking, and `Models` identifies U with the intrinsic two-core.

The lifted A₅ is the derived subgroup and the intrinsic component layer.
Consequently X₃ normalizes it; the same Borel rigidity forces centralization.
Multiplication now gives the A₄ × A₅ normalizer with both literal factor
embeddings, conditional on the independent `CubicFourModel` recognition.

The final assembly constructs the normal A₅ lift by transfer and the marked
A₄ model from the cubic action. Thus `RecognizedQuotient.nonempty_unalignedGeometry`
requires only the local census, the selected other involution, and the frame's
recognized quotient. It assumes no splitting or normalizer recognition, and
does not require simplicity of the ambient group.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1(1), printed p.260.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
variable {G : Type*} [Group G] [Finite G] {D : Seed G} {t : G}

namespace LocalFrame
variable (F : LocalFrame D t)
theorem borel_card : Nat.card (F.E ⊔ F.X1 : Subgroup G) = 12 := by
  have hd : Disjoint F.E F.X1 := disjoint_of_coprime_natCard (by
    rw [F.E_card, F.X1_card]; decide)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint F.E F.X1 F.X1_normalizes hd,
    F.E_card, F.X1_card]

theorem U_centralizes_borel : F.U ≤ centralizer ((F.E ⊔ F.X1 : Subgroup G) : Set G) := by
  let : IsElementaryAbelian 2 (F.E ⊔ F.U : Subgroup G) := F.elementary
  have he : F.U ≤ centralizer (F.E : Set G) := by
    intro u hu e he
    exact congrArg Subtype.val (isMulCommutative_iff.mp
      (inferInstance : IsMulCommutative (F.E ⊔ F.U : Subgroup G))
      (⟨e, mem_sup_left he⟩ : (F.E ⊔ F.U : Subgroup G))
      (⟨u, mem_sup_right hu⟩ : (F.E ⊔ F.U : Subgroup G)))
  have hx : F.U ≤ centralizer (F.X1 : Set G) := F.U_eq ▸ inf_le_right
  exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp he)
    (le_centralizer_iff.mp hx))
end LocalFrame

namespace LiftedFive
variable {F : LocalFrame D t} (K : LiftedFive F)
theorem card : Nat.card K.K = 60 := (Nat.card_congr K.equiv.toEquiv).trans card_A5

theorem centralizer_normalizes : involutionCentralizer t ≤ normalizer (K.K : Set G) := by
  exact (normal_subgroupOf_iff_le_normalizer K.le_centralizer).mp K.normal

theorem centralizes_of_normalizes_borel {g : G}
    (hg : g ∈ normalizer (K.K : Set G))
    (hb : g ∈ centralizer ((F.E ⊔ F.X1 : Subgroup G) : Set G)) :
    g ∈ centralizer (K.K : Set G) := by
  let S := (F.E ⊔ F.X1).subgroupOf K.K
  have hle : F.E ⊔ F.X1 ≤ K.K := sup_le K.E_le K.X1_le
  have hcard : Nat.card S = 12 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans F.borel_card
  let a : MulAut K.K := K.K.normalizerMonoidHom ⟨g, hg⟩
  have ha : a = 1 := AlternatingFiveSubgroupExtension.aut_eq_of_agree
    AlternatingFiveSubgroupExtension.restrictionFaithful K.equiv S hcard a 1 (by
      intro s
      apply Subtype.ext
      change g * (s.val.val) * g⁻¹ = s.val.val
      rw [← hb s.val.val s.property, mul_inv_cancel_right])
  intro k hk
  have h := congrArg (fun f : MulAut K.K => (f ⟨k, hk⟩ : G)) ha
  change g * k * g⁻¹ = k at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem U_centralizes : F.U ≤ centralizer (K.K : Set G) := by
  intro u hu
  exact K.centralizes_of_normalizes_borel
    (K.centralizer_normalizes (F.join_le_centralizer (mem_sup_right hu)))
    (F.U_centralizes_borel hu)

theorem U_disjoint : Disjoint F.U K.K := by
  apply disjoint_def.mpr
  intro x hxU hxK
  have hx : (⟨x, hxK⟩ : K.K) ∈ center K.K := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (K.U_centralizes hxU y y.property)
  have hxe : K.equiv ⟨x, hxK⟩ ∈ center A5 :=
    (centerCongr K.equiv ⟨⟨x, hxK⟩, hx⟩).property
  rw [alternatingGroup.center_eq_bot (by simp)] at hxe
  have he := K.equiv.injective ((mem_bot.mp hxe).trans (map_one K.equiv).symm)
  exact congrArg Subtype.val he

theorem join_eq (ht : OtherInvolution D t) (Q : RecognizedQuotient F) :
    F.U ⊔ K.K = involutionCentralizer t := by
  apply eq_of_le_of_card_ge (sup_le
    (le_sup_right.trans F.join_le_centralizer) K.le_centralizer)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint F.U K.K
    ((le_centralizer_iff.mp K.U_centralizes).trans (Subgroup.centralizer_le_normalizer _))
    K.U_disjoint, F.U_card, K.card, Q.kernel.centralizer_card ht.1 Q.equiv]

include K in
theorem centralizer_centralizes_U (ht : OtherInvolution D t) (Q : RecognizedQuotient F) :
    involutionCentralizer t ≤ centralizer (F.U : Set G) := by
  rw [← K.join_eq ht Q]
  apply sup_le _ (le_centralizer_iff.mp K.U_centralizes)
  intro u hu v hv
  let : IsElementaryAbelian 2 (F.E ⊔ F.U : Subgroup G) := F.elementary
  exact congrArg Subtype.val (isMulCommutative_iff.mp
    (inferInstance : IsMulCommutative (F.E ⊔ F.U : Subgroup G))
    (⟨v, mem_sup_right hv⟩ : (F.E ⊔ F.U : Subgroup G))
    (⟨u, mem_sup_right hu⟩ : (F.E ⊔ F.U : Subgroup G)))

include K in
theorem centralizer_U_eq (ht : OtherInvolution D t) (Q : RecognizedQuotient F) :
    centralizer (F.U : Set G) = involutionCentralizer t :=
  F.centralizer_U_eq (K.centralizer_centralizes_U ht Q)

include K in
theorem normalizer_U_eq (ht : OtherInvolution D t) (Q : RecognizedQuotient F) :
    normalizer (F.U : Set G) = F.X3 ⊔ involutionCentralizer t := by
  apply F.normalizer_U_eq _ (K.centralizer_centralizes_U ht Q)
  intro he
  have := ht.1
  simp [he] at this

theorem involution_fusion (L : LocalCensus D)
    (u : involutionCentralizer t) (hu : orderOf u = 2) :
    IsConj D.z (u : G) ↔ (u : G) ∈ K.K := by
  constructor
  · intro hzu
    obtain ⟨v, huv⟩ := F.A.exists_isConj_of_orderOf_eq_prime_pow
      (n := 1) (by simpa using hu)
    have hvA : ((v : involutionCentralizer t) : G) ∈ F.E ⊔ F.U :=
      F.A_eq ▸ mem_map_of_mem (involutionCentralizer t).subtype v.property
    have hzv := hzu.trans ((involutionCentralizer t).subtype.map_isConj huv)
    obtain ⟨g, hg⟩ := isConj_iff.mp huv
    have hv2 : orderOf ((v : involutionCentralizer t) : G) = 2 := by
      rw [orderOf_coe, ← hg, ← MulAut.conj_apply, (MulAut.conj g).orderOf_eq, hu]
    have hvK := K.E_le ((F.involution_fusion L hvA hv2).mp hzv)
    have hn := K.centralizer_normalizes g.property
    apply (hn (u : G)).mpr
    have hgv := congrArg Subtype.val hg
    change (g : G) * (u : G) * (g : G)⁻¹ = ((v : involutionCentralizer t) : G) at hgv
    exact hgv.symm ▸ hvK
  · intro huK
    let zK : K.K := ⟨D.z, K.E_le F.z_mem⟩
    let uK : K.K := ⟨u, huK⟩
    have hzK : orderOf zK = 2 := by
      rw [← orderOf_coe]; exact D.localType.involution
    have huK2 : orderOf uK = 2 := by
      exact (Subgroup.orderOf_coe uK).symm.trans ((Subgroup.orderOf_coe u).trans hu)
    have h := alternatingGroup.five_involutions_isConj (K.equiv zK) (K.equiv uK)
      ((K.equiv.orderOf_eq _).trans hzK) ((K.equiv.orderOf_eq _).trans huK2)
    exact K.K.subtype.map_isConj (by
      simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
        K.equiv.symm.toMonoidHom.map_isConj h)

/-- Multiplication coordinates preserve both specified factors. -/
theorem exists_coordinates (ht : OtherInvolution D t) (Q : RecognizedQuotient F) :
    ∃ e : involutionCentralizer t ≃* (E4 × A5),
      (∀ c, (e c).1 = 1 ↔ (c : G) ∈ K.K) ∧
      (∀ c, (e c).2 = 1 ↔ (c : G) ∈ F.U) := by
  let : IsElementaryAbelian 2 (F.E ⊔ F.U : Subgroup G) := F.elementary
  let : IsElementaryAbelian 2 F.U := {
    toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq
      (p := 2) F.U_card
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun u =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := F.E ⊔ F.U)
        u (mem_sup_right u.property))) }
  obtain ⟨eU⟩ := IsElementaryAbelian.nonempty_mulEquiv_plane_of_card
    (show Nat.card F.U = 2 ^ 2 from F.U_card)
  obtain ⟨m, hm⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    F.U K.K K.U_disjoint K.U_centralizes
  let n : F.U × K.K ≃* involutionCentralizer t :=
    m.trans (MulEquiv.subgroupCongr (K.join_eq ht Q))
  have hn (u : F.U) (k : K.K) : (n (u, k) : G) = (u : G) * (k : G) := hm u k
  let e := n.symm.trans (eU.prodCongr K.equiv)
  refine ⟨e, ?_, ?_⟩
  · intro c
    obtain ⟨⟨u, k⟩, rfl⟩ := n.surjective c
    have he : (e (n (u, k))).1 = eU u := by
      change eU (n.symm (n (u, k))).1 = eU u
      rw [n.symm_apply_apply]
    rw [he, map_eq_one_iff eU eU.injective, hn]
    constructor
    · intro hu
      simp only [hu, Subgroup.coe_one, one_mul]
      exact k.property
    · intro h
      apply Subtype.ext
      exact disjoint_def.mp K.U_disjoint u.property (by
        simpa only [mul_inv_cancel_right] using K.K.mul_mem h (K.K.inv_mem k.property))
  · intro c
    obtain ⟨⟨u, k⟩, rfl⟩ := n.surjective c
    have he : (e (n (u, k))).2 = K.equiv k := by
      change K.equiv (n.symm (n (u, k))).2 = K.equiv k
      rw [n.symm_apply_apply]
    rw [he, map_eq_one_iff K.equiv K.equiv.injective, hn]
    constructor
    · intro hk
      simp only [hk, Subgroup.coe_one, mul_one]
      exact u.property
    · intro h
      apply Subtype.ext
      exact disjoint_def.mp K.U_disjoint (by
        simpa only [inv_mul_cancel_left] using F.U.mul_mem (F.U.inv_mem u.property) h)
        k.property

/-- The full centralizer has the genuine marked E₄ × A₅ model. -/
theorem exists_secondCentralizer (L : LocalCensus D)
    (ht : OtherInvolution D t) (Q : RecognizedQuotient F) :
    ∃ C : SecondCentralizer D t, C.fourFactor = F.U ∧ C.fiveFactor = K.K := by
  obtain ⟨e, heK, heU⟩ := K.exists_coordinates ht Q
  let C : SecondCentralizer D t :=
    ⟨e, fun u hu => (K.involution_fusion L u hu).trans (heK u).symm⟩
  refine ⟨C, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      apply (heU (e.symm a)).mp
      simpa using ha.2
    · intro u hu
      let c : involutionCentralizer t := ⟨u, F.join_le_centralizer (mem_sup_right hu)⟩
      exact ⟨e c, ⟨mem_top _, (heU c).mpr hu⟩, by simp [SecondCentralizer.embedding, C, c]⟩
  · apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      apply (heK (e.symm a)).mp
      simpa using ha.1
    · intro k hk
      let c : involutionCentralizer t := ⟨k, K.le_centralizer hk⟩
      exact ⟨e c, ⟨(heK c).mpr hk, mem_top _⟩, by simp [SecondCentralizer.embedding, C, c]⟩

include K in
theorem rootCore_eq (L : LocalCensus D) (ht : OtherInvolution D t)
    (Q : RecognizedQuotient F) : rootCore t = F.U := by
  obtain ⟨C, hU, _⟩ := K.exists_secondCentralizer L ht Q
  exact C.rootCore_eq_fourFactor.trans hU

private theorem quasisimple : IsQuasisimple K.K := by
  let : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple A5 := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  exact IsQuasisimple.of_mulEquiv K.equiv.symm

private theorem derived_eq (ht : OtherInvolution D t) (Q : RecognizedQuotient F) :
    _root_.commutator (involutionCentralizer t) = K.K.subgroupOf (involutionCentralizer t) := by
  let N := K.K.subgroupOf (involutionCentralizer t)
  let : N.Normal := K.normal
  let : IsQuasisimple K.K := K.quasisimple
  let : IsQuasisimple N := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe K.le_centralizer).symm
  have hN : Nat.card N = 60 :=
    (Nat.card_congr (subgroupOfEquivOfLe K.le_centralizer).toEquiv).trans K.card
  have hC := Q.kernel.centralizer_card ht.1 Q.equiv
  have hq : Nat.card (involutionCentralizer t ⧸ N) = 2 ^ 2 := by
    have h := N.index_mul_card
    rw [hN, hC] at h
    change Nat.card (involutionCentralizer t ⧸ N) * 60 = 240 at h
    omega
  change _root_.commutator (involutionCentralizer t) = N
  apply le_antisymm
  · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq hq)
  · rw [← N.commutator_eq_self]
    exact commutator_mono le_top le_top

theorem component_eq (ht : OtherInvolution D t) (Q : RecognizedQuotient F) :
    rootComponent t = K.K := by
  let N := K.K.subgroupOf (involutionCentralizer t)
  let : IsQuasisimple K.K := K.quasisimple
  let : IsQuasisimple N := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe K.le_centralizer).symm
  have hN : IsComponent (involutionCentralizer t) N :=
    ⟨K.normal.isSubnormal, inferInstance⟩
  have he : componentLayer (involutionCentralizer t) = N := by
    change sSup {J : Subgroup (involutionCentralizer t) | IsComponent (involutionCentralizer t) J} = N
    refine le_antisymm ?_ (le_sSup hN)
    apply sSup_le
    intro J hJ
    let : IsQuasisimple J := hJ.2
    change J ≤ K.K.subgroupOf (involutionCentralizer t)
    rw [← K.derived_eq ht Q]
    rw [← J.commutator_eq_self]
    exact commutator_mono le_top le_top
  rw [rootComponent, he, map_subgroupOf_eq_of_le K.le_centralizer]

include K in
theorem z_mem_component (ht : OtherInvolution D t) (Q : RecognizedQuotient F) :
    D.z ∈ rootComponent t := by
  rw [K.component_eq ht Q]
  exact K.E_le F.z_mem

private theorem X3_normalizes (ht : OtherInvolution D t) (Q : RecognizedQuotient F) :
    F.X3 ≤ normalizer (K.K : Set G) := by
  have hC : F.X3 ≤ normalizer (involutionCentralizer t : Set G) := by
    rw [← K.centralizer_U_eq ht Q]
    exact F.X3_normalizes.trans (normalizer_le_normalizer_centralizer F.U)
  have hd : ⁅involutionCentralizer t, involutionCentralizer t⁆ = K.K := by
    rw [← map_subtype_commutator, K.derived_eq ht Q,
      map_subgroupOf_eq_of_le K.le_centralizer]
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [← hd, map_commutator, mem_normalizer_iff_map_conj_eq.mp (hC hx)]

theorem X3_centralizes (ht : OtherInvolution D t) (Q : RecognizedQuotient F) :
    F.X3 ≤ centralizer (K.K : Set G) := by
  intro x hx
  apply K.centralizes_of_normalizes_borel (K.X3_normalizes ht Q hx)
  have he : F.E ≤ centralizer ({x} : Set G) := by
    intro e he
    exact mem_centralizer_singleton_iff.mpr (F.X3_centralizes hx e (Or.inl he))
  have hX : F.X1 ≤ centralizer ({x} : Set G) := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (F.X3_centralizes hx y (Or.inr hy))
  intro a ha
  exact mem_centralizer_singleton_iff.mp (sup_le he hX ha)

include K in
/-- All intrinsic markings of the centralizer, with the cubic actor centralizing its layer. -/
theorem exists_markedCentralizer (L : LocalCensus D)
    (ht : OtherInvolution D t) (Q : RecognizedQuotient F) :
    ∃ C : SecondCentralizer D t,
      C.fourFactor = F.U ∧ rootComponent t = C.fiveFactor ∧
      D.z ∈ rootComponent t ∧ F.X3 ≤ centralizer (rootComponent t : Set G) := by
  obtain ⟨C, hU, hK⟩ := K.exists_secondCentralizer L ht Q
  refine ⟨C, hU, (K.component_eq ht Q).trans hK.symm, K.z_mem_component ht Q, ?_⟩
  rw [K.component_eq ht Q]
  exact K.X3_centralizes ht Q

include K in
/-- The marked normalizer follows by multiplication from the two independent lifts. -/
theorem unalignedGeometry_of_cubicFourModel (L : LocalCensus D)
    (ht : OtherInvolution D t) (Q : RecognizedQuotient F) (V : CubicFourModel F) :
    Nonempty (UnalignedGeometry D t) := by
  obtain ⟨C, hU, hcomp, hz, _⟩ := K.exists_markedCentralizer L ht Q
  let H := F.U ⊔ F.X3
  have hc : H ≤ centralizer (K.K : Set G) :=
    sup_le K.U_centralizes (K.X3_centralizes ht Q)
  have hd : Disjoint H K.K := by
    apply disjoint_def.mpr
    intro x hxH hxK
    have hx : (⟨x, hxK⟩ : K.K) ∈ center K.K :=
      mem_center_iff.mpr (fun y => Subtype.ext (hc hxH y y.property))
    have hxe : K.equiv ⟨x, hxK⟩ ∈ center A5 :=
      (centerCongr K.equiv ⟨⟨x, hxK⟩, hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp)] at hxe
    exact congrArg Subtype.val
      (K.equiv.injective ((mem_bot.mp hxe).trans (map_one K.equiv).symm))
  have hj : H ⊔ K.K = normalizer (rootCore t : Set G) := by
    rw [K.rootCore_eq L ht Q, K.normalizer_U_eq ht Q, ← K.join_eq ht Q]
    simpa only [H, sup_assoc] using sup_left_comm F.U F.X3 K.K
  obtain ⟨m, hm⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting H K.K hd hc
  let n : H × K.K ≃* normalizer (rootCore t : Set G) :=
    m.trans (MulEquiv.subgroupCongr hj)
  let e : normalizer (rootCore t : Set G) ≃* (A4 × A5) :=
    n.symm.trans (V.equiv.prodCongr K.equiv)
  have he (a : A4) (b : A5) : (e.symm (a, b) : G) =
      (V.equiv.symm a : G) * (K.equiv.symm b : G) := by
    exact hm (V.equiv.symm a) (K.equiv.symm b)
  refine ⟨⟨C, hcomp, hz, e, ?_, ?_⟩⟩
  · rw [K.component_eq ht Q]
    apply le_antisymm
    · rintro _ ⟨⟨a, b⟩, hab, rfl⟩
      change (e.symm (a, b) : G) ∈ K.K
      rw [he, show a = 1 from hab.1, map_one, Subgroup.coe_one, one_mul]
      exact (K.equiv.symm b).property
    · intro k hk
      refine ⟨(1, K.equiv ⟨k, hk⟩), ⟨rfl, mem_top _⟩, ?_⟩
      change (e.symm (1, K.equiv ⟨k, hk⟩) : G) = k
      rw [he, map_one, Subgroup.coe_one, one_mul, K.equiv.symm_apply_apply]
  · refine Eq.trans (b := F.U) ?_ (K.rootCore_eq L ht Q).symm
    apply le_antisymm
    · rintro _ ⟨⟨a, b⟩, hab, rfl⟩
      change (e.symm (a, b) : G) ∈ F.U
      rw [he, show b = 1 from hab.2, map_one, Subgroup.coe_one, mul_one]
      exact V.core_eq.le (mem_map_of_mem _ hab.1)
    · intro u hu
      rw [← V.core_eq] at hu
      obtain ⟨a, ha, hau⟩ := hu
      refine ⟨(a, 1), ⟨ha, rfl⟩, ?_⟩
      change (e.symm (a, 1) : G) = u
      rw [he, map_one, Subgroup.coe_one, mul_one]
      exact hau
end LiftedFive

namespace RecognizedQuotient
variable {F : LocalFrame D t} (Q : RecognizedQuotient F)

include Q

/-- The chosen four-group is the intrinsic two-core of the full centralizer. -/
theorem rootCore_eq (L : LocalCensus D) (ht : OtherInvolution D t) :
    rootCore t = F.U := by
  obtain ⟨K⟩ := Q.nonempty_liftedFive L ht
  exact K.rootCore_eq L ht Q

/-- The marked quotient recognition supplies the split centralizer and its
root-core normalizer, including fusion, the intrinsic component, the placement
of `D.z`, and both literal normalizer-factor embeddings. Transfer and the cubic
action discharge the independent A₅-lift and A₄-model premises. -/
theorem nonempty_unalignedGeometry (L : LocalCensus D) (ht : OtherInvolution D t) :
    Nonempty (UnalignedGeometry D t) := by
  obtain ⟨K⟩ := Q.nonempty_liftedFive L ht
  obtain ⟨V⟩ := F.nonempty_cubicFourModel
  exact K.unalignedGeometry_of_cubicFourModel L ht Q V

end RecognizedQuotient
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
