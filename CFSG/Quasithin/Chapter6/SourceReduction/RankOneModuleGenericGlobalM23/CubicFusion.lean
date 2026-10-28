module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Fusion
public import Theory.GroupTheory.Recognition.QuasithinM23.CubicFusion
public import Theory.GroupTheory.Recognition.QuasithinM23.ExceptionalCubics

/-!
# Cubic and commuting-pair fusion in the original nonmaximal linear row

The already constructed central involution has an elementary core and
PSL₃(2) centralizer quotient. Cubic fusion lifts through this elementary
kernel. Ambient involution fusion then moves any commuting involution to
that representative, proving source 5.2.14(1). The same argument inside
centralizers fuses involutions by conjugators in the literal cubic
centralizer; this supplies the fusion
input needed in the recognition step of 5.2.15.

Every cubic in the original exceptional local centralizes an actual
involution there. The fixed-vector case uses its elementary core; the
fixed-point-free case uses the three-cycle quotient and coprime centralizer
lifting. Thus all cubics of that local are fused in G. This is the
exceptional-local part of 5.2.14(2); fusion for the entire other local and
the cubic-normalizer identification remain separate obligations.

Source: Aschbacher–Smith 5.2.14–15, printed pp.654–655 (`refs/quasithin.pdf`).
All statements retain the original field and compatible amalgam, without
ambient recognition or splitting assumptions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem cubic_centralizer_setup
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    : ∃ z : G, orderOf z = 2 ∧
      ∀ a b : centralizer ({z} : Set G), orderOf a = 3 → orderOf b = 3 → IsConj a b := by
  obtain ⟨_,hc⟩ := d.linear_maximal_or_exceptional h hH hp F hm hF he
  obtain ⟨_,J,hJ,hKJ,_⟩ := hc.resolve_left hnonmax
  obtain ⟨hU,_,_⟩ := d.linear_overcomponent_action h hH.1.1.2 hp F hm hF he hJ.1 hKJ.le
  let := hU
  obtain ⟨_,_,z,_,hz,_,_,hcore,hquot,_⟩ :=
    d.linear_exceptional_centralizer_geometry h hH hp F hm hF he hJ hKJ
  let C := centralizer ({z} : Set G)
  let e : pCore 2 C ≃* pCore 2 J :=
    ((pCore 2 C).equivMapOfInjective C.subtype C.subtype_injective).trans
      ((MulEquiv.subgroupCongr hcore).trans
        ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).symm)
  let : IsElementaryAbelian 2 (pCore 2 C) :=
    IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  exact ⟨z,hz,fun a b ha hb =>
    QuasithinM23.elementary_psl3Two_cubics_isConj (pCore 2 C) hquot.some ha hb⟩

/-- Source 5.2.14(1): all elements of order three centralizing involutions
are conjugate in the original ambient group. -/
theorem Preparation.linear_nonmaximal_cubics_isConj
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    {a b : G} (ha : orderOf a = 3) (hb : orderOf b = 3)
    (ha2 : ∃ x : G, orderOf x = 2 ∧ Commute a x)
    (hb2 : ∃ x : G, orderOf x = 2 ∧ Commute b x) : IsConj a b := by
  obtain ⟨z,hz,hc⟩ := cubic_centralizer_setup d h hH hp F hm hF he hnonmax
  exact QuasithinM23.cubics_isConj_of_involution_fusion z
    (fun x hx => d.linear_nonmaximal_involutions_isConj h hH hp F hm hF he hnonmax hx hz)
    hc ha hb ha2 hb2

/-- The cubic class is unique inside each actual involution centralizer. -/
theorem Preparation.linear_nonmaximal_involution_centralizer_cubics_isConj
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    (t : G) (ht : orderOf t = 2)
    (a b : centralizer ({t} : Set G)) (ha : orderOf a = 3) (hb : orderOf b = 3) :
    IsConj a b := by
  obtain ⟨z,hz,hc⟩ := cubic_centralizer_setup d h hH hp F hm hF he hnonmax
  exact QuasithinM23.involution_centralizer_cubics_isConj z
    (fun x hx => d.linear_nonmaximal_involutions_isConj h hH hp F hm hF he hnonmax hx hz)
    hc t ht a b ha hb

/-- Commuting-pair fusion gives the genuine involution-fusion input inside
the cubic centralizer used in the recognition argument of source 5.2.15. -/
theorem Preparation.linear_nonmaximal_cubic_centralizer_involutions_isConj
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    (c : G) (hc3 : orderOf c = 3)
    (s t : centralizer ({c} : Set G)) (hs : orderOf s = 2) (ht : orderOf t = 2) :
    IsConj s t := by
  obtain ⟨z,hz,hc⟩ := cubic_centralizer_setup d h hH hp F hm hF he hnonmax
  exact QuasithinM23.cubic_centralizer_involutions_isConj z
    (fun x hx => d.linear_nonmaximal_involutions_isConj h hH hp F hm hF he hnonmax hx hz)
    hc c hc3 s t hs ht

/-- Every cubic in the original exceptional overcomponent centralizes an
involution there, including the fixed-point-free cubic row. -/
theorem Preparation.linear_exceptional_cubic_centralizes_involution
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J) (c : J) (hc : orderOf c = 3) :
    ∃ z : J, orderOf z = 2 ∧ Commute c z := by
  have hTH := hH.1.1.2
  have hn := (d.block_overcomponent_parameter h hTH hp F hm hF (.inl he) hJ.1 hKJ).1
  have hb := d.linear_four_overcomponent_exceptional (hn ▸ h) hTH hp F hm hF he hJ.1 hKJ
  obtain ⟨ha,hcard,_⟩ := d.linear_overcomponent_action h hTH hp F hm hF he hJ.1 hKJ.le
  rw [hn] at hcard
  have hcard : Nat.card (pCore 2 J) = 16 := hcard
  let := ha
  let e := hb.2.1.some
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 J :=
    (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans (QuotientGroup.ker_mk' _)
  have hC : centralizer (pCore 2 J : Set J) = pCore 2 J :=
    le_antisymm (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
      (h.qtke.evenCharacteristic T) hJ.1) (fun x hx y hy => setLike_mul_comm hy hx)
  exact QuasithinM23.exceptional_cubic_centralizes_involution (pCore 2 J) hcard q hq hk hC c hc

/-- The exceptional-local part of source 5.2.14(2): all its cubics are
conjugate in G, with no splitting or ambient recognition assumption. -/
theorem Preparation.linear_nonmaximal_exceptional_cubics_isConj
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J) (a b : J) (ha : orderOf a = 3) (hb : orderOf b = 3) :
    IsConj (a : G) (b : G) := by
  obtain ⟨s,hs,has⟩ := d.linear_exceptional_cubic_centralizes_involution h hH hp F hm hF he hJ hKJ a ha
  obtain ⟨t,ht,hbt⟩ := d.linear_exceptional_cubic_centralizes_involution h hH hp F hm hF he hJ hKJ b hb
  exact d.linear_nonmaximal_cubics_isConj h hH hp F hm hF he hnonmax
    ((Subgroup.orderOf_coe a).trans ha) ((Subgroup.orderOf_coe b).trans hb)
    ⟨s,(Subgroup.orderOf_coe s).trans hs,has.map J.subtype⟩
    ⟨t,(Subgroup.orderOf_coe t).trans ht,hbt.map J.subtype⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
