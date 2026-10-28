module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.Inputs
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.Transport
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.FixedImage
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers.AlternatingLift
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers.Models
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers.ProductMark
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers.SymmetricMark
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers.SectionLayer
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic

/-!
# The A₈ and A₆ layers in the HS covering fixed subgroups

The explicit earlier inputs are the HS center bound from 16.1.2(2) and
the involution-lifting clause I.2.2(5a). A marked 2-central double
transposition has an involutory lift, and all its lifts have the same square
in the double central cover. The Schur-cover calculation then constructs a
section over A₈ or A₆; perfect-lift uniqueness identifies the full fixed
subgroup layer with that alternating group.

The two root marks are proved in the actual HS carrier: each is an
involutory square, so the exhaustive HS involution-class calculation places
it in the center of a genuine Sylow two-subgroup. Thus
`Configuration.coverLayerIdentification` discharges both marks and proves
both layer equivalences. Only the stated earlier center bound and lifting
clause remain explicit; the source-theorem assembly must supply them.
Neither splitting nor the desired layers are premises.

Source: Aschbacher–Smith 16.1.2, p.1170; 16.1.5(10) and 16.1.7(3h),
pp.1172–1173; I.2.2(5a) and its proof, pp.409–412; 16.3.5, p.1179.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers
open Subgroup Theory.GroupTheory
open GLS3.Chapter5.SchurPresentation
open DoubleCoverCentralizer
open OtherPreliminaries.JankoTwoHigmanSims
variable {G : Type*} [Group G]

/-- I.2.2(5a), expressed using the specified actual HS quotient model.
This is a source premise, not a splitting assertion. -/
def TwoCentralLifting (I : Subgroup G)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) : Prop :=
  ∀ x : Sporadic.LeechRelated.HS.Carrier, orderOf x = 2 → TwoCentral x →
    ∃ y : I, modelProjection I e y = x ∧ orderOf y = 2

theorem modelProjection_ker (I : Subgroup G)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) :
    (modelProjection I e).ker = pCore 2 I := by
  ext x
  change e (QuotientGroup.mk' (pCore 2 I) x) = 1 ↔ x ∈ pCore 2 I
  rw [← map_one e, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

/-- In a double central cover, one involutory lift makes every lift involutory. -/
theorem root_lifts_sq_one [Finite G] (I : Subgroup G)
    (hz : center I = pCore 2 I) (hc : Nat.card (center I) = 2)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hlift : TwoCentralLifting I e)
    (x : Sporadic.LeechRelated.HS.Carrier) (hx : orderOf x = 2) (hmark : TwoCentral x)
    (y : I) (hy : modelProjection I e y = x) : y ^ 2 = 1 := by
  obtain ⟨z, hzq, hz2⟩ := hlift x hx hmark
  have hq : QuotientGroup.mk' (center I) y = QuotientGroup.mk' (center I) z := by
    have h : QuotientGroup.mk' (pCore 2 I) y = QuotientGroup.mk' (pCore 2 I) z :=
      e.injective (hy.trans hzq.symm)
    apply QuotientGroup.eq.mpr
    rw [hz]
    exact QuotientGroup.eq.mp h
  rw [DoubleCoverCentralizer.square_eq_of_quotient_eq hc hq, ← hz2, pow_orderOf_eq_one]

/-- The generic reduction for either alternating row. No surjectivity of
fixed points and no splitting of a covering centralizer is assumed. -/
theorem layer_equiv_of_root_lifts [Finite G] (I : Subgroup G)
    (hz : pCore 2 I ≤ center I) (hc : Nat.card (pCore 2 I) ≤ 2)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) (r : MulAut I)
    (n : ℕ) (j : alternatingGroup (Fin (n + 5)) →* (modelAction I e r).fixedSubgroup)
    (hj : Function.Injective j) (hn : j.range.Normal)
    (hunique : ∀ K : Subgroup (modelAction I e r).fixedSubgroup,
      IsComponent _ K → K = j.range)
    (hlift : ∀ x : I, modelProjection I e x = (j (rootInvolution n)).val → x ^ 2 = 1) :
    Nonempty (componentLayer r.fixedSubgroup ≃* alternatingGroup (Fin (n + 5))) := by
  let f := modelProjection I e
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfz : f.ker ≤ center I := (modelProjection_ker I e).le.trans hz
  have hfc : Nat.card f.ker ≤ 2 := by rw [modelProjection_ker]; exact hc
  let k := (modelAction I e r).fixedSubgroup.subtype.comp j
  have hk : Function.Injective k := Subtype.val_injective.comp hj
  obtain ⟨s, hs⟩ := exists_section_over_alternating n f hf hfz hfc k hk hlift
  let : IsQuasisimple (alternatingGroup (Fin (n + 5))) := alternatingGroup_isQuasisimple n
  exact layer_equiv_of_section I hz e r j hj hn hunique s hs

/-- Transport a concrete row embedding while retaining its unique component. -/
theorem layer_equiv_of_model_root_lifts [Finite G] {R : Type*} [Group R]
    (I : Subgroup G) (hz : pCore 2 I ≤ center I) (hc : Nat.card (pCore 2 I) ≤ 2)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) (r : MulAut I)
    (n : ℕ) (v : (modelAction I e r).fixedSubgroup ≃* R)
    (j : alternatingGroup (Fin (n + 5)) →* R) (hj : Function.Injective j)
    (hn : j.range.Normal) (hunique : ∀ K : Subgroup R, IsComponent _ K → K = j.range)
    (hlift : ∀ x : I, modelProjection I e x = (v.symm (j (rootInvolution n))).val →
      x ^ 2 = 1) :
    Nonempty (componentLayer r.fixedSubgroup ≃* alternatingGroup (Fin (n + 5))) := by
  let k := v.symm.toMonoidHom.comp j
  have hk : Function.Injective k := v.symm.injective.comp hj
  have hkn : k.range.Normal := by
    rw [MonoidHom.range_comp]
    exact hn.map _ v.symm.surjective
  have hku (K : Subgroup (modelAction I e r).fixedSubgroup) (hK : IsComponent _ K) :
      K = k.range := by
    have he := congrArg (Subgroup.map v.symm.toMonoidHom)
      (hunique _ (hK.map_equiv v))
    have hid : v.symm.toMonoidHom.comp v.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [map_map, hid, map_id] at he
    exact he.trans (MonoidHom.range_comp v.symm.toMonoidHom j).symm
  exact layer_equiv_of_root_lifts I hz hc e r n k hk hkn hku hlift

/-- Assembly after the two concrete root marks are proved. The center-size
and lifting premises are the literal earlier source clauses 16.1.2(2) and
I.2.2(5a); neither includes either desired layer identification. -/
theorem coverLayerIdentification_of_root_marks [Finite G] (I : Subgroup G)
    (hz : center I = pCore 2 I) (hc : Nat.card (center I) = 2)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hlift : TwoCentralLifting I e)
    (h8 : ∀ (r : MulAut I), orderOf r = 2 →
      ∀ v : (modelAction I e r).fixedSubgroup ≃* S8, TwoCentral (symmetricRoot _ v))
    (h6 : ∀ (r : MulAut I), orderOf r = 2 →
      ∀ v : (modelAction I e r).fixedSubgroup ≃* C2 × MulAut A6, TwoCentral (productRoot _ v)) :
    CoverLayerIdentification I e := by
  have hcard : Nat.card (pCore 2 I) ≤ 2 := by rw [← hz, hc]
  intro r hr
  constructor
  · rintro ⟨v⟩
    exact layer_equiv_of_model_root_lifts I hz.ge hcard e r 3 v
      symmetricEmbedding symmetricEmbedding_injective symmetricEmbedding_normal
      symmetric_component_unique
      (root_lifts_sq_one I hz hc e hlift _ (symmetricRoot_order _ v) (h8 r hr v))
  · rintro ⟨v⟩
    exact layer_equiv_of_model_root_lifts I hz.ge hcard e r 1 v
      productEmbedding productEmbedding_injective productEmbedding_normal
      product_component_unique
      (root_lifts_sq_one I hz hc e hlift _ (productRoot_order _ v) (h6 r hr v))

/-- The two HS covering layers, from the center size and the literal
involution-lifting clause I.2.2(5a). Both concrete root marks are discharged
in the actual HS carrier. -/
theorem coverLayerIdentification [Finite G] (I : Subgroup G)
    (hz : center I = pCore 2 I) (hc : Nat.card (center I) = 2)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hlift : TwoCentralLifting I e) : CoverLayerIdentification I e :=
  coverLayerIdentification_of_root_marks I hz hc e hlift
    (fun r _ v => symmetricRoot_twoCentral (modelAction I e r) v)
    (fun r _ v => productRoot_twoCentral (modelAction I e r) v)

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers

namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses
open Subgroup Theory.GroupTheory CoverLayers
open OtherPreliminaries.JankoTwoHigmanSims
open DoubleCoverCentralizer
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Configuration supplies the central quotient and its nontriviality.
This intermediate reduction keeps the two concrete root marks explicit;
`Configuration.coverLayerIdentification` below discharges them. -/
theorem Configuration.coverLayerIdentification_of_root_marks {𝒦 : GroupClass.{u}}
    {E L I : Subgroup G} {a i : G} (h : Configuration 𝒦 E L I a i)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hcard : Nat.card (center I) ≤ 2) (hlift : TwoCentralLifting I e)
    (h8 : ∀ (r : MulAut I), orderOf r = 2 →
      ∀ v : (modelAction I e r).fixedSubgroup ≃* S8, TwoCentral (symmetricRoot _ v))
    (h6 : ∀ (r : MulAut I), orderOf r = 2 →
      ∀ v : (modelAction I e r).fixedSubgroup ≃* C2 × MulAut A6, TwoCentral (productRoot _ v)) :
    CoverLayerIdentification I e := by
  have hne : center I ≠ ⊥ := h.center_eq_core ▸ h.core_ne
  have hlt := (Subgroup.one_lt_card_iff_ne_bot (center I)).mpr hne
  exact CoverLayers.coverLayerIdentification_of_root_marks I h.center_eq_core
    (by omega) e hlift h8 h6

/-- In the HS configuration, every involutory actor with quotient fixed
subgroup S₈ (respectively C₂ × Aut(A₆)) has fixed-subgroup layer A₈
(respectively A₆). The only additional inputs are the HS specialization of
16.1.2(2) and the involution-lifting clause I.2.2(5a). -/
theorem Configuration.coverLayerIdentification {𝒦 : GroupClass.{u}}
    {E L I : Subgroup G} {a i : G} (h : Configuration 𝒦 E L I a i)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hcard : Nat.card (center I) ≤ 2) (hlift : TwoCentralLifting I e) :
    CoverLayerIdentification I e :=
  h.coverLayerIdentification_of_root_marks e hcard hlift
    (fun r _ v => symmetricRoot_twoCentral (modelAction I e r) v)
    (fun r _ v => productRoot_twoCentral (modelAction I e r) v)

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses
