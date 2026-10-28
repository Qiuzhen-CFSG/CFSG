module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankOneRadical
public import Theory.SpecificGroups.Janko1.Model.InvolutionCentralizer.ThreeFree
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne

/-!
# The original rank-one J1 exclusion

All automorphisms of the actual J1 carrier are inner, so the original
X-hat range is the full inner group. The same marked V image becomes an
involution in J1. Its literal centralizer has a two-group solvable radical,
contradicting the cubic divisor supplied by condition (*).

Source: Aschbacher--Smith, proof of 12.6.26, printed p.833. Every original
point, action, quotient, TI and nonsingular-centralizer input is retained.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)

include hz hTV hTz hbound hH hn a in
/-- Condition (*) excludes J1 on the original selected component. -/
theorem SourceHypothesis.original_selectedComponent_not_jankoOne
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃* Janko1.Model) := by
  classical
  rintro ⟨e⟩
  let B := Nonabelian.Setup.star H c.K
  let : IsSimpleGroup B := S.original_selectedComponent_simple D hZ z hz hTV hTz
    hbound hH hn c a hTI hns
  let := c.component.2
  let : IsSimpleGroup Janko1.Model := e.symm.isSimpleGroup
  let : Group.IsPerfect Janko1.Model := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hzJ : center Janko1.Model = ⊥ := center_eq_bot_of_simple_perfect
  have hinner : Function.Surjective (MulAut.conj : B →* MulAut B) := by
    intro α
    obtain ⟨g,hg⟩ := Janko1.OuterCertificate.aut_inner (MulAut.congr e α)
    refine ⟨e.symm g,(MulAut.congr e).injective ?_⟩
    rw [MulAut.congr_conj,e.apply_symm_apply]
    exact hg
  have htop : a.action.range = ⊤ := by
    apply top_unique
    rw [←MonoidHom.range_eq_top.mpr hinner]
    change MulAut.innerSubgroup B ≤ a.action.range
    rw [←a.component_image]
    exact map_le_range _ _
  let j1Aut := MulEquiv.ofBijective (MulAut.conj : Janko1.Model →* MulAut Janko1.Model)
    ⟨Theory.GroupTheory.conj_injective_of_center_eq_bot hzJ,
      Janko1.OuterCertificate.aut_inner⟩
  let f : a.action.range ≃* Janko1.Model :=
    ((MulEquiv.subgroupCongr htop).trans topEquiv).trans
      ((MulAut.congr e).trans j1Aut.symm)
  let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
  have hU : Nat.card U = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (map_le_range _ _)).toEquiv]
    exact a.module_card
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  have ht' : orderOf (t : a.action.range) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hgen : zpowers (t : a.action.range) = U :=
    eq_of_le_of_card_ge (zpowers_le.mpr t.property) (by rw [Nat.card_zpowers,ht',hU])
  let C := centralizer (U : Set a.action.range)
  have hC : C = centralizer ({(t : a.action.range)} : Set a.action.range) := by
    change centralizer (U : Set a.action.range) = _
    calc
      centralizer (U : Set a.action.range) =
          centralizer (zpowers (t : a.action.range) : Set a.action.range) :=
        congrArg (fun A : Subgroup a.action.range => centralizer (A : Set a.action.range)) hgen.symm
      _ = _ := by rw [zpowers_eq_closure,centralizer_closure]
  let eC := (MulEquiv.subgroupCongr hC).trans
    (CentralizerSmallKernelTransport.centralizerEquiv f (t : a.action.range))
  let eR := (eC.subgroupMap (solvableRadical C)).trans
    (MulEquiv.subgroupCongr (map_solvableRadical_equiv eC))
  have hp := Janko1.InvolutionCentralizer.involution_radical_isTwoGroup
    (f t) ((f.orderOf_eq _).trans ht')
  have hd := S.original_action_centralizer_radical_three_dvd D hZ z hz hTV hTz
    hbound hH hn c a
  change 3 ∣ Nat.card (solvableRadical C) at hd
  rw [Nat.card_congr eR.toEquiv] at hd
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  rw [hk] at hd
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

end CFSG.Quasithin.Chapter12.Section06
