module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankTwoSporadic
public import Theory.SpecificGroups.Janko4.SylowCentralizerThreeCore
public import Theory.SpecificGroups.Janko4.Model.ElementarySylowFixers
public import Theory.SpecificGroups.Janko4.Model.Center
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Excluding J₄ on the original rank-two component

Full native automorphism innerness identifies the actual action range X-hat
with the marked J₄ component. The original V-hat generator remains central
in the image of a full Sylow two-subgroup. Transport its literal centralizer
and both intrinsic prime cores through this same group isomorphism.

Condition (*) embeds the original Sylow E₉ in O₃(C/O₂(C)), forcing rank at
least two. The native J₄ calculation bounds this rank by one while retaining
the cubic kernel in 3.M₂₂.2. This excludes the last sporadic alternative.
The earlier TI and nonsingular-centralizer inputs remain explicit; the
nonsporadic rows, rank-one branch and natural reduction remain obligations.
Source: Aschbacher–Smith, proof of 12.6.26, printed p.832, last paragraph.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
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
/-- Condition (*) excludes the native J4 component, retaining its cubic centralizer kernel. -/
theorem SourceHypothesis.original_rank_two_not_jankoFour
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃* Janko4.Model) := by
  classical
  rintro ⟨e⟩
  let B := Nonabelian.Setup.star H c.K
  have hinner : Function.Surjective (MulAut.conj : B →* MulAut B) := by
    intro α
    obtain ⟨g,hg⟩ := Janko4.AdequateLocal.conj_surjective (MulAut.congr e α)
    refine ⟨e.symm g,(MulAut.congr e).injective ?_⟩
    rw [MulAut.congr_conj,e.apply_symm_apply]
    exact hg
  have htop : a.action.range = ⊤ := by
    apply top_unique
    rw [←MonoidHom.range_eq_top.mpr hinner]
    change MulAut.innerSubgroup B ≤ a.action.range
    rw [←a.component_image]
    exact map_le_range _ _
  let j4Aut := MulEquiv.ofBijective (MulAut.conj : Janko4.Model →* MulAut Janko4.Model)
    ⟨Theory.GroupTheory.conj_injective_of_center_eq_bot Janko4.model_center_eq_bot,
      Janko4.AdequateLocal.conj_surjective⟩
  let f : a.action.range ≃* Janko4.Model :=
    ((MulEquiv.subgroupCongr htop).trans topEquiv).trans
      ((MulAut.congr e).trans j4Aut.symm)
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
  let q := QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)
  let eCore := (q.subgroupMap (pCore 3 _)).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 3 q))
  obtain ⟨R,_,hUR⟩ := S.original_action_module_sylow_central D hZ z hz hTV hTz hbound hH hn c a
  let Q := R.mapSurjective (f := f.toMonoidHom) f.surjective
  have hQ : (Q : Subgroup Janko4.Model) ≤ centralizer ({f t} : Set Janko4.Model) := by
    rintro _ ⟨x,hx,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact (f.map_mul _ _).symm.trans
      ((congrArg f ((hUR t.property) x hx)).trans (f.map_mul _ _))
  have hl := Janko4.InvolutionCentralizers.sylow_fixed_centralizer_quotient_threeCore_rank
    (f t) ((f.orderOf_eq _).trans ht') Q hQ
  have hh := S.original_rank_two_centralizer_core_rank D hZ z hz hTV hTz hbound hH hn c a hTI hns hr
  change 2 ≤ primeRank 3 (pCore 3 (C ⧸ pCore 2 C)) at hh
  rw [primeRank_equiv 3 eCore] at hh
  omega

include hz hTV hTz hbound hH hn a in
/-- Every Theorem C sporadic model is excluded on the same original rank-two component. -/
theorem SourceHypothesis.original_rank_two_not_sporadic
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    ¬ ChapterA.Section02.IsTheoremCSporadicModel (Nonabelian.Setup.star H c.K) := by
  intro hm
  exact S.original_rank_two_not_jankoFour D hZ z hz hTV hTz hbound hH hn c a hTI hns hr
    (S.original_rank_two_sporadic_jankoFour D hZ z hz hTV hTz hbound hH hn c a hTI hns hr hm)

end CFSG.Quasithin.Chapter12.Section06
