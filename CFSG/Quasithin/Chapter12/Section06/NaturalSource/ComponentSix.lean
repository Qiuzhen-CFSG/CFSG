module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRanks
public import Theory.GroupTheory.SmallFittingResidual
public import Theory.SpecificGroups.AlternatingSix.TripleCentralInvolution
public import Theory.SpecificGroups.AlternatingSix.InvolutionCubicPlane
public import Theory.SpecificGroups.Alternating.TwoThreeCycles

/-!
# Ordinary and triple-covered A₆ are excluded at the original component

The two-perfect point residual centralizes the cubic component center.
Rank saturation then puts this center in each original Sylow E₉ after
H → H/O₂(H). The marked V-star centralizes that E₉, so its literal action
fixes the covering center. In a triple A₆ cover this forces the involution
to be inner, with two-group automorphism centralizer. The nontrivial
two-perfect image of L₁ cannot lie in that centralizer.

In the ordinary A₆ row, rank saturation makes the original Sylow E₉
action faithful. It centralizes the same marked involution, contrary to
the actual A₆ automorphism fixed-group calculations.

The proof keeps the original point, residual, component and action. It
uses neither an assumed natural reduction nor an identification of the
two-core kernel with the component center. The classical, A₇ and M₂₂
cover rows and the remaining rank-one/two exclusions are still open.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The actual cubic component center lies in each original Sylow E₉ image. -/
theorem SourceHypothesis.original_component_center_le_residual_sylow
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H)
    (hcard : Nat.card (center (Nonabelian.Setup.star H c.K)) = 3)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    (center (Nonabelian.Setup.star H c.K)).map (Nonabelian.Setup.star H c.K).subtype ≤
      Nonabelian.Setup.star H ((P : Subgroup (D.fullSetup hZ T z).L₁).map
        (D.fullSetup hZ T z).L₁.subtype) := by
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let Z := (center B).map B.subtype
  let A := Nonabelian.Setup.star H E.L₁
  let R := Nonabelian.Setup.star H ((P : Subgroup E.L₁).map E.L₁.subtype)
  have hnZ : A ≤ normalizer (Z : Set (Nonabelian.Setup.Hstar H)) :=
    (S.original_residual_star_normalizes_selectedComponent D hZ z hz hH c).trans
      (normalizer_le_normalizer_characteristic_image B (center B))
  have hcZ : Nat.card Z = 3 := by
    rw [card_map_of_injective B.subtype_injective]
    exact hcard
  let f : A →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion hnZ)
  have hf : f = 1 := (S.original_point_residual_star_twoPerfect D hZ z hH).hom_eq_one_of_isPGroup
    (aut_two_of_card_one_or_three Z (Or.inr hcZ)) f
  have hAZ : A ≤ centralizer (Z : Set (Nonabelian.Setup.Hstar H)) := by
    intro x hx y hy
    have he := congrArg (fun g : A →* MulAut Z => (g ⟨x,hx⟩ ⟨y,hy⟩ : Nonabelian.Setup.Hstar H)) hf
    change x*y*x⁻¹=y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hRA : R ≤ A := map_mono (comap_mono (map_subtype_le _))
  obtain ⟨hR,hRc,_⟩ := S.original_point_sylow_star D hZ z hz hTz hH P
  let := hR
  intro x hx
  apply R.mem_of_pow_eq_one_of_elementary_card_le
    (fun Q hQ => by
      rw [hRc]
      exact (primeRank_le_iff_elementary_card_le (Nonabelian.Setup.Hstar H)).mp
        (S.original_star_three_rank D hZ z hz hH) Q hQ)
  · exact congrArg Subtype.val (hcZ ▸ pow_card_eq_one' (x := (⟨x,hx⟩ : Z)))
  · exact le_centralizer_iff.mp (hRA.trans hAZ) hx

/-- The original module action fixes the actual cubic covering center. -/
theorem SourceHypothesis.original_component_center_fixed
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hcard : Nat.card (center (Nonabelian.Setup.star H c.K)) = 3) :
    ∀ t ∈ (V.subgroupOf c.localActor).map a.action,
      ∀ x ∈ center (Nonabelian.Setup.star H c.K), t x = x := by
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let P : Sylow 3 E.L₁ := Sylow.nonempty.some
  have hC := S.original_component_center_le_residual_sylow D hZ z hz hTz hH c hcard P
  have hRA : Nonabelian.Setup.star H ((P : Subgroup E.L₁).map E.L₁.subtype) ≤
      Nonabelian.Setup.star H E.L₁ := map_mono (comap_mono (map_subtype_le _))
  have hCV := (hC.trans hRA).trans
    (S.original_point_residual_star_centralizes D hZ z hz hTV hTz hbound hH hn)
  rintro _ ⟨t,ht,rfl⟩ x hx
  apply Subtype.ext
  rw [a.conjugation]
  have hv : QuotientGroup.mk' (pCore 2 H) (inclusion a.local_le t) ∈ Nonabelian.Setup.star H V :=
    mem_map_of_mem _ ht
  have hc := hCV (mem_map_of_mem B.subtype hx) _ hv
  change _ * x.val = x.val * _ at hc
  rw [hc,mul_inv_cancel_right]

/-- The original contrary-nonabelian configuration excludes the triple A₆ cover. -/
theorem SourceHypothesis.original_selectedComponent_not_alternatingSixCover
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking) :
    ¬ Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 6 := by
  rintro ⟨_,⟨ec⟩,⟨e⟩⟩
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  have hcard : Nat.card (center B) = 3 := by
    rw [Nat.card_congr ec.toEquiv]
    simp
  let U := (V.subgroupOf c.localActor).map a.action
  let A := ((D.fullSetup hZ T z).L₁.subgroupOf c.localActor).map a.action
  have hU : Nat.card U = 2 := a.module_card
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  have hto : orderOf (t : MulAut B) = 2 :=
    (orderOf_injective U.subtype U.subtype_injective t).trans ht
  have hp := AlternatingSix.TripleCentralInvolution.centralizer_isTwoGroup_of_fixes_center
    e hcard t hto (S.original_component_center_fixed D hZ z hz hTV hTz hbound hH hn c a hcard t t.property)
  have hAC : A ≤ centralizer ({(t : MulAut B)} : Set (MulAut B)) := by
    intro b hb
    apply mem_centralizer_singleton_iff.mpr
    exact (a.residual_centralizes hb t t.property).symm
  have hf := a.residual_twoPerfect.hom_eq_one_of_isPGroup hp (inclusion hAC)
  apply a.residual_ne_bot
  apply bot_unique
  intro b hb
  exact congrArg (fun f : A →* centralizer ({(t : MulAut B)} : Set (MulAut B)) =>
    (f ⟨b,hb⟩ : MulAut B)) hf

/-- The original marked Sylow E₉ excludes the ordinary A₆ row as well. -/
theorem SourceHypothesis.original_selectedComponent_not_alternatingSix
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking) :
    ¬ Chapter1.Section02.LocalModels.IsAlternating (Nonabelian.Setup.star H c.K) 6 := by
  rintro ⟨e⟩
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let P : Sylow 3 E.L₁ := Sylow.nonempty.some
  obtain ⟨hP,hPc⟩ := S.original_point_residual_sylow D hZ z hz hTz P
  let := hP
  have hc : center B = ⊥ := by
    apply bot_unique
    intro x hx
    have he := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center (alternatingGroup (Fin 6)) at he
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hr : primeRank 3 c.K = 2 := by
    rw [c.three_rank_eq_star]
    apply le_antisymm
    · exact (_root_.primeRank_le_of_injective 3 B.subtype B.subtype_injective).trans
        (S.original_star_three_rank D hZ z hz hH)
    · rw [primeRank_congr 3 e]
      exact alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
  let f : P →* MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr e).toMonoidHom.comp (a.residualSylowAction P)
  have hf : Function.Injective f := (MulAut.congr e).injective.comp
    (S.original_rank_two_centerless_sylow_faithful D hZ z hz hTz hH c a hr hc P)
  let U := (V.subgroupOf c.localActor).map a.action
  have hU : Nat.card U = 2 := a.module_card
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hU])
  have hto : orderOf (MulAut.congr e (t : MulAut B)) = 2 :=
    ((MulAut.congr e).orderOf_eq _).trans
      ((orderOf_injective U.subtype U.subtype_injective t).trans ht)
  apply AlternatingSix.ShadowLocal.no_faithful_nine_centralizing_involution hPc f hf _ hto
  intro p
  have hAX : E.L₁ ≤ c.localActor := le_sup_right.trans le_sup_left
  have hm : a.residualSylowAction P p ∈ (E.L₁.subgroupOf c.localActor).map a.action :=
    ⟨⟨p.val.val,hAX p.val.property⟩,p.val.property,rfl⟩
  have hcomm := (a.residual_centralizes hm t t.property).symm
  change MulAut.congr e (a.residualSylowAction P p) * MulAut.congr e t =
    MulAut.congr e t * MulAut.congr e (a.residualSylowAction P p)
  simpa only [map_mul] using congrArg (MulAut.congr e) hcomm

/-- At the actual selected component, the A.3.6 cover list loses its A₆ row. -/
theorem SourceHypothesis.original_selectedComponent_simple_or_remaining_cover
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking) :
    let B := Nonabelian.Setup.star H c.K
    IsSimpleGroup B ∨
      (Nonempty (center B ≃* Multiplicative (ZMod 3)) ∧
        ((∃ (unitary : Bool) (q : ℕ), Chapter1.Section02.LocalModels.CoverParameter unitary q ∧
          Chapter1.Section02.LocalModels.IsSLSign B unitary 3 q) ∨
        Chapter1.Section02.LocalModels.IsAlternatingCover B 7 ∨
        Chapter1.Section02.LocalModels.IsM22Cover B)) := by
  rcases S.original_selectedComponent_simple_or_cover D hZ z hz hH c with hs|⟨hc,hm⟩
  · exact Or.inl hs
  · refine Or.inr ⟨hc,?_⟩
    cases hm with
    | classical unitary q hq he => exact Or.inl ⟨unitary,q,hq,he⟩
    | alternating_six he => exact (S.original_selectedComponent_not_alternatingSixCover
        D hZ z hz hTV hTz hbound hH hn c a he).elim
    | alternating_seven he => exact Or.inr (Or.inl he)
    | mathieu he => exact Or.inr (Or.inr he)

/-- Original-source assembly retains condition (*), the same Sylow actions and
all rank alternatives while excluding both A₆ models on that selected K. -/
theorem SourceHypothesis.original_selectedComponent_without_six
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    ∃ c : (D.fullSetup hZ T z).SelectedComponent H, ∃ a : c.ActionMarking,
      let A := (((D.fullSetup hZ T z).L₁.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
      let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
      let C := centralizer (U : Set a.action.range)
      (Nat.card U = 2 ∧ 3 ∣ Nat.card A ∧
        A.subgroupOf C ≤ (pCore 3 (C ⧸ pCore 2 C)).comap (QuotientGroup.mk' (pCore 2 C)) ∧
        ∃ R : Sylow 2 a.action.range, U ≤ (R : Subgroup a.action.range) ∧
          U ≤ centralizer (R : Set a.action.range)) ∧
      (primeRank 3 c.K = 1 ∨ (primeRank 3 c.K = 2 ∧
        ∀ P : Sylow 3 (D.fullSetup hZ T z).L₁,
          Function.Injective (a.residualSylowAction P) ∨
            (Nonempty (center (Nonabelian.Setup.star H c.K) ≃* Multiplicative (ZMod 3)) ∧
              Chapter1.Section02.LocalModels.ThreeCoverModel (Nonabelian.Setup.star H c.K)))) ∧
      ¬ Chapter1.Section02.LocalModels.IsAlternating (Nonabelian.Setup.star H c.K) 6 ∧
      ¬ Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 6 := by
  obtain ⟨c,a,hc,hr⟩ := S.original_selectedComponent_rank_cases D hZ z hz hTV hTz hbound hns hH hn
  exact ⟨c,a,hc,hr,
    S.original_selectedComponent_not_alternatingSix D hZ z hz hTz hH c a,
    S.original_selectedComponent_not_alternatingSixCover D hZ z hz hTV hTz hbound hH hn c a⟩

end CFSG.Quasithin.Chapter12.Section06
