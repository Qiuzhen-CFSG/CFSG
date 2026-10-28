module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankTwoModels
public import Theory.Mathieu.SylowFixerCentralizers

/-!
# Excluding all Mathieu rows in the original rank-two branch

Transport the original V-hat involution and faithful Sylow E₉ action
through the actual component isomorphism. They commute, so nine divides
the full automorphism centralizer of that same Sylow-fixing involution.
The native five-model centralizer bounds give the contradiction. The
order of J₁ also excludes rank two, leaving five sporadic rows.

The original TI and nonsingular-centralizer inputs remain explicit.
No conclusion about the other simple rows, the rank-one branch, abelian
point span or universal NaturalReduction is asserted here.
Source: Aschbacher–Smith, proof of 12.6.26, printed p.832, last paragraph.
-/

public section
open Subgroup
open Theory.GroupTheory
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
/-- The same E9 embeds in the full model centralizer of the original marked involution. -/
theorem SourceHypothesis.original_rank_two_model_centralizer
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) {B : Type*} [Group B] [Finite B]
    (e : Nonabelian.Setup.star H c.K ≃* B) :
    ∃ α : MulAut B, orderOf α = 2 ∧
      (∃ R : Sylow 2 B, ∀ x ∈ R, α x = x) ∧
      9 ∣ Nat.card (centralizer ({α} : Set (MulAut B))) := by
  let U := (V.subgroupOf c.localActor).map a.action
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [show Nat.card U = 2 from a.module_card])
  let α := MulAut.congr e (t : MulAut (Nonabelian.Setup.star H c.K))
  have hα : orderOf α = 2 := ((MulAut.congr e).orderOf_eq _).trans ((Subgroup.orderOf_coe t).trans ht)
  obtain ⟨R,hR⟩ := S.original_action_module_fixes_component_sylow D hZ z hz hTV hTz hbound hH hn c a
  let Q := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : ∀ x ∈ Q, α x = x := by
    rintro _ ⟨x,hx,rfl⟩
    change e ((t : MulAut _) (e.symm (e x))) = e x
    rw [e.symm_apply_apply,hR t t.property x hx]
  refine ⟨α,hα,⟨Q,hQ⟩,?_⟩
  let P : Sylow 3 (D.fullSetup hZ T z).L₁ := default
  have hPc := (S.original_point_residual_sylow D hZ z hz hTz P).2
  let f := (MulAut.congr e).toMonoidHom.comp (a.residualSylowAction P)
  have hf : Function.Injective f := (MulAut.congr e).injective.comp
    (S.original_rank_two_sylow_faithful D hZ z hz hTV hTz hbound hH hn c a hTI hns hr P)
  let g : P →* centralizer ({α} : Set (MulAut B)) := f.codRestrict _ (by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    have hAX : (D.fullSetup hZ T z).L₁ ≤ c.localActor := le_sup_right.trans le_sup_left
    have hx : a.residualSylowAction P x ∈
        ((D.fullSetup hZ T z).L₁.subgroupOf c.localActor).map a.action :=
      ⟨⟨x.val.val,hAX x.val.property⟩,x.val.property,rfl⟩
    have hcomm := (a.residual_centralizes hx t t.property).symm
    change MulAut.congr e (a.residualSylowAction P x) * MulAut.congr e t =
      MulAut.congr e t * MulAut.congr e (a.residualSylowAction P x)
    simpa only [map_mul] using congrArg (MulAut.congr e) hcomm)
  rw [← hPc]
  exact card_dvd_of_injective g (fun x y he => hf (congrArg Subtype.val he))

include hz hTV hTz hbound hH hn a in
/-- None of the five actual Mathieu models occurs in the original rank-two branch. -/
theorem SourceHypothesis.original_rank_two_not_mathieu
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) (name : ClassificationModels.SporadicName)
    (hname : name = .m11 ∨ name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24) :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃* name.Carrier) := by
  rintro ⟨e⟩
  let : Finite name.Carrier := Finite.of_equiv _ e.toEquiv
  rcases hname with rfl|rfl|rfl|rfl|rfl
  · obtain ⟨α,hα,_,h9⟩ := S.original_rank_two_model_centralizer D hZ z hz hTV hTz hbound hH hn c a hTI hns hr e
    exact Sporadic.Mathieu.m11_not_nine_dvd_involution_aut_centralizer α hα h9
  · obtain ⟨α,hα,⟨P,hP⟩,h9⟩ := S.original_rank_two_model_centralizer D hZ z hz hTV hTz hbound hH hn c a hTI hns hr e
    exact Sporadic.Mathieu.m12_not_nine_dvd_sylow_fixer_centralizer P α hα hP h9
  · obtain ⟨α,hα,⟨P,hP⟩,h9⟩ := S.original_rank_two_model_centralizer D hZ z hz hTV hTz hbound hH hn c a hTI hns hr e
    exact Sporadic.Mathieu.m22_not_nine_dvd_sylow_fixer_centralizer P α hα hP h9
  · obtain ⟨α,hα,_,h9⟩ := S.original_rank_two_model_centralizer D hZ z hz hTV hTz hbound hH hn c a hTI hns hr e
    exact Sporadic.Mathieu.m23_not_nine_dvd_involution_aut_centralizer α hα h9
  · obtain ⟨α,hα,⟨P,hP⟩,h9⟩ := S.original_rank_two_model_centralizer D hZ z hz hTV hTz hbound hH hn c a hTI hns hr e
    exact Sporadic.Mathieu.m24_not_nine_dvd_sylow_fixer_centralizer P α hα hP h9

include c in
/-- The actual Janko-one order excludes cubic rank two. -/
theorem SourceHypothesis.original_rank_two_not_jankoOne
    (hr : primeRank 3 c.K = 2) :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃* Janko1.Model) := by
  rintro ⟨e⟩
  have hrB : primeRank 3 (Nonabelian.Setup.star H c.K) = 2 :=
    c.three_rank_eq_star.symm.trans hr
  have hl : primeRank 3 Janko1.Model ≤ 1 := primeRank_le_one_of_square_not_dvd
    (by rw [Janko1.card_model]; decide)
  rw [primeRank_equiv 3 e] at hrB
  omega

include hz hTV hTz hbound hH hn a in
/-- The original sporadic alternative now retains only J2, J4, HS, He and Ru,
with a literal model equivalence for the same component. -/
theorem SourceHypothesis.original_rank_two_sporadic_restricted
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (Nonabelian.Setup.star H c.K)) :
    ∃ name : ClassificationModels.SporadicName,
      (name = .j2 ∨ name = .j4 ∨ name = .hs ∨ name = .he ∨ name = .ru) ∧
      Nonempty (Nonabelian.Setup.star H c.K ≃* name.Carrier) := by
  rcases hm with ⟨name,hname,he⟩|he
  · have hnmath := S.original_rank_two_not_mathieu D hZ z hz hTV hTz hbound hH hn c a hTI hns hr name
    cases name with
    | m11 => exact (hnmath (Or.inl rfl) he).elim
    | m12 => exact (hnmath (Or.inr (Or.inl rfl)) he).elim
    | m22 => exact (hnmath (Or.inr (Or.inr (Or.inl rfl))) he).elim
    | m23 => exact (hnmath (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) he).elim
    | m24 => exact (hnmath (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) he).elim
    | j3 => exact (hname rfl).elim
    | j2 => exact ⟨.j2,Or.inl rfl,he⟩
    | j4 => exact ⟨.j4,Or.inr (Or.inl rfl),he⟩
    | hs => exact ⟨.hs,Or.inr (Or.inr (Or.inl rfl)),he⟩
    | he => exact ⟨.he,Or.inr (Or.inr (Or.inr (Or.inl rfl))),he⟩
    | ru => exact ⟨.ru,Or.inr (Or.inr (Or.inr (Or.inr rfl))),he⟩
  · exact (S.original_rank_two_not_jankoOne D hZ z c hr he).elim

end CFSG.Quasithin.Chapter12.Section06
