module
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.GroupAction.CentralKernelFixedComponents
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoFour
public import Theory.Mathieu.InvolutoryTwoComponents
public import Theory.Mathieu.M24.Properties.InvolutionFixedOrders
public import Theory.SpecificGroups.Rudvalis.ComponentFacts
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.ThreePart
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.HeldBounds
public import Theory.SpecificGroups.Janko3.Model.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.SymplecticSix.OrderRank

/-!
# Finite model exclusions for an involution fixing a Mathieu component

A component covering M₂₂ forces |M₂₂| to divide the fixed-group order. This excludes alternating degree at most nine, PSL₄(2), PSL₅(2),
PSp₆(2), M₁₁, M₁₂, J₁, J₂, J₃ and He by their actual orders. An automorphism
of M₂₂ fixing an M₂₂ cover would fix the whole group. The full involutory
fixed groups of M₂₃ and J₄ have no ordinary components; those of M₂₄ and Ru
have orders not divisible by nine. All automorphisms, component embeddings and
central quotients are transported through genuine group equivalences.

The resulting Theorem B list retains its Lie families, HS and McL. This
is a partial model inspection, not the full p.612 equality assertion.
The exterior application is Hall.OddNormalizer.PushingUpProperModels.
Source: Aschbacher--Smith 4.2.13, printed p.612, Theorem B, p.33, and
GLS III, Tables 5.3a--i,p,r. The imported model certificates retain their
individual source references and licenses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.MathieuPumpup
open Sporadic.Mathieu

@[expose] def HasMathieuFixedComponent (S : Type*) [Group S] : Prop :=
  ∃ a : MulAut S, orderOf a = 2 ∧ ∃ B : Subgroup S,
    IsComponentIn B a.fixedSubgroup ∧ Nonempty ((B ⧸ center B) ≃* M22)

variable {S U : Type*} [Group S] [Group U]

theorem HasMathieuFixedComponent.of_mulEquiv (h : HasMathieuFixedComponent S) (e : S ≃* U) :
    HasMathieuFixedComponent U := by
  obtain ⟨a,ha,B,hB,⟨b⟩⟩ := h
  let a' := MulAut.congr e a
  refine ⟨a',(MulAut.congr e).orderOf_eq a |>.trans ha,B.map e.toMonoidHom,?_,?_⟩
  · exact hB.map_fixed_of_central_ker a a' e.toMonoidHom e.surjective
      (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact bot_le)
      (fun x => by change e (a x) = e (a (e.symm (e x))); rw [e.symm_apply_apply])
      (fun hb => hB.ne_bot ((map_eq_bot_iff_of_injective B e.injective).mp hb))
  · let c := e.subgroupMap B
    let q : (B ⧸ center B) ≃* ((B.map e.toMonoidHom) ⧸ center (B.map e.toMonoidHom)) :=
      QuotientGroup.congr _ _ c (by
        apply le_antisymm
        · rintro _ ⟨z,hz,rfl⟩
          exact (centerCongr c ⟨z,hz⟩).property
        · intro y hy
          exact ⟨c.symm y,(centerCongr c.symm ⟨y,hy⟩).property,c.apply_symm_apply y⟩)
    exact ⟨q.symm.trans b⟩

private theorem mathieu_card_dvd {B : Subgroup S}
    (b : (B ⧸ center B) ≃* M22) : 443520 ∣ Nat.card B := by
  rw [←m22_order,←Nat.card_congr b.toEquiv]
  exact card_quotient_dvd_card _

theorem HasMathieuFixedComponent.card_dvd (h : HasMathieuFixedComponent S) :
    443520 ∣ Nat.card S := by
  obtain ⟨a,ha,B,hB,⟨b⟩⟩ := h
  exact (mathieu_card_dvd b).trans B.card_subgroup_dvd_card

private theorem fixed_dvd {a : MulAut S} {B : Subgroup S}
    (hB : IsComponentIn B a.fixedSubgroup) (b : (B ⧸ center B) ≃* M22) :
    443520 ∣ Nat.card a.fixedSubgroup :=
  (mathieu_card_dvd b).trans (card_dvd_of_le hB.1)

private theorem no_card_model (h : HasMathieuFixedComponent S)
    (e : S ≃* U) (hc : ¬ 443520 ∣ Nat.card U) : False :=
  hc (Nat.card_congr e.toEquiv ▸ h.card_dvd)

private theorem fixed_card_lt [Finite S] (a : MulAut S) (ha : orderOf a = 2) :
    Nat.card a.fixedSubgroup < Nat.card S := by
  have hne : a.fixedSubgroup ≠ ⊤ := by
    intro hh
    have he : a = 1 := by
      ext x
      exact (MulAut.mem_fixedSubgroup a x).mp (hh ▸ mem_top x)
    rw [he,orderOf_one] at ha
    omega
  exact Set.ncard_lt_card (show (a.fixedSubgroup : Set S) ≠ Set.univ from
    fun hh => hne (SetLike.coe_injective hh))

theorem no_mathieu_self_fixed : ¬ HasMathieuFixedComponent M22 := by
  rintro ⟨a,ha,B,hB,⟨b⟩⟩
  have hd := Nat.le_of_dvd (Nat.card_pos (α := a.fixedSubgroup)) (fixed_dvd hB b)
  have hl := fixed_card_lt a ha
  rw [m22_order] at hl
  omega

theorem HasMathieuFixedComponent.not_alternating (h : HasMathieuFixedComponent S)
    (n : ℕ) (hn : n ≤ 9) (e : S ≃* alternatingGroup (Fin n)) : False := by
  have hd := (h.of_mulEquiv e).card_dvd.trans
    (alternatingGroup (Fin n)).card_subgroup_dvd_card
  have hc : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
    simp [Nat.card_eq_fintype_card,Fintype.card_perm]
  rw [hc] at hd
  interval_cases n <;> norm_num [Nat.factorial] at hd

theorem HasMathieuFixedComponent.not_linear_binary (h : HasMathieuFixedComponent S)
    (n : ℕ) (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL S n 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hd := (h.of_mulEquiv e).card_dvd
  let : NeZero n := ⟨by rcases hn with rfl | rfl <;> decide⟩
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) n
  rcases hn with rfl | rfl <;>
    norm_num [hF,Fin.prod_univ_succ] at hc <;> rw [hc] at hd <;> norm_num at hd

theorem HasMathieuFixedComponent.not_symplectic_binary (h : HasMathieuFixedComponent S)
    (hm : ClassicalGroup.IsPSp S 3 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hd := (h.of_mulEquiv e).card_dvd.trans (card_quotient_dvd_card _)
  change 443520 ∣ Nat.card (Theory.SpecificGroups.SymplecticSix.Sp F) at hd
  rw [Theory.SpecificGroups.SymplecticSix.card_sp_of_card_two hF] at hd
  norm_num at hd

theorem no_mathieu_fixed_m23 : ¬ HasMathieuFixedComponent M23 := by
  rintro ⟨a,ha,B,hB,_⟩
  exact M23Geometry.InvolutionCentralizer.fixedSubgroup_no_component_of_inner a ha
    (m23_involution_automorphism_inner a ha) _ hB.2

theorem no_mathieu_fixed_m24 : ¬ HasMathieuFixedComponent M24 := by
  rintro ⟨a,ha,B,hB,⟨b⟩⟩
  exact m24_involution_not_nine_dvd_fixed_card a ha
    ((by decide : 9 ∣ 443520).trans (fixed_dvd hB b))

theorem no_mathieu_fixed_j4 [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model] :
    ¬ HasMathieuFixedComponent Janko4.Model := by
  rintro ⟨a,ha,B,hB,_⟩
  exact Chapter16.OtherPreliminaries.JankoFour.involution_fixed_no_componentIn a ha B hB

theorem no_mathieu_fixed_ru [IsSimpleGroup Rudvalis.Model] [Group.IsPerfect Rudvalis.Model] :
    ¬ HasMathieuFixedComponent Rudvalis.Model := by
  rintro ⟨a,ha,B,hB,⟨b⟩⟩
  obtain ⟨x,hx,rfl,hfix⟩ := MulAut.inner_involution_representative
    (center_eq_bot_of_simple_perfect (G := Rudvalis.Model)) a ha
    (by obtain ⟨x,hx⟩ := Rudvalis.component_conj_surjective a; exact ⟨x,hx.symm⟩)
  have hd := (by decide : 9 ∣ 443520).trans (fixed_dvd hB b)
  rw [hfix] at hd
  exact Rudvalis.InvolutionCentralizers.centralizer_not_nine x hx hd

open ClassificationModels ChapterA.Section02

/-- Only HS and McL remain among the finite sporadic containing components. -/
theorem HasMathieuFixedComponent.sporadic_rows [IsSimpleGroup S] [Group.IsPerfect S]
    (h : HasMathieuFixedComponent S) (hm : IsTheoremBSporadicModel S) :
    Nonempty (S ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (S ≃* Sporadic.LeechRelated.McL.Carrier) := by
  change IsSporadicModel S ∨ Nonempty (S ≃* Janko1.Model) ∨
    Nonempty (S ≃* Sporadic.LeechRelated.McL.Carrier) at hm
  rcases hm with ⟨name,⟨e⟩⟩ | hj | he
  · cases name with
    | m11 => exact (no_card_model h e (by change ¬ 443520 ∣ Nat.card M11; rw [m11_order]; decide)).elim
    | m12 => exact (no_card_model h e (by change ¬ 443520 ∣ Nat.card M12; rw [m12_order]; decide)).elim
    | m22 => exact (no_mathieu_self_fixed (h.of_mulEquiv e)).elim
    | m23 => exact (no_mathieu_fixed_m23 (h.of_mulEquiv e)).elim
    | m24 => exact (no_mathieu_fixed_m24 (h.of_mulEquiv e)).elim
    | j2 => exact (no_card_model h e (by
        change ¬ 443520 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier
        rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
        decide)).elim
    | j3 => exact (no_card_model h e (by change ¬ 443520 ∣ Nat.card Sporadic.Janko3.Model; rw [Sporadic.Janko3.model_card]; decide)).elim
    | j4 =>
      change S ≃* Janko4.Model at e
      let : IsSimpleGroup Janko4.Model := e.symm.isSimpleGroup
      let : Group.IsPerfect Janko4.Model := Group.IsPerfect.ofSurjective
        (f := e.toMonoidHom) e.surjective
      exact (no_mathieu_fixed_j4 (h.of_mulEquiv e)).elim
    | hs => exact Or.inl ⟨e⟩
    | he =>
      have hd := (h.of_mulEquiv e).card_dvd.trans Held.OddPrimary.card_dvd
      norm_num at hd
    | ru =>
      change S ≃* Rudvalis.Model at e
      let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
      let : Group.IsPerfect Rudvalis.Model := Group.IsPerfect.ofSurjective
        (f := e.toMonoidHom) e.surjective
      exact (no_mathieu_fixed_ru (h.of_mulEquiv e)).elim
  · obtain ⟨e⟩ := hj
    exact (no_card_model h e (by rw [Janko1.card_model]; decide)).elim
  · exact Or.inr he

/-- The exact rows still requiring involution-component exclusion. -/
@[expose] def RemainingMathieuOvercomponentModel (S : Type*) [Group S] : Prop :=
  IsTheoremBOddModel S ∨ IsBenderModel S ∨
    (∃ n, IsRankTwoModel S n) ∨
    Nonempty (S ≃* Sporadic.LeechRelated.HS.Carrier) ∨
    Nonempty (S ≃* Sporadic.LeechRelated.McL.Carrier)

/-- Exclude B(1), B(4), and eleven sporadic B(5) overcomponent rows. -/
theorem HasMathieuFixedComponent.theoremB_rows [IsSimpleGroup S] [Group.IsPerfect S]
    (h : HasMathieuFixedComponent S) (hm : IsTheoremBModel S) :
    RemainingMathieuOvercomponentModel S := by
  cases hm with
  | alternating n hn he => exact (h.not_alternating n hn he.some).elim
  | odd ho => exact Or.inl ho
  | bender hb => exact Or.inr (Or.inl hb)
  | rank_two n hr => exact Or.inr (Or.inr (Or.inl ⟨n,hr⟩))
  | linear_binary n hn hl => exact (h.not_linear_binary n hn hl).elim
  | symplectic_binary hs => exact (h.not_symplectic_binary hs).elim
  | sporadic hs => exact Or.inr (Or.inr (Or.inr (h.sporadic_rows hs)))

end CFSG.Quasithin.ChapterI.MathieuPumpup
