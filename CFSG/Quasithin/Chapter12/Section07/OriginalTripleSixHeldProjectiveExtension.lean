module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldComponentNormalizer
public import Theory.GroupAction.ComponentRankAction
public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure
import Theory.GroupTheory.PResidual.FiniteLocalPair
import Theory.GroupTheory.PResidual.Quotient

/-!
# The actual projective extension of the original point component

The literal B X acts on B/Z(B), with kernel the original Vt. Its image
contains every inner automorphism. The two-perfect scalar residual maps
trivially into Aut(PSL3(4))/PGL3(4), a two-group. Its nontrivial action on
the covering center rules out an inner image. The diagonal index divides
three, so the image is exactly PGL3(4), with the quotient action retained.

Source: Aschbacher--Smith12.7.7, first paragraph printed p.841.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
open Matrix.PSL3.OuterSolvable Matrix.PSL3Four.OuterThreeStructure
open Theory.GroupAction.ComponentRankAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The genuine PGL3(4) quotient of the original B X, with its exact kernel
and its original action on the marked central quotient of B. -/
theorem original_tripleSix_held_projective_extension
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hB : let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      IsComponent H ((conjugateSpanBy Lt H).subgroupOf H))
    (hcenter :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      centerIn (conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))) = tripleSixPoint D a t)
    (e :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
      B ⧸ center B ≃* Matrix.PSL3Four.PSL) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    let X := tripleSixScalarResidual K
    let W := B ⊔ X
    ∃ hWN : W ≤ normalizer (B : Set G),
      ∃ f : W →* Matrix.ProjGenLinGroup (Fin 3) Matrix.PSL3Four.F,
        Function.Surjective f ∧ f.ker = (tripleSixPoint D a t).subgroupOf W ∧
        ∀ w : W, (pglEquiv (f w)).val = action B e (inclusion hWN w) := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  let X := tripleSixScalarResidual K
  let W := B ⊔ X
  let Vt := tripleSixPoint D a t
  obtain ⟨hCB,_,_,hXN⟩ := original_tripleSix_held_component_normalizer
    h structural D a t ht heven hB hcenter e
  have hWN : W ≤ normalizer (B : Set G) := sup_le B.le_normalizer hXN
  have hVB : Vt ≤ B := by
    rw [show Vt = centerIn B from hcenter.symm]
    exact inf_le_left
  have hBW : B ≤ W := le_sup_left
  let : Group.IsPerfect Lt := tripleSixPointCentralizerResidual_perfect D a t ht heven
  let : Group.IsPerfect B := conjugateSpanBy_isPerfect Lt H
  let ρ := (action B e).comp (inclusion hWN)
  have hker : ρ.ker = Vt.subgroupOf W := by
    rw [show ρ = (action B e).comp (inclusion hWN) from rfl,
      ←MonoidHom.comap_ker,ker_eq,hCB]
    rfl
  let A := ρ.range
  let I := MulAut.innerSubgroup Matrix.PSL3Four.PSL
  let J := innerDiagonal Matrix.PSL3Four.F
  have hIA : I ≤ A := by
    rintro _ ⟨s,rfl⟩
    obtain ⟨b,hb⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (center B))) s
    refine ⟨⟨b,hBW b.property⟩,?_⟩
    change action B e ⟨b,_⟩ = MulAut.conj s
    rw [action_on_component]
    exact congrArg MulAut.conj hb
  have hJn : J.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← standard_eq_top_of_two_power_card Matrix.PSL3Four.F (m := 2)
      (by decide) (by simpa using Matrix.PSL3Four.card_F)]
    exact standard_le_normalizer_innerDiagonal
  let := hJn
  have hJtwo : IsPGroup 2 ((MulAut Matrix.PSL3Four.PSL) ⧸ J) :=
    IsPGroup.of_card_dvd_pow (n := 2) diagonal_index_dvd_four
  have hXp : IsPPerfect 2 X := by
    let Z := centralPreimage (pCore 2 K)
    let R := (pResidual 2 Z).map Z.subtype
    let ex := R.equivMapOfInjective K.subtype K.subtype_injective
    exact (isPPerfect_embedded_pResidual_of_finite 2 Z).of_surjective ex.toMonoidHom ex.surjective
  have hXJ : (X.subgroupOf W).map ρ ≤ J := by
    let j := (QuotientGroup.mk' J).comp (ρ.comp (inclusion (show X ≤ W from le_sup_right)))
    have hh := pResidual_le_ker_of_isPGroup 2 j hJtwo
    rw [(pResidual_eq_top_iff 2 X).mpr hXp] at hh
    rintro _ ⟨x,hx,rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    have hhx : j (⟨(x : G),hx⟩ : X) = 1 := hh (mem_top _)
    change QuotientGroup.mk' J (ρ (⟨x.val,_⟩ : W)) = 1 at hhx
    exact hhx
  have hBJ : (B.subgroupOf W).map ρ ≤ J := by
    rintro _ ⟨b,hb,rfl⟩
    apply inner_le_innerDiagonal Matrix.PSL3Four.F
    refine ⟨e (QuotientGroup.mk' (center B) ⟨b,hb⟩),?_⟩
    exact (action_on_component B e ⟨b,hb⟩).symm
  have hAJ : A ≤ J := by
    have he : B.subgroupOf W ⊔ X.subgroupOf W = ⊤ := by
      rw [←subgroupOf_sup (show B ≤ W from le_sup_left)
        (show X ≤ W from le_sup_right),subgroupOf_self]
    rw [show A = ρ.range from rfl,MonoidHom.range_eq_map,←he,Subgroup.map_sup]
    exact sup_le hBJ hXJ
  have hne : A ≠ I := by
    intro he
    have htX : (t : G) ∈ centralizer (X : Set G) := by
      intro x hx
      let xW : W := ⟨x,(show X ≤ W from le_sup_right) hx⟩
      have hxI : ρ xW ∈ I := he ▸ (show ρ xW ∈ A from ⟨xW,rfl⟩)
      obtain ⟨s,hs⟩ := hxI
      let ax := B.normalizerMonoidHom ⟨x,hXN hx⟩
      have ha : ∃ b : B, ax = MulAut.conj b :=
        (MulAut.centralQuotientAction_inner_iff e ax).mp ⟨s,hs.symm⟩
      obtain ⟨b,hb⟩ := ha
      have htV : (t:G) ∈ Vt := (tripleSixPoint_properties D a t ht).1
      let tb : B := ⟨t,hVB htV⟩
      have htcenter : tb ∈ center B := by
        have hh : (t:G) ∈ centerIn B := hcenter.symm ▸ htV
        exact (mem_center_iff.mpr (fun y => Subtype.ext (hh.2 y y.property)))
      have hfix := congrArg (fun α : MulAut B => (α tb : G)) hb
      change x*(t:G)*x⁻¹ = (b:G)*(t:G)*(b:G)⁻¹ at hfix
      have hcomm : (b:G)*(t:G)=(t:G)*(b:G) :=
        congrArg Subtype.val (mem_center_iff.mp htcenter b)
      rw [hcomm,mul_inv_cancel_right] at hfix
      exact (mul_inv_eq_iff_eq_mul.mp hfix)
    have htbot : (t:G) ∈ (⊥ : Subgroup G) :=
      (tripleSixScalarResidual_fixed_eq_bot D a) ▸ (show (t:G) ∈ U ⊓ centralizer (X:Set G) from
        ⟨t.property,htX⟩)
    exact ht (Subtype.ext htbot)
  have hfull : A = J := by
    have hd : I.relIndex J ∣ 3 := inner_relIndex_diagonal_dvd_three
    have hm := relIndex_mul_relIndex I A J hIA hAJ
    have hsmall : I.relIndex A * A.relIndex J ≤ 3 := by
      rw [hm]
      exact Nat.le_of_dvd (by decide) hd
    have hi : 0 < I.relIndex A := Nat.card_pos
    have hj : 0 < A.relIndex J := Nat.card_pos
    have hi1 : I.relIndex A ≠ 1 := by
      intro hh
      exact hne (le_antisymm (relIndex_eq_one.mp hh) hIA)
    have hi2 : 2 ≤ I.relIndex A := by omega
    have hj1 : A.relIndex J = 1 := by nlinarith
    exact le_antisymm hAJ (relIndex_eq_one.mp hj1)
  let eqA : A ≃* Matrix.ProjGenLinGroup (Fin 3) Matrix.PSL3Four.F :=
    (MulEquiv.subgroupCongr hfull).trans pglEquiv.symm
  let f := eqA.toMonoidHom.comp ρ.rangeRestrict
  refine ⟨hWN,f,eqA.surjective.comp ρ.rangeRestrict_surjective,?_,?_⟩
  · rw [show f = eqA.toMonoidHom.comp ρ.rangeRestrict from rfl,
      MonoidHom.ker_comp_of_injective _ _ eqA.injective,MonoidHom.ker_rangeRestrict,hker]
  · intro w
    change (pglEquiv (pglEquiv.symm ((MulEquiv.subgroupCongr hfull) (ρ.rangeRestrict w)))).val = _
    rw [pglEquiv.apply_symm_apply]
    rfl

end CFSG.Quasithin.Chapter12.Section07
