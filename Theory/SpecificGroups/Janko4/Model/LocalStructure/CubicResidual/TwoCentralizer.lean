module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CubicResidual.LocalControl
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CubicFusion
public import Theory.GroupTheory.InvolutionSylowBound
public import Theory.GroupTheory.OddKernelInvolutionCentralizer
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# Binary subgroups centralizing a cubic residual in J₄

The native simultaneous-centralizer residual contains the original cubic.
Its centralizer inside that simultaneous centralizer has order dividing six.
The marked involution centralizes the seed, so its centralizer in the full
seed centralizer has no subgroup of order four. The Sylow normalizer condition
therefore bounds every binary subgroup of the seed centralizer by order two.
Cubic fusion transports this bound to any prescribed cubic and its full
solvable residual. The cover version keeps the literal quotient map and
requires injectivity only on the binary subgroup being bounded.

Source: Aschbacher--Smith, 4.2.13, printed p.612. The application compares
sixteen cubic-fixed exterior vectors with this bound. The imported native
J₄ matrices and certificates retain their ATLAS attribution and license.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

private theorem two_subgroup_card_bound {G : Type*} [Group G] [Finite G]
    (u : G) (hu : orderOf u = 2)
    (hc : ¬ 4 ∣ Nat.card (centralizer ({u} : Set G)))
    (P : Subgroup G) (hP : IsPGroup 2 P) : Nat.card P ≤ 2 := by
  have hz : IsPGroup 2 (zpowers u) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hu,pow_one])
  obtain ⟨S,hS⟩ := hz.exists_le_sylow
  let t : S := ⟨u,hS (mem_zpowers u)⟩
  let C := centralizer ({t} : Set S)
  have hcard : Nat.card C = 2 := by
    obtain ⟨n,hn⟩ := (S.isPGroup'.to_subgroup C).exists_card_eq
    have hnot : ¬ 4 ∣ Nat.card C := by
      intro hd
      exact hc (hd.trans (card_dvd_of_injective ((S : Subgroup G).subtype.elementCentralizerMap t)
        (fun a b he => Subtype.ext (Subtype.ext (congrArg (fun c : centralizer ({u} : Set G) => (c : G)) he)))))
    have htC : t ∈ C := mem_centralizer_singleton_iff.mpr rfl
    have hd : 2 ∣ Nat.card C := by
      have he : orderOf (⟨t,htC⟩ : C) = 2 :=
        (orderOf_coe _).symm.trans ((orderOf_coe t).symm.trans hu)
      simpa only [he] using orderOf_dvd_natCard (⟨t,htC⟩ : C)
    have hnlt : n < 2 := by
      by_contra h
      exact hnot (hn ▸ pow_dvd_pow 2 (by omega : 2 ≤ n))
    interval_cases n
    · norm_num at hn
      rw [hn] at hd
      norm_num at hd
    · simpa only [pow_one] using hn
  have hct : C ≤ zpowers t := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) ?_).ge
    rw [Nat.card_zpowers,←orderOf_coe t]
    exact hcard.le.trans_eq hu.symm
  have hSmall := card_le_two_of_self_centralizing_involution t
    ((orderOf_coe t).symm.trans hu) hct (⊤ : Subgroup S)
    (S.isPGroup'.to_subgroup ⊤)
  have hSc : Nat.card S ≤ 2 :=
    (Nat.card_congr (topEquiv : (⊤ : Subgroup S) ≃* S).toEquiv).symm.le.trans hSmall
  obtain ⟨n,hn⟩ := hP.exists_card_eq
  have hd : Nat.card P ∣ Nat.card S := hn ▸ S.pow_dvd_card_of_pow_dvd_card
    (hn ▸ P.card_subgroup_dvd_card)
  exact (Nat.le_of_dvd (Nat.card_pos) hd).trans hSc

namespace Janko4.InvolutionCentralizers.First.CubicResidual
open OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreLinearModel TwoCoreComparison QuotientExtension Sporadic.Mathieu
attribute [local irreducible] modelGroup matrixA matrixB involutionCentralizer involutionTwoCore
  actionGroup derivedGroup scalarUnit

private theorem scalar_residual_two_centralizer_bound
    (x : centralizer) (hx : orderOf x = 3)
    (hs : centralizerExtension.rightHom x = scalarElement)
    (P : Subgroup Model) (hP : IsPGroup 2 P)
    (hPC : P ≤ Subgroup.centralizer
      ((solvableResidual (Subgroup.centralizer ({(x : Model)} : Set Model))).map
        (Subgroup.centralizer ({(x : Model)} : Set Model)).subtype : Set Model)) :
    Nat.card P ≤ 2 := by
  let D := Subgroup.centralizer ({x} : Set centralizer)
  let S := solvableResidual D
  let f : D →* Model := centralizer.subtype.comp D.subtype
  let B := S.map f
  let Z := Subgroup.centralizer (B : Set Model)
  have hBfull : B ≤ (solvableResidual (Subgroup.centralizer ({(x : Model)} : Set Model))).map
      (Subgroup.centralizer ({(x : Model)} : Set Model)).subtype := by
    rintro b ⟨d,hd,rfl⟩
    exact mem_map_of_mem (Subgroup.centralizer ({(x : Model)} : Set Model)).subtype
      (map_solvableResidual_le (centralizer.subtype.elementCentralizerMap x)
        (mem_map_of_mem (centralizer.subtype.elementCentralizerMap x) hd))
  have haZ : a ∈ Z := by
    rintro y ⟨y,hy,rfl⟩
    exact mem_centralizer_singleton_iff.mp y.val.property
  let t : Z := ⟨a,haZ⟩
  have ht : orderOf t = 2 := (orderOf_coe t).symm.trans orderOf_a
  have hxb : (x : Model) ∈ B := mem_map_of_mem f (scalar_lift_mem_residual x hx hs)
  let C := Subgroup.centralizer ({t} : Set Z)
  let j : C →* Subgroup.centralizer (S : Set D) := {
    toFun c := ⟨⟨⟨c.val.val,mem_centralizer_singleton_iff.mpr
      (congrArg Z.subtype (mem_centralizer_singleton_iff.mp c.property))⟩,
      mem_centralizer_singleton_iff.mpr (Subtype.ext (c.val.property (x : Model) hxb).symm)⟩,
      fun y hy => Subtype.ext (Subtype.ext (c.val.property (f y) (mem_map_of_mem f hy)))⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro c d he
    exact Subtype.ext (Subtype.ext (congrArg
      (fun z : Subgroup.centralizer (S : Set D) => (z.val.val : Model)) he))
  have hnot : ¬ 4 ∣ Nat.card C := by
    intro hd
    exact (by decide : ¬ 4 ∣ 6) ((hd.trans (card_dvd_of_injective j hj)).trans
      (scalar_centralizer_residual_centralizer_card x hx hs))
  have hPZ : P ≤ Z := hPC.trans (centralizer_le hBfull)
  have hb := two_subgroup_card_bound t ht hnot (P.subgroupOf Z) hP.comap_subtype
  rwa [Nat.card_congr (subgroupOfEquivOfLe hPZ).toEquiv] at hb

end Janko4.InvolutionCentralizers.First.CubicResidual

namespace Janko4.LocalStructure
attribute [local irreducible] modelGroup matrixA matrixB

/-- Binary subgroups centralizing the full residual at any prescribed cubic
have order at most two. The cubic and the full residual are literal. -/
theorem cubic_residual_two_centralizer_bound
    (x : Model) (hx : orderOf x = 3) (P : Subgroup Model) (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer
      ((solvableResidual (centralizer ({x} : Set Model))).map
        (centralizer ({x} : Set Model)).subtype : Set Model)) : Nat.card P ≤ 2 := by
  obtain ⟨y,hy,hs⟩ := InvolutionCentralizers.First.CubicResidual.exists_scalar_lift
  obtain ⟨g,hg⟩ := cubic_cyclic_fusion (MonoidHom.id Model) Function.surjective_id
    (by simp) x (y : Model) hx ((orderOf_coe y).trans hy)
  let α := MulAut.conj g
  let C := centralizer ({x} : Set Model)
  let D := centralizer ({(y : Model)} : Set Model)
  have hC : C.map α.toMonoidHom = D := by
    change (centralizer ({x} : Set Model)).map α.toMonoidHom = D
    rw [←centralizer_closure,←zpowers_eq_closure,map_centralizer_equiv]
    change centralizer ((zpowers x).map α.toMonoidHom : Set Model) = _
    rw [hg,zpowers_eq_closure,centralizer_closure]
  let c : C ≃* D := (α.subgroupMap C).trans (MulEquiv.subgroupCongr hC)
  have hR : (solvableResidual D).map D.subtype =
      ((solvableResidual C).map C.subtype).map α.toMonoidHom := by
    rw [←map_solvableResidual_eq c.toMonoidHom c.surjective,Subgroup.map_map,
      Subgroup.map_map]
    rfl
  have hPc : P.map α.toMonoidHom ≤ centralizer
      ((solvableResidual D).map D.subtype : Set Model) := by
    rintro p ⟨p,hp,rfl⟩ z hz
    rw [hR] at hz
    obtain ⟨w,hw,rfl⟩ := hz
    exact (map_mul α w p).symm.trans
      ((congrArg α (hPC hp w hw)).trans (map_mul α p w))
  have hb := InvolutionCentralizers.First.CubicResidual.scalar_residual_two_centralizer_bound
    y hy hs (P.map α.toMonoidHom) (hP.map _) hPc
  rwa [card_map_of_injective α.injective] at hb
end Janko4.LocalStructure

namespace Janko4.LocalStructure
attribute [local irreducible] modelGroup matrixA matrixB

/-- The bound retains a specified cover and its quotient map. Only the
binary subgroup under consideration must inject into the J₄ quotient. -/
theorem cover_cubic_residual_two_centralizer_bound
    {U : Type*} [Group U] [Finite U]
    (q : U →* Model) (hq : Function.Surjective q)
    (hthree : Nat.Coprime 3 (Nat.card q.ker)) (x : U) (hx : orderOf x = 3)
    (P : Subgroup U) (hP : IsPGroup 2 P)
    (hi : Function.Injective (q.comp P.subtype))
    (hPC : P ≤ centralizer ((solvableResidual (centralizer ({x} : Set U))).map
      (centralizer ({x} : Set U)).subtype : Set U)) : Nat.card P ≤ 2 := by
  let C := centralizer ({x} : Set U)
  let D := centralizer ({q x} : Set Model)
  have hxp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hx,pow_one])
  have hxi := injective_comp_subtype_of_coprime_ker q hthree (zpowers x) hxp
  have hqx : orderOf (q x) = 3 :=
    (orderOf_injective (q.comp (zpowers x).subtype) hxi ⟨x,mem_zpowers x⟩).trans
      ((orderOf_coe (⟨x,mem_zpowers x⟩ : zpowers x)).symm.trans hx)
  have hCD : C.map q = D := by
    have hh := centralizer_map_of_prime_free_kernel q hq
      (Nat.prime_three.coprime_iff_not_dvd.mp hthree) (zpowers x) hxp
    rw [MonoidHom.map_zpowers,zpowers_eq_closure,centralizer_closure,
      zpowers_eq_closure,centralizer_closure] at hh
    exact hh
  have hs : Function.Surjective (q.elementCentralizerMap x) := by
    intro y
    obtain ⟨c,hc,he⟩ := hCD.symm ▸ (show (y : Model) ∈ D from y.property)
    exact ⟨⟨c,hc⟩,Subtype.ext he⟩
  have hR : ((solvableResidual C).map C.subtype).map q =
      (solvableResidual D).map D.subtype := by
    rw [←map_solvableResidual_eq (q.elementCentralizerMap x) hs,
      Subgroup.map_map,Subgroup.map_map]
    rfl
  have hPc : P.map q ≤ centralizer ((solvableResidual D).map D.subtype : Set Model) := by
    rintro p ⟨p,hp,rfl⟩ z hz
    rw [←hR] at hz
    obtain ⟨w,hw,rfl⟩ := hz
    exact (map_mul q w p).symm.trans ((congrArg q (hPC hp w hw)).trans (map_mul q p w))
  have hb := cubic_residual_two_centralizer_bound (q x) hqx (P.map q) (hP.map q) hPc
  have he : P ≃* P.map q := (MonoidHom.ofInjective hi).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp,range_subtype]))
  exact (Nat.card_congr he.toEquiv).trans_le hb
end Janko4.LocalStructure
