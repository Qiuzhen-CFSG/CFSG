module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.PointModel
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Solvable
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Nonsolvable
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.CoreAction
public import Theory.GroupTheory.WreathTwoThreeCore
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The original parabolic residual meets a three-free subgroup in its two-core

A minimal parabolic mapping onto O₄⁺(2) is solvable: the kernel lies in its
solvable parabolic core. B.6.8 makes its two-residual modulo O₂ a group of
one odd prime power order. The cubic point stabilizer forces that prime to
be three. A two-perfect subgroup consequently meets any three-free subgroup
inside O₂. The actual H-star consumer applies this to Y and H∩M.
Source: Aschbacher–Smith10.2.1, printed p.743, and B.6.8, pp.113–115.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open BinaryFourPlus ChapterB

private theorem wreath_solvable : Group.IsSolvable Wreath := by
  obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let e := RegularWreathProduct.congr eSL (MulEquiv.refl C2)
  have hp : IsPGroup 2 (Wreath ⧸ pCore 3 Wreath) :=
    Theory.GroupTheory.WreathTwoResidual.threeCore_quotient_two.of_equiv
      (QuotientGroup.congr _ _ e (pCore_map_iso 3 e))
  let : Group.IsNilpotent (Wreath ⧸ pCore 3 Wreath) := hp.isNilpotent
  let : Group.IsNilpotent (pCore 3 Wreath) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 3 Wreath)).mpr
    ⟨inferInstance,inferInstance⟩

variable {H : Type*} [Group H] [Finite H]

theorem parabolic_wreath_residual_isThreeGroup
    (S : Sylow 2 H) (hP : IsMinimalParabolicOver S ⊤)
    (f : H →* Wreath) (hf : Function.Surjective f) :
    IsPGroup 3 (pResidual 2 (H ⧸ pCore 2 H)) := by
  have hne : f.ker≠⊤ := by
    intro he
    have hz : ∀w:Wreath,w=1 := by
      intro w
      obtain ⟨h,rfl⟩ := hf w
      exact MonoidHom.mem_ker.mp (he ▸ mem_top h)
    have hc : Subsingleton Wreath := ⟨fun a b => (hz a).trans (hz b).symm⟩
    have hh := Nat.card_eq_one_iff_unique.mpr ⟨hc,inferInstance⟩
    have hcard : Nat.card Wreath=72 :=
      (Nat.card_congr isometryEquivWreath.toEquiv).symm.trans card_isometrySubgroup
    omega
  obtain ⟨hk,_⟩ := minimalParabolic_reduced_image S hP f hf twoCore_eq_bot hne
  let : Group.IsSolvable Wreath := wreath_solvable
  let : Group.IsSolvable (minimalParabolicCore S hP) := minimalParabolic_core_solvable S hP
  have hs : Group.IsSolvable H := Group.isSolvable_of_ker_le_range
    (minimalParabolicCore S hP).subtype f (by rwa [range_subtype])
  obtain ⟨p,hp,_,hr,_,_,_⟩ := minimalParabolic_solvable_structure S hP hs
  let : Fact p.Prime := ⟨hp⟩
  have hpcore : pCore 2 H≤f.ker := by
    have hn : ((pCore 2 H).map f).Normal := (inferInstance : (pCore 2 H).Normal).map f hf
    have hb : (pCore 2 H).map f≤pCore 2 Wreath := le_sSup ⟨hn,pCore_isPGroup.map f⟩
    apply (Subgroup.map_eq_bot_iff _).mp
    exact bot_unique (hb.trans twoCore_eq_bot.le)
  let fb : (H ⧸ pCore 2 H) →* Wreath := QuotientGroup.lift _ f hpcore
  have hfb : Function.Surjective fb := by
    intro w
    obtain ⟨h,rfl⟩ := hf w
    exact ⟨QuotientGroup.mk' _ h,rfl⟩
  have hpR : IsPGroup p (pResidual 2 Wreath) := by
    rw [←map_pResidual_of_surjective 2 fb hfb]
    have hpp : IsPGroup p (pResidual 2 (H⧸pCore 2 H)) := by
      rw [hr]
      exact pCore_isPGroup
    exact hpp.map fb
  let b : Plane := nonzeroVector 0
  have hb : b≠0 := by decide
  let C := pointStabilizer (0,b)
  have hsmall : IsPGroup p (pResidual 2 C) :=
    (hpR.to_le (map_pResidual_le 2 C.subtype)).of_equiv
      ((pResidual 2 C).equivMapOfInjective C.subtype C.subtype_injective).symm
  have hd : p∣3 := by
    have hh := hsmall.card_eq_or_dvd
    rw [point_stabilizer_residual_card b hb] at hh
    exact hh.resolve_left (by decide)
  have he : p=3 := ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd).resolve_left hp.ne_one
  subst p
  rw [hr]
  exact pCore_isPGroup

theorem parabolic_wreath_twoPerfect_inf_threeFree_le_core
    (S : Sylow 2 H) (hP : IsMinimalParabolicOver S ⊤)
    (f : H →* Wreath) (hf : Function.Surjective f)
    (Y M : Subgroup H) (hY : IsPPerfect 2 Y)
    (hM : Nat.Coprime 3 (Nat.card M)) : Y ⊓ M≤pCore 2 H := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hYq : IsPGroup 3 (Y.map q) :=
    (parabolic_wreath_residual_isThreeGroup S hP f hf).to_le
      ((map_mono (le_pResidual_of_isPPerfect Y hY)).trans
        (map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)).le)
  obtain ⟨n,hn⟩ := hYq.exists_card_eq
  have hc : Nat.Coprime (Nat.card (Y.map q)) (Nat.card (M.map q)) := by
    rw [hn]
    exact (hM.coprime_dvd_right (card_map_dvd M q)).pow_left n
  have hd : Disjoint (Y.map q) (M.map q) := disjoint_of_coprime_natCard hc
  intro y hy
  apply (QuotientGroup.eq_one_iff y).mp
  exact mem_bot.mp (hd.le_bot ⟨mem_map_of_mem q hy.1,mem_map_of_mem q hy.2⟩)

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
