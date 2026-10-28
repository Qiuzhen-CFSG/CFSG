module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.CentralFusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.WeakClosure
public import Theory.GroupTheory.WeakClosureSetFusion
public import Mathlib.Data.Set.Card.Arithmetic

/-!
# The q+1 central lines in each original root plane

Weak closure of the root plane and Burnside set fusion move any ambient
conjugate of Z(S) inside that plane by its full normalizer. The actual
normalizer factorization removes the common-overlap component, leaving
a conjugator in the original affine factor. Its centralizer calculation
identifies each such line with the center of the centralizer of any
nonzero point on it. Thus distinct lines meet only at the identity, and
affine transitivity partitions the nonzero plane into q+1 lines.

These are the original source groups and both amalgam orientations; q=4
is included. This proves §5.3.6(2), without ambient recognition or an
assumed full-normalizer realization.
Source: Aschbacher–Smith, printed p.660 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
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
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax

/-- Each central-line conjugate contained in a root plane is already conjugate
under the original affine factor. This is the orbit equality of §5.3.6(2). -/
theorem Preparation.linear_root_line_fusion (i : Fin 2) (g : G)
    (hg : (centerIn (sourceS L H)).conjBy g ≤ (![L,residual H] i).pCoreIn 2) :
    ∃ a ∈ ![L,residual H] i,
      (centerIn (sourceS L H)).conjBy a = (centerIn (sourceS L H)).conjBy g := by
  let Z := centerIn (sourceS L H)
  let V := (![L,residual H] i).pCoreIn 2
  have hc := (d.linear_core_structure h hH hp F hm hF he).2.2
  let : IsElementaryAbelian 2 V := (hc i).1
  have hZV : Z ≤ V := by
    have hz := (d.linear_involution_geometry h hH hp F hm hF he hmax).1
    rw [←centerIn_eq_map_center] at hz
    fin_cases i
    · exact hz.le.trans inf_le_left
    · exact hz.le.trans inf_le_right
  have hVV : V ≤ centralizer (V : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hweak := d.linear_root_planes_weakly_closed h hH hp F hm hF he hmax
  have hVi : V ∈ ({L.pCoreIn 2,(residual H).pCoreIn 2} : Set (Subgroup G)) := by
    fin_cases i <;> simp [V]
  obtain ⟨a,ha,heq⟩ := T.weakly_closed_normalizer_controls_set_fusion V
    ((hc i).2.2.trans (sourceS_le_sylow h.sylow_normalizes hH.1.1.2))
    (fun a ha => mem_normalizer_iff_map_conj_eq.mpr (hweak V hVi a ha))
    (Z : Set G) (Z.conjBy g : Set G)
    ((hVV.trans (centralizer_le hZV)).trans (Subgroup.centralizer_le_normalizer _))
    ((hVV.trans (centralizer_le hg)).trans (Subgroup.centralizer_le_normalizer _)) g rfl
  have han : a ∈ normalizer (![L,residual H] i : Set G) := by
    have hn := d.linear_root_normalizers h hH hp F hm hF he hmax
    fin_cases i
    · exact hn.1 ▸ ha
    · exact hn.2.1 ▸ ha
  have hcomp : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) := .linear F m hm hF he
  have hl := d.normalizer_local_conditions h hH hmax rfl
    (d.common_sylow_of_comparison h hH.1.1.2 hp hcomp)
    (d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp hcomp)
  have hprod : ∃ l ∈ ![L,residual H] i,
      ∃ b ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G), a = l*b := by
    fin_cases i
    · exact hl.factor_left a han
    · exact hl.factor_right a han
  obtain ⟨l,hl,b,hb,rfl⟩ := hprod
  have hbZ : Z.conjBy b = Z := by
    apply mem_normalizer_iff_map_conj_eq.mp
    exact (d.linear_center_normalizer h hH hp F hm hF he hmax).symm ▸ hb
  refine ⟨l,hl,?_⟩
  have hh : Z.conjBy (l*b) = Z.conjBy g := SetLike.coe_injective heq
  rwa [←conjBy_conjBy,hbZ] at hh

/-- Local conjugate central lines meeting outside the identity coincide. -/
theorem Preparation.linear_local_root_lines_eq (i : Fin 2)
    (a b x : G) (ha : a ∈ ![L,residual H] i) (hb : b ∈ ![L,residual H] i)
    (hxa : x ∈ (centerIn (sourceS L H)).conjBy a)
    (hxb : x ∈ (centerIn (sourceS L H)).conjBy b) (hx1 : x ≠ 1) :
    (centerIn (sourceS L H)).conjBy a = (centerIn (sourceS L H)).conjBy b := by
  let X := ![L,residual H] i
  let S := sourceS L H
  have center_eq (a : G) (ha : a ∈ X) (hxa : x ∈ (centerIn S).conjBy a) :
      (centerIn S).conjBy a = centerIn (X ⊓ centralizer ({x} : Set G)) := by
    obtain ⟨z,hz,hzx⟩ := hxa
    have hz1 : z ≠ 1 := by intro h; simp [h] at hzx; exact hx1 hzx.symm
    have hc := d.linear_factor_centralizer h hH hp F hm hF he hmax i z hz hz1
    have hmap : S.conjBy a = X ⊓ centralizer ({x} : Set G) := by
      apply le_antisymm
      · rintro _ ⟨y,hy,rfl⟩
        refine ⟨X.mul_mem (X.mul_mem ha ((d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he i) hy))
          (X.inv_mem ha),mem_centralizer_singleton_iff.mpr ?_⟩
        rw [←hzx]
        simpa only [map_mul,MulAut.conj_apply,MulEquiv.coe_toMonoidHom] using congrArg (MulAut.conj a) (hz.2 y hy)
      · rintro y ⟨hyX,hyx⟩
        refine ⟨a⁻¹*y*a,?_,by simp [mul_assoc]⟩
        change a⁻¹*y*a ∈ sourceS L H
        rw [←hc]
        refine ⟨X.mul_mem (X.mul_mem (X.inv_mem ha) hyX) ha,mem_centralizer_singleton_iff.mpr ?_⟩
        have hh := congrArg (MulAut.conj a⁻¹) (mem_centralizer_singleton_iff.mp hyx)
        have hinv : MulAut.conj a⁻¹ x = z := by rw [←hzx]; simp [mul_assoc]
        simpa only [map_mul,hinv,MulAut.conj_apply,inv_inv] using hh
    change (centerIn S).map (MulAut.conj a).toMonoidHom = _
    rw [centerIn_map_equiv]
    exact congrArg centerIn hmap
  exact (center_eq a ha hxa).trans (center_eq b hb hxb).symm

/-- The nonidentity vectors of each source root plane are partitioned by
its factor-conjugate central lines. -/
theorem Preparation.linear_root_line_partition (i : Fin 2) (x : G)
    (hx : x ∈ (![L,residual H] i).pCoreIn 2) (hx1 : x ≠ 1) :
    ∃! U : Subgroup G,
      (∃ a ∈ ![L,residual H] i, (centerIn (sourceS L H)).conjBy a = U) ∧ x ∈ U := by
  obtain ⟨z,hz,hz2,_⟩ := d.linear_exists_sylow_central_involution h hH hp F hm hF he hmax
  have hz1 : z ≠ 1 := by intro hh; simp [hh] at hz2
  have hzV : z ∈ (![L,residual H] i).pCoreIn 2 := by
    have hgeo := (d.linear_involution_geometry h hH hp F hm hF he hmax).1
    rw [←centerIn_eq_map_center] at hgeo
    fin_cases i
    · exact (hgeo ▸ hz).1
    · exact (hgeo ▸ hz).2
  obtain ⟨e⟩ := d.linear_factor_affine h hH hp F hm hF he i
  obtain ⟨a,ha,hax⟩ := Matrix.PSL3.LinearAmbientGeometry.affine_core_transitive
    (![L,residual H] i) e z x hzV hx hz1 hx1
  refine ⟨(centerIn (sourceS L H)).conjBy a,⟨⟨a,ha,rfl⟩,⟨z,hz,hax⟩⟩,?_⟩
  rintro U ⟨⟨b,hb,rfl⟩,hxb⟩
  exact d.linear_local_root_lines_eq h hH hp F hm hF he hmax i b a x hb ha hxb
    ⟨z,hz,hax⟩ hx1

/-- Exactly q+1 ambient conjugates of the original central line lie in
each root plane, as in source §5.3.6(2). -/
theorem Preparation.linear_root_line_count (i : Fin 2) :
    Nat.card {U : Subgroup G //
      (∃ g : G, (centerIn (sourceS L H)).conjBy g = U) ∧
        U ≤ (![L,residual H] i).pCoreIn 2} = Nat.card F + 1 := by
  classical
  let Z := centerIn (sourceS L H)
  let X := ![L,residual H] i
  let V := X.pCoreIn 2
  let C := {U : Subgroup G // ∃ a ∈ X, Z.conjBy a = U}
  have hZV : Z ≤ V := by
    have hz := (d.linear_involution_geometry h hH hp F hm hF he hmax).1
    rw [←centerIn_eq_map_center] at hz
    fin_cases i
    · exact hz.le.trans inf_le_left
    · exact hz.le.trans inf_le_right
  have hUV (U : C) : U.val ≤ V := by
    obtain ⟨a,ha,heq⟩ := U.property
    rw [←heq]
    have haV : V.conjBy a = V := mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X) (X.le_normalizer ha))
    exact (Subgroup.map_mono hZV).trans_eq haV
  let e : C ≃ {U : Subgroup G // (∃ g : G, Z.conjBy g = U) ∧ U ≤ V} :=
    Equiv.ofBijective (fun U => ⟨U.val,by
      obtain ⟨a,ha,heq⟩ := U.property
      exact ⟨⟨a,heq⟩,hUV U⟩⟩) (by
      constructor
      · intro U W heq
        exact Subtype.ext (congrArg (fun U : {U : Subgroup G // (∃ g : G, Z.conjBy g = U) ∧ U ≤ V} => U.val) heq)
      · rintro ⟨U,⟨g,hg⟩,hU⟩
        obtain ⟨a,ha,heq⟩ := d.linear_root_line_fusion h hH hp F hm hF he hmax i g (hg.symm ▸ hU)
        exact ⟨⟨U,a,ha,heq.trans hg⟩,rfl⟩)
  change Nat.card {U : Subgroup G // (∃ g : G, Z.conjBy g = U) ∧ U ≤ V} = _
  rw [←Nat.card_congr e]
  have hZcard : Nat.card Z = Nat.card F := by
    change Nat.card (centerIn (sourceS L H)) = Nat.card F
    rw [centerIn_eq_map_center,card_map_of_injective (sourceS L H).subtype_injective]
    exact (d.linear_involution_geometry h hH hp F hm hF he hmax).2.1
  have hUcard (U : C) : Nat.card U.val = Nat.card F := by
    obtain ⟨a,ha,heq⟩ := U.property
    rw [←heq]
    change Nat.card (Z.map (MulAut.conj a).toMonoidHom) = Nat.card F
    rw [card_map_of_injective (MulAut.conj a).injective,hZcard]
  let parts : C → Set G := fun U => (U.val : Set G) \ {1}
  have hparts (U : C) : (parts U).ncard = Nat.card F - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem U.val.one_mem]
    exact congrArg (fun k => k-1) (hUcard U)
  have hdis : Pairwise (Function.onFun Disjoint parts) := by
    intro U W hUW
    apply Set.disjoint_left.mpr
    rintro x ⟨hxU,hx1⟩ ⟨hxW,_⟩
    obtain ⟨a,ha,heqa⟩ := U.property
    obtain ⟨b,hb,heqb⟩ := W.property
    apply hUW
    apply Subtype.ext
    exact heqa.symm.trans ((d.linear_local_root_lines_eq h hH hp F hm hF he hmax i
      a b x ha hb (heqa.symm ▸ hxU) (heqb.symm ▸ hxW) hx1).trans heqb)
  have hcover : (⋃ U, parts U) = (V : Set G) \ {1} := by
    ext x
    constructor
    · intro hx
      obtain ⟨U,hU,hx1⟩ := Set.mem_iUnion.mp hx
      exact ⟨hUV U hU,hx1⟩
    · rintro ⟨hx,hx1⟩
      obtain ⟨U,hU,_⟩ := d.linear_root_line_partition h hH hp F hm hF he hmax i x hx hx1
      exact Set.mem_iUnion.mpr ⟨⟨U,hU.1⟩,hU.2,hx1⟩
  have hcount := congrArg Set.ncard hcover
  rw [Set.ncard_iUnion_of_finite (fun U => Set.toFinite (parts U)) hdis] at hcount
  let : Fintype C := Fintype.ofFinite C
  simp only [hparts,finsum_eq_sum_of_fintype,Finset.sum_const,Finset.card_univ,
    smul_eq_mul] at hcount
  rw [Set.ncard_sdiff_singleton_of_mem V.one_mem] at hcount
  change Fintype.card C * (Nat.card F - 1) = Nat.card V - 1 at hcount
  rw [((d.linear_core_structure h hH hp F hm hF he).2.2 i).2.1] at hcount
  rw [Nat.card_eq_fintype_card]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hs : Nat.card F - 1 + 1 = Nat.card F := Nat.sub_add_cancel hq.le
  have hs2 : Nat.card F ^ 2 - 1 + 1 = Nat.card F ^ 2 :=
    Nat.sub_add_cancel (by nlinarith)
  nlinarith

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
