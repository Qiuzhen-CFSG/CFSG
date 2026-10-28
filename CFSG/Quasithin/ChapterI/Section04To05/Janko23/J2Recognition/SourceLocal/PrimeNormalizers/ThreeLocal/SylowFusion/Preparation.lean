module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Extension
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.FusionTypes
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Models
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCube


/-!
# Source three-class fusion and the embedded Sylow center

The E₄ × A₅ centralizer in 47.1 fuses all second-class elements. Once the
second-normalizer calculation supplies order 72, comparison with the first
normalizer's order 2160 separates the classes. A Sylow three-subgroup cannot
then be abelian: one containing a second-class element would lie in its
normalizer, although 27 does not divide 72. Prime-cube extraspeciality follows.

A Sylow subgroup of the actual C_G(X), embedded in G, has center exactly X.
Sylow conjugacy transports this equality to the literal embedded centers of
all Sylow three-subgroups. The second-normalizer premise remains an explicit
unproved source calculation; none of these reductions asserts its existence.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3, printed pp.261–262.
-/

@[expose] public section

open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
variable {G : Type*} [Group G] [Finite G] {D : Seed G}
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem threeA_of_isConj {x y : G} (h : IsConj x y) (hx : ThreeA D x) :
    ThreeA D y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  let e := MulAut.conj g
  obtain ⟨hx, t, ht, hxt⟩ := (threeA_iff_centralizes D x).mp hx
  apply (threeA_iff_centralizes D _).mpr
  exact ⟨(e.orderOf_eq x).trans hx, e t,
    ht.trans (isConj_iff.mpr ⟨g, rfl⟩), hxt.map e⟩

theorem threeB_of_isConj {x y : G} (h : IsConj x y) (hx : ThreeB D x) :
    ThreeB D y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  let e := MulAut.conj g
  obtain ⟨hx, t, ht, hnt, hxt⟩ := hx
  refine ⟨(e.orderOf_eq x).trans hx, e t, (e.orderOf_eq t).trans ht, ?_, hxt.map e⟩
  intro hc
  exact hnt (hc.trans (isConj_iff.mpr ⟨g, rfl⟩).symm)

theorem exists_threeA (D : Seed G) : ∃ a : D.X, orderOf a = 3 ∧ ThreeA D (a : G) := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := D.X) 3 (by rw [D.card_X])
  refine ⟨a, ha, ?_⟩
  apply (threeA_iff_centralizes D _).mpr
  exact ⟨(orderOf_coe a).trans ha, D.z, IsConj.refl _,
    mem_centralizer_singleton_iff.mp (D.X_le a.property)⟩

theorem sylowThree_card (hG : Nat.card G = 604800) (P : Sylow 3 G) : Nat.card P = 27 := by
  rw [P.card_eq_multiplicity, hG]
  decide +kernel

theorem threeA_normalizer_card (H : CentralizerCalculation D)
    {x : G} (hx : ThreeA D x) : Nat.card (normalizer (zpowers x : Set G)) = 2160 := by
  obtain ⟨g, hg⟩ := hx.2
  let e := MulAut.conj (ConjAct.ofConjAct g)
  change D.X.map e.toMonoidHom = zpowers x at hg
  rw [← hg, ← map_equiv_normalizer_eq, card_map_of_injective e.injective]
  exact H.normalizer_card

theorem threeB_exists (S : InvolutionGeometry.SelectedGeometry D) : ∃ b : G, ThreeB D b := by
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := involutionCentralizer S.t) 3
    (by rw [S.model.centralizer_card]; norm_num)
  exact ⟨b, (orderOf_coe b).trans hb, S.t, S.other.1, S.other.2,
    mem_centralizer_singleton_iff.mp b.property⟩

private theorem a5_isConj_order_three (a b : alternatingGroup (Fin 5))
    (ha : orderOf a = 3) (hb : orderOf b = 3) : IsConj a b := by
  have hcycle (x : alternatingGroup (Fin 5)) (hx : orderOf x = 3) :
      (x : Equiv.Perm (Fin 5)).IsThreeCycle := by
    have ho : orderOf (x : Equiv.Perm (Fin 5)) = 3 := (orderOf_coe x).trans hx
    have hc := Equiv.Perm.isCycle_of_prime_order' (σ := (x : Equiv.Perm (Fin 5)))
      (by rw [ho]; decide) (by rw [ho]; decide)
    apply card_support_eq_three_iff.mp
    rw [← hc.orderOf, ho]
  exact alternatingGroup.isThreeCycle_isConj (by simp) (hcycle a ha) (hcycle b hb)

private theorem second_centralizer_isConj_order_three
    {t : G} (S : InvolutionGeometry.SecondCentralizer D t)
    (a b : involutionCentralizer t) (ha : orderOf a = 3) (hb : orderOf b = 3) :
    IsConj a b := by
  have hfst (x : involutionCentralizer t) (hx : orderOf x = 3) : (S.equiv x).1 = 1 := by
    have hd3 : orderOf (S.equiv x).1 ∣ 3 := by
      simpa [hx] using orderOf_map_dvd ((MonoidHom.fst _ _).comp S.equiv.toMonoidHom) x
    have hd4 : orderOf (S.equiv x).1 ∣ 4 := by
      simpa only [InvolutionGeometry.card_E4] using orderOf_dvd_natCard (S.equiv x).1
    have hd := Nat.dvd_gcd hd3 hd4
    norm_num at hd
    exact hd
  have hsnd (x : involutionCentralizer t) (hx : orderOf x = 3) : orderOf (S.equiv x).2 = 3 := by
    have h := (S.equiv.orderOf_eq x).trans hx
    rwa [Prod.orderOf, hfst x hx, orderOf_one, Nat.lcm_one_left] at h
  have hc := a5_isConj_order_three (S.equiv a).2 (S.equiv b).2 (hsnd a ha) (hsnd b hb)
  have hp : IsConj (S.equiv a) (S.equiv b) := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    apply isConj_iff.mpr
    refine ⟨(1, c), ?_⟩
    exact Prod.ext (by simp [hfst a ha, hfst b hb]) hc
  simpa only [MulEquiv.coe_toMonoidHom, S.equiv.symm_apply_apply] using
    S.equiv.symm.toMonoidHom.map_isConj hp

theorem threeB_isConj (S : InvolutionGeometry.SelectedGeometry D)
    {x y : G} (hx : ThreeB D x) (hy : ThreeB D y) : IsConj x y := by
  have placed {x : G} (hx : ThreeB D x) :
      ∃ a : involutionCentralizer S.t, orderOf a = 3 ∧ IsConj x (a : G) := by
    obtain ⟨hx, t, ht, hnt, hxt⟩ := hx
    obtain ⟨g, hg⟩ := isConj_iff.mp (InvolutionGeometry.OtherInvolution.isConj
      (D := D) (t := t) (u := S.t) ⟨ht, hnt⟩ S.other)
    let e := MulAut.conj g
    have hm : e x ∈ involutionCentralizer S.t := by
      apply mem_centralizer_singleton_iff.mpr
      have hc := hxt.map e
      change Commute (e x) (e t) at hc
      exact hg ▸ hc
    exact ⟨⟨e x, hm⟩, (orderOf_coe _).symm.trans ((e.orderOf_eq x).trans hx),
      isConj_iff.mpr ⟨g, rfl⟩⟩
  obtain ⟨a, ha, hxa⟩ := placed hx
  obtain ⟨b, hb, hyb⟩ := placed hy
  exact hxa.trans (((involutionCentralizer S.t).subtype.map_isConj
    (second_centralizer_isConj_order_three S.model a b ha hb)).trans hyb.symm)

/-- The outstanding second-normalizer calculation in 47.3(2). -/
def SecondNormalizerFamily (D : Seed G) : Prop :=
  ∀ y : G, ThreeB D y → Nonempty (normalizer (zpowers y : Set G) ≃*
    Equiv.Perm (Fin 3) × alternatingGroup (Fin 4))

theorem threeB_normalizer_card (hB : SecondNormalizerFamily D)
    {y : G} (hy : ThreeB D y) : Nat.card (normalizer (zpowers y : Set G)) = 72 := by
  rw [Nat.card_congr (hB y hy).some.toEquiv, Nat.card_prod,
    Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 3)),
    Fintype.card_perm, Fintype.card_fin, nat_card_alternatingGroup]
  norm_num

theorem threeA_not_threeB (H : CentralizerCalculation D) (hB : SecondNormalizerFamily D)
    {x : G} (hx : ThreeA D x) : ¬ ThreeB D x := by
  intro hy
  have ha := threeA_normalizer_card H hx
  have hb := threeB_normalizer_card hB hy
  omega

theorem sylowThree_noncommutative (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D) (hB : SecondNormalizerFamily D)
    (P : Sylow 3 G) : ¬ IsMulCommutative P := by
  intro hcomm
  let := hcomm
  obtain ⟨b, hb⟩ := threeB_exists S
  have hp : IsPGroup 3 (zpowers b) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hb.1]; rfl)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hqc : IsMulCommutative Q := IsMulCommutative.of_comm fun a b =>
    (Q.equiv P).injective (by simp only [map_mul]; exact mul_comm _ _)
  have hle : (Q : Subgroup G) ≤ normalizer (zpowers b : Set G) :=
    ((le_centralizer_iff_isMulCommutative.mpr hqc).trans
      (centralizer_le hQ)).trans (Subgroup.centralizer_le_normalizer _)
  have hd := card_dvd_of_le hle
  rw [sylowThree_card hG Q, threeB_normalizer_card hB hb] at hd
  norm_num at hd

theorem sylowThree_extraspecial (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D) (hB : SecondNormalizerFamily D)
    (P : Sylow 3 G) : IsExtraspecial 3 P :=
  IsExtraspecial.of_noncommutative_card_prime_cube (sylowThree_card hG P)
    (sylowThree_noncommutative hG S hB P)

theorem exists_sylowThree_in_C (H : CentralizerCalculation D)
    (hG : Nat.card G = 604800) :
    ∃ P : Sylow 3 G, D.X ≤ (P : Subgroup G) ∧ (P : Subgroup G) ≤ C D := by
  let Q : Sylow 3 (C D) := Classical.choice inferInstance
  have hQ : Nat.card Q = 27 := by
    rw [Q.card_eq_multiplicity, H.centralizer_card]
    decide +kernel
  let A := (Q : Subgroup (C D)).map (C D).subtype
  have hA : Nat.card A = 27 := by
    rw [card_map_of_injective (C D).subtype_injective, hQ]
  have hXp : IsPGroup 3 (XC D) := IsPGroup.of_card (n := 1)
    (by simpa using CentralizerCalculation.card_XC (D := D))
  have hXQ := hXp.le_sylow_of_normal Q
  let P : Sylow 3 G := Sylow.ofCard A (by rw [hA, hG]; decide +kernel)
  refine ⟨P, ?_, map_subtype_le _⟩
  intro x hx
  exact mem_map_of_mem (C D).subtype (hXQ (show (⟨x, X_le_C D hx⟩ : C D) ∈ XC D from hx))

theorem center_eq_seed_of_le_C (P : Sylow 3 G) (hP : IsExtraspecial 3 P)
    (hXP : D.X ≤ (P : Subgroup G)) (hPC : (P : Subgroup G) ≤ C D) :
    (center P).map (P : Subgroup G).subtype = D.X := by
  let := hP
  apply (eq_of_le_of_card_ge ?_ ?_).symm
  · intro x hx
    refine ⟨⟨x, hXP hx⟩, mem_center_iff.mpr ?_, rfl⟩
    intro y
    exact Subtype.ext ((hPC y.property) x hx).symm
  · rw [card_map_of_injective (P : Subgroup G).subtype_injective,
      IsExtraspecial.center_order_p 3 P, D.card_X]

theorem sylowThree_center_vertex (H : CentralizerCalculation D)
    (hG : Nat.card G = 604800) (S : InvolutionGeometry.SelectedGeometry D)
    (hB : SecondNormalizerFamily D) (P : Sylow 3 G) :
    (center P).map (P : Subgroup G).subtype ∈ MulAction.orbit (ConjAct G) D.X := by
  obtain ⟨Q, hXQ, hQC⟩ := exists_sylowThree_in_C H hG
  have hZ := center_eq_seed_of_le_C Q (sylowThree_extraspecial hG S hB Q) hXQ hQC
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨ConjAct.toConjAct g, ?_⟩
  rw [← hZ]
  change ((center Q).map (Q : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom = _
  let e := Q.equivSMul g
  have he : (center Q).map e.toMonoidHom = center (g • Q : Sylow 3 G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      apply mem_center_iff.mpr
      intro a
      obtain ⟨b, rfl⟩ := e.surjective a
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
        congrArg e (mem_center_iff.mp hy b)
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      apply mem_center_iff.mpr
      intro y
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using mem_center_iff.mp hx (e y)
  rw [← he, map_map, map_map]
  rfl

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
