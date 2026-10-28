module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.PerfectActions
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.CComponent.Structure
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.SpecificGroups.SL2.ResidualTwoExtension

/-!
# Separating C-component actions on prime planes

Distinct C-components commute modulo the solvable radical. In a quasisimple
image, a nontrivial perfect normal image of the first is the whole image;
its commutator with the second is central, forcing the perfect second image
to vanish. Prime-field perfect-subgroup recognition supplies quasisimplicity
for the actual image in SL₂. Determinant one extends the result to arbitrary
actions on elementary abelian groups of order at most p².

For an actual normal p-subgroup P, Burnside's Frattini kernel theorem lifts
this fixation from P/Φ(P) to P. `centralizes_normal_pGroup` preserves the
literal ambient conjugation action. Finally, generalized-Fitting
self-centralization and the perfect iterated-commutator lemma lift
centralization of F*(B) to centralization of B.

These are the action and final centralizer steps of A.3.7. Applying them
to every Fitting core still needs the noncentral structural branch of A.3.6;
no general C-component commutation conclusion is asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.7 and its proof, printed p.45.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.RankActions
namespace CFSG.Quasithin.ChapterA.Section03.CComponentCommutation

variable {G D : Type*} [Group G] [Group D] [Finite G] [Finite D]

theorem commutator_le_radical {B C : Subgroup G}
    (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C) :
    ⁅B, C⁆ ≤ solvableRadical G := by
  let q := QuotientGroup.mk' (solvableRadical G)
  have hb := hB.map_quotient (solvableRadical G)
  have hc := hC.map_quotient (solvableRadical G)
  have hn : B.map q ≠ C.map q := fun he => hne (hB.eq_of_map_quotient_eq hC _ he)
  have he := hb.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot
    (solvableRadical_quotient_solvableRadical (G := G)) hc hn
  have hm : ⁅B,C⁆.map q = ⊥ := by rw [map_commutator]; exact he
  simpa only [q, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hm

omit [Finite D] in
private theorem perfect_eq_bot_of_le_center (B : Subgroup D) [Group.IsPerfect B]
    (hB : B ≤ center D) : B = ⊥ := by
  have hc : ⁅B,B⁆ = ⊥ := le_bot_iff.mp ((commutator_mono hB hB).trans
    (commutator_center_left (center D)).le)
  simpa only [commutator_eq_self] using hc

theorem trivial_image_of_quasisimple_image [IsQuasisimple D]
    (f : G →* D) (hf : Function.Surjective f)
    {B C : Subgroup G} [B.Normal]
    (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C)
    (hb : ¬ B ≤ f.ker) : C ≤ f.ker := by
  let : Group.IsPerfect B := hB.perfect
  let : Group.IsPerfect C := hC.perfect
  let : Group.IsPerfect (B.map f) := Group.IsPerfect.map f
  let : Group.IsPerfect (C.map f) := Group.IsPerfect.map f
  let : (B.map f).Normal := Normal.map inferInstance f hf
  have htop : B.map f = ⊤ := by
    rcases IsQuasisimple.normal_le_center_or_eq_top (B.map f) with hz | ht
    · exact (hb ((Subgroup.map_eq_bot_iff B).mp
        (perfect_eq_bot_of_le_center (B.map f) hz))).elim
    · exact ht
  have hr : (solvableRadical G).map f ≤ center D :=
    (map_solvableRadical_le_of_surjective f hf).trans
      IsQuasisimple.solvableRadical_le_center
  have hc : ⁅(⊤ : Subgroup D), C.map f⁆ ≤ center D := by
    rw [← htop, ← map_commutator]
    exact (map_mono (commutator_le_radical hB hC hne)).trans hr
  have hz : C.map f ≤ center D := by
    rw [← (C.map f).commutator_eq_self]
    exact (commutator_mono le_top le_rfl).trans hc
  exact (Subgroup.map_eq_bot_iff C).mp (perfect_eq_bot_of_le_center (C.map f) hz)

theorem trivial_SL2_image [Group.IsPerfect G]
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (f : G →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    {B C : Subgroup G} [B.Normal]
    (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C)
    (hb : ¬ B ≤ f.ker) : C ≤ f.ker := by
  let g := f.rangeRestrict
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hne_range : f.range ≠ ⊥ := by
    intro hz
    apply hb
    intro b _
    have hm : f b ∈ f.range := ⟨b,rfl⟩
    simpa only [hz, mem_bot, MonoidHom.mem_ker] using hm
  let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr hne_range
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hQ : IsQuasisimple f.range := by
    rcases primePerfectSL2Recognition p hp f.range inferInstance inferInstance
      with hfull | hexception
    · obtain ⟨e⟩ := hfull
      exact Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
        (F := ZMod p) (by simpa only [Nat.card_zmod] using hp) e
    · obtain ⟨_, ⟨e⟩⟩ := hexception
      exact Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
        (F := ZMod 5) (by rw [Nat.card_zmod]; decide) e
  let := hQ
  have hker : g.ker = f.ker := by
    ext x
    change (f.rangeRestrict x = 1) ↔ f x = 1
    exact Subtype.ext_iff
  have ht := trivial_image_of_quasisimple_image g f.rangeRestrict_surjective
    hB hC hne (by simpa only [hker] using hb)
  simpa only [hker] using ht

theorem trivial_plane_action [Group.IsPerfect G]
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian p V]
    (hV : Nat.card V ≤ p ^ 2) (a : G →* MulAut V)
    {B C : Subgroup G} [B.Normal]
    (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C)
    (hb : ¬ B ≤ a.ker) : C ≤ a.ker := by
  obtain ⟨j, hj⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le V hV
  let f := j.comp a
  have hd (x : G) : (f x).det = 1 :=
    Abelianization.commutator_subset_ker (Matrix.GeneralLinearGroup.det.comp f)
      Group.IsPerfect.mem_commutator
  let g : G →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
    { toFun := fun x => ⟨(f x : Matrix (Fin 2) (Fin 2) (ZMod p)), congrArg Units.val (hd x)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro x y; apply Subtype.ext; exact congrArg Units.val (f.map_mul x y) }
  have hker : g.ker = a.ker := by
    ext x
    change g x = 1 ↔ a x = 1
    constructor
    · intro hx
      apply hj
      rw [map_one]
      apply Units.ext
      exact congrArg Subtype.val hx
    · intro hx
      apply Subtype.ext
      change (j (a x)).val = 1
      rw [hx, map_one]
      rfl
  simpa only [hker] using trivial_SL2_image hp g hB hC hne
    (by simpa only [hker] using hb)

theorem centralizes_pGroup_of_plane_action [Group.IsPerfect G]
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P)
    (hcard : Nat.card (P ⧸ frattini P) ≤ p ^ 2) (a : G →* MulAut P)
    {B C : Subgroup G} [B.Normal]
    (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C)
    (hb : ¬ B ≤ ((quotientAut (frattini P)).comp a).ker) : C ≤ a.ker := by
  let : Fact (IsPGroup p P) := ⟨hP⟩
  let : IsElementaryAbelian p (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  have hc := trivial_plane_action hp hcard ((quotientAut (frattini P)).comp a)
    hB hC hne hb
  let : Group.IsPerfect C := hC.perfect
  have hphi : (quotientAut (frattini P)).comp (a.comp C.subtype) = 1 := by
    ext c x
    exact DFunLike.congr_fun (hc c.property) x
  have ha : a.comp C.subtype = 1 := by
    by_contra hn
    exact MonoidHom.frattini_comp_ne_one_of_isPerfect hP (a.comp C.subtype) hn hphi
  intro c hc
  exact DFunLike.congr_fun ha ⟨c,hc⟩

end CFSG.Quasithin.ChapterA.Section03.CComponentCommutation

namespace CFSG.Quasithin.ChapterA.Section03.CComponentCommutation
variable {G : Type*} [Group G] [Finite G]

theorem centralizes_normal_pGroup [Group.IsPerfect G]
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (hcard : Nat.card (P ⧸ frattini P) ≤ p ^ 2)
    {B C : Subgroup G} [B.Normal]
    (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C)
    (hb : ⁅P,B⁆ ≠ ⊥) : ⁅P,C⁆ = ⊥ := by
  let : Group.IsPerfect B := hB.perfect
  let a : G →* MulAut P := MulAut.conjNormal
  have hactive : ¬ B ≤ ((quotientAut (frattini P)).comp a).ker := by
    intro hz
    apply frattiniAction_ne_one P B hP hb
    ext b z
    exact DFunLike.congr_fun (hz b.property) z
  have hc := centralizes_pGroup_of_plane_action hp hP hcard a hB hC hne hactive
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
  intro c hcC x hx
  have he := congrArg (fun t : MulAut P => (t ⟨x,hx⟩ : G)) (hc hcC)
  change c * x * c⁻¹ = x at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

theorem commutes_of_centralizes_generalizedFitting
    (B C : Subgroup G) [B.Normal] [Group.IsPerfect C]
    (hc : ⁅(generalizedFitting B).map B.subtype, C⁆ = ⊥) : ⁅B,C⁆ = ⊥ := by
  let F := (generalizedFitting B).map B.subtype
  let : F.Normal := ConjAct.normal_of_characteristic_of_normal
  have hCF : C ≤ centralizer (F : Set G) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hc
  have hcomm : ⁅B,C⁆ ≤ F := by
    have hB := commutator_le_left B C
    have hC := (commutator_mono le_rfl hCF).trans
      (commutator_le_right B (centralizer (F : Set G)))
    intro x hx
    have hz : (⟨x,hB hx⟩ : B) ∈ centralizer (generalizedFitting B : Set B) := by
      intro y hy
      exact Subtype.ext (hC hx y (mem_map_of_mem B.subtype hy))
    exact mem_map_of_mem B.subtype (centralizer_generalizedFitting_le B hz)
  exact commutator_eq_bot_of_iterated_eq_bot B C
    (le_bot_iff.mp ((commutator_mono hcomm le_rfl).trans hc.le))

end CFSG.Quasithin.ChapterA.Section03.CComponentCommutation
