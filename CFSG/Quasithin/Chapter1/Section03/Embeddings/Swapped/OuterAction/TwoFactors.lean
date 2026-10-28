module

public import Theory.GroupTheory.AutomorphismTowerSimple
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.Ring

/-!
# Outer order of two nonabelian simple factors

Every surjective homomorphism from Q × Q to the finite nonabelian simple
group Q uses exactly one coordinate: each nontrivial coordinate restriction
is an automorphism, and its commuting companion has central image. Applying
this to both coordinates of an automorphism gives either two coordinate
automorphisms or their composite with the transposition.

This description is proved here and counted, yielding
|Out(Q × Q)| = 2 · |Out(Q)|². Consequently, when Out(Q) has odd order,
every two-subgroup of Out(Q × Q) has order at most two. An actual product
isomorphism transports both this bound and centerlessness.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of Proposition 1.3.4, printed p.510.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.SwappedOuter
variable {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q] [Group.IsPerfect Q]

omit [Finite Q] in
private theorem simple_center : center Q = ⊥ := by
  rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp h)).elim

omit [Group.IsPerfect Q] in
private theorem endomorphism_cases (f : Q →* Q) :
    f = 1 ∨ ∃ a : MulAut Q, f = a.toMonoidHom := by
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
  · have hi : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp h
    exact Or.inr ⟨MulEquiv.ofBijective f ⟨hi, Finite.surjective_of_injective hi⟩, rfl⟩
  · exact Or.inl (MonoidHom.ker_eq_top_iff.mp h)

private theorem surjective_prod_hom_cases (f : Q × Q →* Q) (hf : Function.Surjective f) :
    (∃ a : MulAut Q, ∀ x y, f (x, y) = a x) ∨
    (∃ a : MulAut Q, ∀ x y, f (x, y) = a y) := by
  let l := f.comp (MonoidHom.inl Q Q)
  let r := f.comp (MonoidHom.inr Q Q)
  have he (x y : Q) : f (x, y) = l x * r y := by
    change f (x, y) = f (x, 1) * f (1, y)
    rw [← map_mul]
    simp
  rcases endomorphism_cases l with hl | ⟨a, ha⟩
  · right
    have hr : Function.Surjective r := by
      intro z
      obtain ⟨⟨x, y⟩, hxy⟩ := hf z
      refine ⟨y, ?_⟩
      simpa only [he, hl, MonoidHom.one_apply, one_mul] using hxy
    rcases endomorphism_cases r with hb | ⟨b, hb⟩
    · have hone : ∀ z : Q, z = 1 := by
        intro z
        obtain ⟨y, hy⟩ := hr z
        simpa only [hb, MonoidHom.one_apply] using hy.symm
      exact (not_nontrivial_iff_subsingleton.mpr ⟨fun x y => (hone x).trans (hone y).symm⟩
        inferInstance).elim
    · exact ⟨b, fun x y => by simp only [he, hl, hb, MonoidHom.one_apply, one_mul,
          MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]⟩
  · left
    have hr (y : Q) : r y = 1 := by
      have hc : r y ∈ center Q := by
        apply mem_center_iff.mpr
        intro z
        obtain ⟨x, rfl⟩ := a.surjective z
        have hh : l x * r y = r y * l x := by
          change f (x, 1) * f (1, y) = f (1, y) * f (x, 1)
          rw [← map_mul, ← map_mul]
          simp
        simpa only [ha, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] using hh
      simpa only [simple_center, mem_bot] using hc
    exact ⟨a, fun x y => by rw [he, hr, mul_one, ha]; rfl⟩

private theorem prod_aut_cases (f : MulAut (Q × Q)) :
    ∃ a b : MulAut Q,
      (∀ x y, f (x, y) = (a x, b y)) ∨ (∀ x y, f (x, y) = (a y, b x)) := by
  have hfst : Function.Surjective ((MonoidHom.fst Q Q).comp f.toMonoidHom) := by
    intro x
    obtain ⟨z, hz⟩ := f.surjective (x, 1)
    exact ⟨z, congrArg Prod.fst hz⟩
  have hsnd : Function.Surjective ((MonoidHom.snd Q Q).comp f.toMonoidHom) := by
    intro y
    obtain ⟨z, hz⟩ := f.surjective (1, y)
    exact ⟨z, congrArg Prod.snd hz⟩
  obtain ⟨w, hw⟩ := exists_ne (1 : Q)
  rcases surjective_prod_hom_cases _ hfst with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
    rcases surjective_prod_hom_cases _ hsnd with ⟨b, hb⟩ | ⟨b, hb⟩
  · exfalso
    have he : f (1, w) = f (1, 1) := Prod.ext ((ha 1 w).trans (ha 1 1).symm)
      ((hb 1 w).trans (hb 1 1).symm)
    exact hw (congrArg Prod.snd (f.injective he))
  · exact ⟨a, b, Or.inl (fun x y => Prod.ext (ha x y) (hb x y))⟩
  · exact ⟨a, b, Or.inr (fun x y => Prod.ext (ha x y) (hb x y))⟩
  · exfalso
    have he : f (w, 1) = f (1, 1) := Prod.ext ((ha w 1).trans (ha 1 1).symm)
      ((hb w 1).trans (hb 1 1).symm)
    exact hw (congrArg Prod.fst (f.injective he))

private def prodAutParam : ((MulAut Q × MulAut Q) × Bool) → MulAut (Q × Q)
  | ((a, b), false) => a.prodCongr b
  | ((a, b), true) => MulEquiv.prodComm.trans (a.prodCongr b)

private theorem prodAutParam_bijective : Function.Bijective (prodAutParam (Q := Q)) := by
  constructor
  · rintro ⟨⟨a, b⟩, i⟩ ⟨⟨c, d⟩, j⟩ h
    have he (x y : Q) := DFunLike.congr_fun h (x, y)
    obtain ⟨w, hw⟩ := exists_ne (1 : Q)
    cases i <;> cases j
    · have ha : a = c := by
        ext x
        simpa [prodAutParam, MulEquiv.prodCongr] using congrArg Prod.fst (he x 1)
      have hb : b = d := by
        ext y
        simpa [prodAutParam, MulEquiv.prodCongr] using congrArg Prod.snd (he 1 y)
      simp only [ha, hb]
    · exfalso
      have hz : a w = 1 := by
        simpa [prodAutParam, MulEquiv.prodCongr] using congrArg Prod.fst (he w 1)
      exact hw (a.injective (hz.trans a.map_one.symm))
    · exfalso
      have hz : c w = 1 := by
        simpa [prodAutParam, MulEquiv.prodCongr] using (congrArg Prod.fst (he w 1)).symm
      exact hw (c.injective (hz.trans c.map_one.symm))
    · have ha : a = c := by
        ext x
        simpa [prodAutParam, MulEquiv.prodCongr] using congrArg Prod.fst (he 1 x)
      have hb : b = d := by
        ext y
        simpa [prodAutParam, MulEquiv.prodCongr] using congrArg Prod.snd (he y 1)
      simp only [ha, hb]
  · intro f
    obtain ⟨a, b, h | h⟩ := prod_aut_cases f
    · refine ⟨((a, b), false), ?_⟩
      apply MulEquiv.ext
      rintro ⟨x, y⟩
      simpa [prodAutParam, MulEquiv.prodCongr] using (h x y).symm
    · refine ⟨((a, b), true), ?_⟩
      apply MulEquiv.ext
      rintro ⟨x, y⟩
      simpa [prodAutParam, MulEquiv.prodCongr] using (h x y).symm

private theorem card_prod_aut :
    Nat.card (MulAut (Q × Q)) = 2 * Nat.card (MulAut Q) ^ 2 := by
  have h := Nat.card_congr (Equiv.ofBijective (prodAutParam (Q := Q)) prodAutParam_bijective)
  have hb : Nat.card Bool = 2 := by simp only [Nat.card_eq_fintype_card, Fintype.card_bool]
  rw [Nat.card_prod, Nat.card_prod, hb] at h
  rw [← h]
  ring

omit [Finite Q] in
private theorem prod_center : center (Q × Q) = ⊥ := by
  rw [Subgroup.center_prod, simple_center, Subgroup.bot_prod_bot]

private theorem card_inner {L : Type*} [Group L] (hc : center L = ⊥) :
    Nat.card (MulAut.innerSubgroup L) = Nat.card L :=
  (Nat.card_congr (MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hc)).toEquiv).symm

/-- The actual two-factor outer group has twice the square of the single-factor order. -/
theorem card_outer_product :
    Nat.card (MulAut.Outer (Q × Q)) = 2 * Nat.card (MulAut.Outer Q) ^ 2 := by
  have hQ := (MulAut.innerSubgroup Q).index_mul_card
  have hQQ := (MulAut.innerSubgroup (Q × Q)).index_mul_card
  rw [Subgroup.index_eq_card, card_inner simple_center] at hQ
  rw [Subgroup.index_eq_card, card_inner prod_center, Nat.card_prod, card_prod_aut] at hQQ
  change Nat.card (MulAut.Outer Q) * Nat.card Q = Nat.card (MulAut Q) at hQ
  change Nat.card (MulAut.Outer (Q × Q)) * (Nat.card Q * Nat.card Q) =
    2 * Nat.card (MulAut Q) ^ 2 at hQQ
  have hpos : 0 < Nat.card Q * Nat.card Q := Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc
    Nat.card (MulAut.Outer (Q × Q)) * (Nat.card Q * Nat.card Q) =
        2 * Nat.card (MulAut Q) ^ 2 := hQQ
    _ = (2 * Nat.card (MulAut.Outer Q) ^ 2) * (Nat.card Q * Nat.card Q) := by
      rw [← hQ]
      ring

omit [Finite Q] in
/-- An actual product of two nonabelian simple groups is centerless. -/
theorem center_eq_bot_of_product_equiv {L : Type*} [Group L] (e : L ≃* Q × Q) :
    center L = ⊥ := by
  apply bot_unique
  intro z hz
  apply e.injective
  have hmem : e z ∈ center (Q × Q) := by
    apply mem_center_iff.mpr
    intro w
    obtain ⟨x, rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul]
    exact congrArg e (mem_center_iff.mp hz x)
  have he : e z = 1 := by simpa only [prod_center, mem_bot] using hmem
  exact he.trans e.map_one.symm

/-- Odd single-factor outer order leaves at most one factor transposition in a two-subgroup. -/
theorem outer_two_subgroup_card_le_two {L : Type*} [Group L] [Finite L]
    (e : L ≃* Q × Q) (hodd : Odd (Nat.card (MulAut.Outer Q)))
    (R : Subgroup (MulAut.Outer L)) (hR : IsPGroup 2 R) : Nat.card R ≤ 2 := by
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hd : Nat.card R ∣ 2 * Nat.card (MulAut.Outer Q) ^ 2 := by
    have h := R.card_subgroup_dvd_card
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv, card_outer_product] at h
    exact h
  have hc : Nat.Coprime (Nat.card R) (Nat.card (MulAut.Outer Q) ^ 2) := by
    rw [hk]
    exact (hodd.coprime_two_left.pow_left k).pow_right 2
  exact Nat.le_of_dvd (by decide : 0 < 2) (hc.dvd_of_dvd_mul_right hd)

end CFSG.Quasithin.Chapter1.XiEmbedding.SwappedOuter
