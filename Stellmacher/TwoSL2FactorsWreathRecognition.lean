module
public import Stellmacher.SectionOne.SL2NormalizerInner
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.RegularWreathProduct

/-!
# Recognition of a two-factor SL₂(2) wreath product

Let two commuting, disjoint SL₂(2) subgroups have a trivial common
centralizer. If the ambient finite group permutes these factors and some
element exchanges them, the ambient group is the regular wreath product
SL₂(2) ≀ C₂. This is the group recognition step behind the two-factor
alternative of Stellmacher (1.7), used in (9.1) and (9.3); see journal
pp. 19 and 48–50 of `refs/latex/stellmacher-n-group.tex`.

Completeness of SL₂(2), supplied by `SL2NormalizerInner`, first writes
every factor-preserving element as a product from the two factors. For
a swapping element x, write x² = df and put t = d⁻¹x. Then t² lies in
the second factor, and conjugating it by t puts it in the first factor
as well. Disjointness gives t² = 1. Every ambient element consequently
has one of the two product normal forms. The final isomorphism evaluates
the two wreath coordinates in these commuting factors and its C₂
coordinate at t. Its kernel is trivial by disjointness, and the normal
forms prove surjectivity.
-/

namespace Stellmacher
open SectionOne
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev splitFlip : C2 := Multiplicative.ofAdd 1
private theorem c2_cases (a : C2) : a = 1 ∨ a = splitFlip := by
  change a.toAdd = 0 ∨ a.toAdd = 1
  have := a.toAdd.val_lt
  have hv : a.toAdd.val = 0 ∨ a.toAdd.val = 1 := by omega
  rcases hv with h | h
  · left; exact ZMod.val_injective 2 (by simpa only [ZMod.val_zero] using h)
  · right; exact ZMod.val_injective 2 (by simpa only [show (1 : ZMod 2).val = 1 by decide] using h)

variable {G : Type*} [Group G]
private def splitMap (D : Subgroup G) (x : G) (w : RegularWreathProduct D C2) : G :=
  (w.left 1 : G) * (x * (w.left splitFlip : G) * x⁻¹) * if w.right = 1 then 1 else x

private theorem splitMap_mul (D : Subgroup G) (x : G) (hx : x * x = 1)
    (hc : ∀ d e : D, Commute (d : G) (x * (e : G) * x⁻¹))
    (w v : RegularWreathProduct D C2) :
    splitMap D x (w * v) = splitMap D x w * splitMap D x v := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx
  have hflip : splitFlip ≠ 1 := by decide
  rcases c2_cases w.right with hw | hw <;>
    rcases c2_cases v.right with hv | hv <;>
    simp only [splitMap, RegularWreathProduct.mul_left, Pi.mul_apply,
      RegularWreathProduct.mul_right, hw, hv, one_mul, mul_one,
      inv_one, Subgroup.coe_mul, hflip, if_false]
  all_goals try simp only [show splitFlip * splitFlip = 1 by decide,
    show splitFlip⁻¹ = splitFlip by decide]
  all_goals simp only [hxi]
  all_goals simp only [ite_true, mul_one]
  · have hh := (hc (v.left 1) (w.left splitFlip)).symm.mul_mul_mul_comm
      (w.left 1 : G) (x * (v.left splitFlip : G) * x⁻¹)
    have hxx (y : G) : x * (x * y) = y := by simp [← mul_assoc, hx]
    simpa only [hxi, mul_assoc, hxx] using hh.symm
  · have hh := congrArg (fun z : G => z * x)
      ((hc (v.left 1) (w.left splitFlip)).symm.mul_mul_mul_comm
      (w.left 1 : G) (x * (v.left splitFlip : G) * x⁻¹)).symm
    have hxx (y : G) : x * (x * y) = y := by simp [← mul_assoc, hx]
    simpa only [hxi, mul_assoc, hxx, hx, mul_one] using hh
  · have hh := congrArg (fun z : G => (w.left 1 : G) * z * x)
      (hc (v.left splitFlip) (w.left splitFlip * v.left 1)).eq
    have hxx (y : G) : x * (x * y) = y := by simp [← mul_assoc, hx]
    simpa only [hxi, Subgroup.coe_mul, mul_assoc, hxx, hx, mul_one] using hh
  · have hh := congrArg (fun z : G => (w.left 1 : G) * z)
      (hc (v.left splitFlip) (w.left splitFlip * v.left 1)).eq
    have hxx (y : G) : x * (x * y) = y := by simp [← mul_assoc, hx]
    simpa only [hxi, Subgroup.coe_mul, mul_assoc, hxx, hx, mul_one] using hh

private def splitHom (D : Subgroup G) (x : G) (hx : x * x = 1)
    (hc : ∀ d e : D, Commute (d : G) (x * (e : G) * x⁻¹)) :
    RegularWreathProduct D C2 →* G where
  toFun := splitMap D x
  map_one' := by simp [splitMap]
  map_mul' := splitMap_mul D x hx hc


private theorem splitHom_injective (D : Subgroup G) (x : G) (hx : x * x = 1)
    (hc : ∀ d e : D, Commute (d : G) (x * (e : G) * x⁻¹))
    (hd : Disjoint D (D.conjBy x)) (hxn : x ∉ D ⊔ D.conjBy x) :
    Function.Injective (splitHom D x hx hc) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro w hw
  change splitMap D x w = 1 at hw
  have hconj : x * (w.left splitFlip : G) * x⁻¹ ∈ D.conjBy x := by
    exact Subgroup.mem_map.mpr ⟨w.left splitFlip, (w.left splitFlip).property, rfl⟩
  have hbase : (w.left 1 : G) * (x * (w.left splitFlip : G) * x⁻¹) ∈ D ⊔ D.conjBy x :=
    (D ⊔ D.conjBy x).mul_mem ((le_sup_left : D ≤ D ⊔ D.conjBy x) (w.left 1).property)
      ((le_sup_right : D.conjBy x ≤ D ⊔ D.conjBy x) hconj)
  have hright : w.right = 1 := by
    by_contra hn
    simp only [splitMap, if_neg hn] at hw
    have he : x = ((w.left 1 : G) * (x * (w.left splitFlip : G) * x⁻¹))⁻¹ :=
      (inv_eq_of_mul_eq_one_right hw).symm
    apply hxn
    exact Eq.mpr (congrArg (fun z : G => z ∈ D ⊔ D.conjBy x) he)
      ((D ⊔ D.conjBy x).inv_mem hbase)
  simp only [splitMap, hright, ite_true, mul_one] at hw
  have hdconj : (w.left 1 : G) ∈ D.conjBy x := by
    have he : (w.left 1 : G) = (x * (w.left splitFlip : G) * x⁻¹)⁻¹ :=
      (inv_eq_of_mul_eq_one_left hw).symm
    exact he ▸ (D.conjBy x).inv_mem hconj
  have hd1 : (w.left 1 : G) = 1 := Subgroup.disjoint_def.mp hd (w.left 1).property hdconj
  have hd2 : (w.left splitFlip : G) = 1 := by
    rw [hd1, one_mul] at hw
    have := congrArg (fun z : G => x⁻¹ * z * x) hw
    simpa [mul_assoc] using this
  change w = 1
  apply RegularWreathProduct.ext
  · funext c
    rcases c2_cases c with rfl | rfl
    · exact Subtype.ext hd1
    · exact Subtype.ext hd2
  · exact hright

private theorem split_wreath_equiv (D : Subgroup G) (x : G) (hx : x * x = 1)
    (hc : ∀ d e : D, Commute (d : G) (x * (e : G) * x⁻¹))
    (hd : Disjoint D (D.conjBy x)) (hxn : x ∉ D ⊔ D.conjBy x)
    (hnorm : ∀ g : G, ∃ d e : D,
      g = (d : G) * (x * (e : G) * x⁻¹) ∨
      g = (d : G) * (x * (e : G) * x⁻¹) * x) :
    Nonempty (G ≃* RegularWreathProduct D C2) := by
  classical
  refine ⟨(MulEquiv.ofBijective (splitHom D x hx hc) ⟨splitHom_injective D x hx hc hd hxn, ?_⟩).symm⟩
  intro g
  obtain ⟨d, e, hg | hg⟩ := hnorm g
  · refine ⟨⟨fun c => if c = 1 then d else e, 1⟩, ?_⟩
    simpa [splitHom, splitMap, show splitFlip ≠ 1 by decide] using hg.symm
  · refine ⟨⟨fun c => if c = 1 then d else e, splitFlip⟩, ?_⟩
    simpa [splitHom, splitMap, show splitFlip ≠ 1 by decide] using hg.symm


variable {G : Type*} [Group G] [Finite G]

private theorem preserving_factors_form
    (D F : Subgroup G) (hD : IsSL2Two D) (hF : IsSL2Two F)
    (hcomm : D ≤ Subgroup.centralizer (F : Set G))
    (hcent : Subgroup.centralizer ((D ⊔ F : Subgroup G) : Set G) = ⊥)
    (g : G) (hgD : D.conjBy g = D) (hgF : F.conjBy g = F) :
    ∃ d : D, ∃ f : F, g = (d : G) * (f : G) := by
  have hgDn : g ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hgD
  have hgFn : g ∈ Subgroup.normalizer (F : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hgF
  obtain ⟨d, hd⟩ := sl2_normalizer_exists_inner D hD g hgDn
  have hdFn : (d : G) ∈ Subgroup.normalizer (F : Set G) :=
    Subgroup.centralizer_le_normalizer _ (hcomm d.property)
  obtain ⟨f, hf⟩ := sl2_normalizer_exists_inner F hF ((d : G)⁻¹ * g)
    ((Subgroup.normalizer (F : Set G)).mul_mem
      ((Subgroup.normalizer (F : Set G)).inv_mem hdFn) hgFn)
  have hfD : (f : G) ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hcomm ha) f f.property).symm
  have hboth : (f : G)⁻¹ * ((d : G)⁻¹ * g) ∈
      Subgroup.centralizer ((D ⊔ F : Subgroup G) : Set G) := by
    rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rcases ha with ha | ha
    · exact Subgroup.mem_centralizer_iff.mp ((Subgroup.centralizer (D : Set G)).mul_mem
        ((Subgroup.centralizer (D : Set G)).inv_mem hfD) hd) a ha
    · exact Subgroup.mem_centralizer_iff.mp hf a ha
  rw [hcent, Subgroup.mem_bot] at hboth
  refine ⟨d, f, ?_⟩
  calc
    g = (d : G) * (f : G) * ((f : G)⁻¹ * ((d : G)⁻¹ * g)) := by group
    _ = (d : G) * (f : G) := by rw [hboth, mul_one]

private theorem corrected_swap
    (D F : Subgroup G) (hD : IsSL2Two D) (hF : IsSL2Two F)
    (hcomm : D ≤ Subgroup.centralizer (F : Set G))
    (hdis : Disjoint D F)
    (hcent : Subgroup.centralizer ((D ⊔ F : Subgroup G) : Set G) = ⊥)
    (x : G) (hxD : D.conjBy x = F) (hxF : F.conjBy x = D) :
    ∃ t : G, t * t = 1 ∧ D.conjBy t = F ∧ F.conjBy t = D := by
  have hx2D : D.conjBy (x * x) = D := by rw [Subgroup.conjBy_mul, hxD, hxF]
  have hx2F : F.conjBy (x * x) = F := by rw [Subgroup.conjBy_mul, hxF, hxD]
  obtain ⟨d, f, hdf⟩ := preserving_factors_form D F hD hF hcomm hcent
    (x * x) hx2D hx2F
  have hdD : D.conjBy ((d : G)⁻¹) = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (D.inv_mem d.property))
  have hdF : F.conjBy ((d : G)⁻¹) = F :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _ (hcomm (D.inv_mem d.property)))
  let t := (d : G)⁻¹ * x
  have htD : D.conjBy t = F := by dsimp [t]; rw [Subgroup.conjBy_mul, hxD, hdF]
  have htF : F.conjBy t = D := by dsimp [t]; rw [Subgroup.conjBy_mul, hxF, hdD]
  have hxd : x * (d : G)⁻¹ * x⁻¹ ∈ F := by
    rw [← hxD]
    exact Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom (D.inv_mem d.property)
  have hdc : (d : G)⁻¹ * (x * (d : G)⁻¹ * x⁻¹) =
      (x * (d : G)⁻¹ * x⁻¹) * (d : G)⁻¹ :=
    (Subgroup.mem_centralizer_iff.mp (hcomm (D.inv_mem d.property)) _ hxd).symm
  have ht2F : t * t ∈ F := by
    have heq : t * t = (x * (d : G)⁻¹ * x⁻¹) * (f : G) := by
      calc
        t * t = (d : G)⁻¹ * (x * (d : G)⁻¹ * x⁻¹) * (x * x) := by dsimp [t]; group
        _ = (x * (d : G)⁻¹ * x⁻¹) * (d : G)⁻¹ * ((d : G) * (f : G)) := by rw [hdc, hdf]
        _ = (x * (d : G)⁻¹ * x⁻¹) * (f : G) := by group
    rw [heq]
    exact F.mul_mem hxd f.property
  have ht2D : t * t ∈ D := by
    have hc : t * (t * t) * t⁻¹ ∈ D := by
      rw [← htF]
      exact Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom ht2F
    convert hc using 1; group
  exact ⟨t, Subgroup.disjoint_def.mp hdis ht2D ht2F, htD, htF⟩

private theorem split_factor_data
    (D F : Subgroup G) (hD : IsSL2Two D) (hF : IsSL2Two F)
    (hcomm : D ≤ Subgroup.centralizer (F : Set G))
    (hdis : Disjoint D F)
    (hcent : Subgroup.centralizer ((D ⊔ F : Subgroup G) : Set G) = ⊥)
    (hperm : ∀ g, (D.conjBy g = D ∧ F.conjBy g = F) ∨
      (D.conjBy g = F ∧ F.conjBy g = D))
    (hswap : ∃ x, D.conjBy x = F) :
    ∃ t : G, t * t = 1 ∧ D.conjBy t = F ∧ t ∉ D ⊔ F ∧
      ∀ g : G, ∃ d e : D,
        g = (d : G) * (t * (e : G) * t⁻¹) ∨
        g = (d : G) * (t * (e : G) * t⁻¹) * t := by
  have hne : D ≠ F := by
    intro heq
    have hbot : D = ⊥ := by simpa [← heq] using hdis
    have hc := SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hD
    rw [hbot, Nat.card_eq_fintype_card] at hc
    simp at hc
  obtain ⟨x, hx⟩ := hswap
  have hxF : F.conjBy x = D := by
    rcases hperm x with hp | hs
    · exact False.elim (hne (hp.1.symm.trans hx))
    · exact hs.2
  obtain ⟨t, htt, htD, htF⟩ := corrected_swap D F hD hF hcomm hdis hcent x hx hxF
  have hFn : F ≤ Subgroup.normalizer (D : Set G) := by
    apply (Subgroup.le_centralizer_iff.mp hcomm).trans
    exact Subgroup.centralizer_le_normalizer _
  have htout : t ∉ D ⊔ F := by
    intro ht
    have htn := (sup_le Subgroup.le_normalizer hFn) ht
    have hfix := Subgroup.mem_normalizer_iff_map_conj_eq.mp htn
    exact hne (hfix.symm.trans htD)
  refine ⟨t, htt, htD, htout, ?_⟩
  intro g
  have hform (k : G) (hkD : D.conjBy k = D) (hkF : F.conjBy k = F) :
      ∃ d e : D, k = (d : G) * (t * (e : G) * t⁻¹) := by
    obtain ⟨d, f, heq⟩ := preserving_factors_form D F hD hF hcomm hcent k hkD hkF
    have hf : (f : G) ∈ D.conjBy t := htD.symm ▸ f.property
    obtain ⟨e, he, hef⟩ := Subgroup.mem_map.mp hf
    exact ⟨d, ⟨e, he⟩, by rw [heq]; congr 1; exact hef.symm⟩
  rcases hperm g with hp | hs
  · obtain ⟨d, e, he⟩ := hform g hp.1 hp.2
    exact ⟨d, e, Or.inl he⟩
  · have hgD : D.conjBy (g * t) = D := by rw [Subgroup.conjBy_mul, htD, hs.2]
    have hgF : F.conjBy (g * t) = F := by rw [Subgroup.conjBy_mul, htF, hs.1]
    obtain ⟨d, e, he⟩ := hform (g * t) hgD hgF
    refine ⟨d, e, Or.inr ?_⟩
    calc
      g = (g * t) * t := by rw [mul_assoc, htt, mul_one]
      _ = (d : G) * (t * (e : G) * t⁻¹) * t := by rw [he]

/-- Two commuting center-free complete SL₂(2) factors, faithfully permuted
by the ambient group with a nontrivial swap, form the standard wreath product. -/
public theorem wreath_of_two_sl2_factors
    (D F : Subgroup G) (hD : IsSL2Two D) (hF : IsSL2Two F)
    (hcomm : D ≤ Subgroup.centralizer (F : Set G))
    (hdis : Disjoint D F) [_hEn : (D ⊔ F).Normal]
    (hcent : Subgroup.centralizer ((D ⊔ F : Subgroup G) : Set G) = ⊥)
    (hperm : ∀ g, (D.conjBy g = D ∧ F.conjBy g = F) ∨
      (D.conjBy g = F ∧ F.conjBy g = D))
    (hswap : ∃ x, D.conjBy x = F) :
    Nonempty (G ≃* RegularWreathProduct
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2))) := by
  obtain ⟨t, htt, htD, htout, hform⟩ :=
    split_factor_data D F hD hF hcomm hdis hcent hperm hswap
  have hc (d e : D) : Commute (d : G) (t * (e : G) * t⁻¹) := by
    have he : t * (e : G) * t⁻¹ ∈ F := by
      rw [← htD]
      exact Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom e.property
    exact (Subgroup.mem_centralizer_iff.mp (hcomm d.property) _ he).symm
  obtain ⟨e⟩ := split_wreath_equiv D t htt hc (htD.symm ▸ hdis)
    (by simpa only [htD] using htout) hform
  obtain ⟨eD⟩ := hD
  exact ⟨e.trans (RegularWreathProduct.congr eD (MulEquiv.refl _))⟩

end Stellmacher
