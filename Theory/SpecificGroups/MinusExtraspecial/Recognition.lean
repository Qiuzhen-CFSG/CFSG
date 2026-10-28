module

public import Theory.SpecificGroups.MinusExtraspecial.Model
public import Theory.GroupTheory.PGroup.RankTwoExtraspecialThirtyTwo
public import Theory.GroupTheory.CentralProductEquivalence

/-!
# Recognition of the minus extraspecial model

The order-thirty-two factor decomposition is glued to the explicit
quaternion--dihedral model.  The two factor maps are aligned on the common
central involution before applying the central-product equivalence theorem.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, pp.389–390; the
quaternion–dihedral factors are supplied by RankTwoExtraspecialThirtyTwo.
-/

open Subgroup

namespace IsExtraspecial

private theorem quaternion_involutions (q : QuaternionGroup 2) :
    q * q = 1 → q = 1 ∨ q = .a 2 := by
  revert q
  decide

private theorem quaternion_a2_comm (q : QuaternionGroup 2) :
    .a 2 * q = q * .a 2 := by
  revert q
  decide

private theorem dihedral_central_elements (d : DihedralGroup 4) :
    (∀ x : DihedralGroup 4, d * x = x * d) → d = 1 ∨ d = .r 2 := by
  revert d
  decide

private theorem dihedral_r2_comm (d : DihedralGroup 4) :
    .r 2 * d = d * .r 2 := by
  revert d
  decide

/-- A rank-two extraspecial group of order thirty-two with the elementary-rank
bound is the concrete quaternion--dihedral model. -/
public theorem exists_mulEquiv_minusExtraspecial_model
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hP : Nat.card P = 32) :
    Nonempty (P ≃* _root_.MinusExtraspecial.Model) := by
  obtain ⟨U, V, ⟨eU⟩, ⟨eV⟩, hcomm, hgen, hI⟩ :=
    dihedral_quaternion_factors_of_card_thirty_two hrank hP
  let Q : Subgroup _root_.MinusExtraspecial.Model := _root_.MinusExtraspecial.quaternion.range
  let D : Subgroup _root_.MinusExtraspecial.Model := _root_.MinusExtraspecial.dihedral.range
  let qcod : QuaternionGroup 2 →* Q :=
    MonoidHom.codRestrict _root_.MinusExtraspecial.quaternion Q (fun q => ⟨q, rfl⟩)
  let dcod : DihedralGroup 4 →* D :=
    MonoidHom.codRestrict _root_.MinusExtraspecial.dihedral D (fun d => ⟨d, rfl⟩)
  have hqbij : Function.Bijective qcod := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      apply _root_.MinusExtraspecial.quaternion_injective
      exact congrArg Subtype.val hab
    · intro x
      rcases (MonoidHom.mem_range.mp x.property) with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      apply Subtype.ext
      exact hq
  have hdbij : Function.Bijective dcod := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      apply _root_.MinusExtraspecial.dihedral_injective
      exact congrArg Subtype.val hab
    · intro x
      rcases (MonoidHom.mem_range.mp x.property) with ⟨d, hd⟩
      refine ⟨d, ?_⟩
      apply Subtype.ext
      exact hd
  let eq : QuaternionGroup 2 ≃* Q := MulEquiv.ofBijective qcod hqbij
  let ed : DihedralGroup 4 ≃* D := MulEquiv.ofBijective dcod hdbij
  have hQD : Q ⊔ D = (⊤ : Subgroup _root_.MinusExtraspecial.Model) := by
    apply top_unique
    intro x hx
    rcases _root_.MinusExtraspecial.factors_generate x with ⟨q, d, hxd⟩
    have hq : _root_.MinusExtraspecial.quaternion q ∈ Q := ⟨q, rfl⟩
    have hd : _root_.MinusExtraspecial.dihedral d ∈ D := ⟨d, rfl⟩
    rw [← hxd]
    exact Subgroup.mul_mem_sup hq hd
  have hQDcomm : ∀ q : Q, ∀ d : D, Commute (q : _root_.MinusExtraspecial.Model) d := by
    intro q d
    rcases MonoidHom.mem_range.mp q.property with ⟨q', hq⟩
    rcases MonoidHom.mem_range.mp d.property with ⟨d', hd⟩
    simpa [← hq, ← hd] using _root_.MinusExtraspecial.factors_commute q' d'
  let W : Subgroup P := U ⊓ V
  have hW : Nat.card W = 2 := by simpa [W] using hI
  have hcommon_unique : ∀ x : P, x ∈ U → x ∈ V → x ≠ 1 →
      x = ((Classical.choose ((Nat.card_eq_two_iff' (1 : W)).mp hW) : W) : P) := by
    intro x hxU hxV hx1
    let w : W := ⟨x, hxU, hxV⟩
    have hw1 : w ≠ (1 : W) := by
      intro hw
      apply hx1
      exact congrArg Subtype.val hw
    have huniq := (Classical.choose_spec ((Nat.card_eq_two_iff' (1 : W)).mp hW)).2
    have hw := huniq w hw1
    exact congrArg Subtype.val hw
  let w : W := Classical.choose ((Nat.card_eq_two_iff' (1 : W)).mp hW)
  have hw1 : w ≠ (1 : W) := (Classical.choose_spec ((Nat.card_eq_two_iff' (1 : W)).mp hW)).1
  have hww : (w : P) * w = 1 := by
    have hww' : w * w = (1 : W) := by
      by_contra hne
      have heq : w * w = w := by
        simpa [w] using (Classical.choose_spec ((Nat.card_eq_two_iff' (1 : W)).mp hW)).2 (w * w) hne
      have : w = (1 : W) := by
        apply mul_right_cancel (b := w)
        simpa only [one_mul] using heq
      exact hw1 this
    exact congrArg Subtype.val hww'
  let wU : U := ⟨(w : P), w.property.1⟩
  let wV : V := ⟨(w : P), w.property.2⟩
  have hwU1 : wU ≠ (1 : U) := by
    intro h
    apply hw1
    apply Subtype.ext
    simpa [wU] using congrArg Subtype.val h
  have hwV1 : wV ≠ (1 : V) := by
    intro h
    apply hw1
    apply Subtype.ext
    simpa [wV] using congrArg Subtype.val h
  have hwVcentral : ∀ y : V, (wV : P) * y = y * wV := by
    intro y
    exact (Subgroup.mem_centralizer_iff.mp (hcomm y.property))
      (wU : P) wU.property
  let heZ : U ≃* Q := eU.trans eq
  let heL : V ≃* D := eV.trans ed
  have hcompat : ∀ z : U, ∀ l : V, (z : P) = (l : P) ↔
      (heZ z : MinusExtraspecial.Model) = (heL l : MinusExtraspecial.Model) := by
    intro z l
    constructor
    · intro hzl
      by_cases hz : z = 1
      · have hl : l = 1 := by
          apply Subtype.ext
          simpa [hz] using hzl.symm
        simp [hz, hl]
      · have hxU : (z : P) ∈ U := z.property
        have hxV : (z : P) ∈ V := by rw [hzl]; exact l.property
        have hzw : (z : P) = (w : P) := hcommon_unique z hxU hxV (by simpa using hz)
        have hzl' : l = wV := by
          apply Subtype.ext
          simpa [hzw, wV] using hzl.symm
        have hzz' : z = wU := by
          apply Subtype.ext
          exact hzw
        subst z
        subst l
        have hq2 : eU wU = 1 ∨ eU wU = .a 2 :=
          quaternion_involutions (eU wU) (by simpa [pow_two, hww] using congrArg (fun x : U => eU x) (show wU * wU = 1 by apply Subtype.ext; simpa [pow_two, hww]))
        have hq : eU wU = .a 2 := hq2.resolve_left (by intro h; exact hwU1 (eU.injective (by simpa using h)))
        have hdcent : ∀ d : DihedralGroup 4, eV wV * d = d * eV wV := by
          intro d
          rcases eV.surjective d with ⟨y, rfl⟩
          have hy : wV * y = y * wV := by
            apply Subtype.ext
            exact hwVcentral y
          simpa only [map_mul] using congrArg eV hy
        have hd2 : eV wV = 1 ∨ eV wV = .r 2 := dihedral_central_elements (eV wV) hdcent
        have hd : eV wV = .r 2 := hd2.resolve_left (by intro h; exact hwV1 (eV.injective (by simpa using h)))
        change _root_.MinusExtraspecial.quaternion (eU wU) =
          _root_.MinusExtraspecial.dihedral (eV wV)
        rw [hq, hd]
        decide
    · intro htarget
      have htarget' : _root_.MinusExtraspecial.quaternion (eU z) =
          _root_.MinusExtraspecial.dihedral (eV l) := by
        have htarget'' : ((eq (eU z) : Q) : _root_.MinusExtraspecial.Model) =
            ((ed (eV l) : D) : _root_.MinusExtraspecial.Model) := by
          simpa [heZ, heL] using htarget
        change _root_.MinusExtraspecial.quaternion (eU z) =
          _root_.MinusExtraspecial.dihedral (eV l) at htarget''
        exact htarget''
      rcases (_root_.MinusExtraspecial.factors_overlap (eU z) (eV l)).mp htarget' with h | h
      · have hz : z = 1 := eU.injective (by simpa only [map_one] using h.1)
        have hl : l = 1 := eV.injective (by simpa only [map_one] using h.2)
        rw [hz, hl]
        rfl
      · have hzUcent : ∀ u : U, (z : P) * u = u * z := by
          intro u
          have huq : eU z * eU u = eU u * eU z := by
            rw [h.1]
            exact quaternion_a2_comm (eU u)
          have hprod : eU (z * u) = eU (u * z) := by simpa only [map_mul] using huq
          exact congrArg Subtype.val (eU.injective hprod)
        have hzVcent : ∀ v : V, (z : P) * v = v * z := by
          intro v
          exact (Subgroup.mem_centralizer_iff.mp (hcomm v.property)) z z.property
        have hzcenter : (z : P) ∈ center P := by
          apply Subgroup.mem_center_iff.mpr
          intro y
          have hleU : U ≤ centralizer ({(z : P)} : Set P) := by
            intro u hu
            rw [Subgroup.mem_centralizer_iff]
            intro t ht
            have : t = (z : P) := by simpa using ht
            subst t
            exact hzUcent ⟨u, hu⟩
          have hleV : V ≤ centralizer ({(z : P)} : Set P) := by
            intro v hv
            rw [Subgroup.mem_centralizer_iff]
            intro t ht
            have : t = (z : P) := by simpa using ht
            subst t
            exact hzVcent ⟨v, hv⟩
          have hle : U ⊔ V ≤ centralizer ({(z : P)} : Set P) := sup_le hleU hleV
          have hy := hle (hgen ▸ (show y ∈ (⊤ : Subgroup P) by trivial))
          exact ((Subgroup.mem_centralizer_iff.mp hy) (z : P) (by simp)).symm
        have hlVcent : ∀ v : V, (l : P) * v = v * l := by
          intro v
          have hvd : eV l * eV v = eV v * eV l := by
            rw [h.2]
            exact dihedral_r2_comm (eV v)
          have hprod : eV (l * v) = eV (v * l) := by simpa only [map_mul] using hvd
          exact congrArg Subtype.val (eV.injective hprod)
        have hlUcent : ∀ u : U, (l : P) * u = u * l := by
          intro u
          exact ((Subgroup.mem_centralizer_iff.mp (hcomm l.property)) u u.property).symm
        have hlcenter : (l : P) ∈ center P := by
          apply Subgroup.mem_center_iff.mpr
          intro y
          have hleU : U ≤ centralizer ({(l : P)} : Set P) := by
            intro u hu
            rw [Subgroup.mem_centralizer_iff]
            intro t ht
            have : t = (l : P) := by simpa using ht
            subst t
            exact hlUcent ⟨u, hu⟩
          have hleV : V ≤ centralizer ({(l : P)} : Set P) := by
            intro v hv
            rw [Subgroup.mem_centralizer_iff]
            intro t ht
            have : t = (l : P) := by simpa using ht
            subst t
            exact hlVcent ⟨v, hv⟩
          have hle : U ⊔ V ≤ centralizer ({(l : P)} : Set P) := sup_le hleU hleV
          have hy := hle (hgen ▸ (show y ∈ (⊤ : Subgroup P) by trivial))
          exact ((Subgroup.mem_centralizer_iff.mp hy) (l : P) (by simp)).symm
        have hz1 : (z : P) ≠ 1 := by
          intro hz
          have hz' : z = 1 := Subtype.ext hz
          have hh : (1 : QuaternionGroup 2) = .a 2 := by simpa [hz'] using h.1
          exact (by decide : (1 : QuaternionGroup 2) ≠ .a 2) hh
        have hl1 : (l : P) ≠ 1 := by
          intro hl
          have hl' : l = 1 := Subtype.ext hl
          have hh : (1 : DihedralGroup 4) = .r 2 := by simpa [hl'] using h.2
          exact (by decide : (1 : DihedralGroup 4) ≠ .r 2) hh
        have hc := (Nat.card_eq_two_iff' (1 : center P)).mp (IsExtraspecial.center_order_p 2 P)
        have uz : (⟨(z : P), hzcenter⟩ : center P) = Classical.choose hc :=
          (Classical.choose_spec hc).2 ⟨(z : P), hzcenter⟩ (by simpa using hz1)
        have ul : (⟨(l : P), hlcenter⟩ : center P) = Classical.choose hc :=
          (Classical.choose_spec hc).2 ⟨(l : P), hlcenter⟩ (by simpa using hl1)
        exact congrArg Subtype.val (uz.trans ul.symm)
  obtain ⟨e, _, _⟩ := exists_mulEquiv_of_central_products U V Q D
    (by intro u v; exact (Subgroup.mem_centralizer_iff.mp (hcomm v.property)) u u.property)
    hQDcomm hgen hQD heZ heL hcompat
  exact ⟨e⟩

end IsExtraspecial
