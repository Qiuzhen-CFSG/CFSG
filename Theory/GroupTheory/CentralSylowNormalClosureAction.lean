module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# The two-core of a central Sylow normal-closure action

Let `W` centralize a supplied Sylow two-subgroup `T`, and let `V` be the
normal closure of `W`.  The preimage of the image two-core in the conjugation
action on `V` has quotient a two-group over the action kernel.  Sylow
supplementation therefore writes that preimage as its intersection with `T`
times the kernel.  Both factors are centralized by `W`; normality then makes
the whole normal closure `V` centralize the preimage, so the image two-core
acts trivially and is zero.  This is the normal-closure action argument in
Janko--Thompson, *Math. Z.* 113 (1970), Lemma 3.1, p. 387.
-/

@[expose] public section

open scoped Pointwise

/-- The conjugation action on the normal closure has trivial image two-core. -/
public theorem pCore_range_conjNormal_normalClosure_eq_bot
    {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (W : Subgroup H) (_hWT : W ≤ (T : Subgroup H))
    (hcentral : W ≤ Subgroup.centralizer (T : Set H)) :
    pCore 2 (MulAut.conjNormal (H := Subgroup.normalClosure (W : Set H))).range = ⊥ := by
  let V : Subgroup H := Subgroup.normalClosure (W : Set H)
  let rho : H →* MulAut V := MulAut.conjNormal
  let action : H →* rho.range := rho.rangeRestrict
  let C : Subgroup rho.range := pCore 2 rho.range
  let D : Subgroup H := C.comap action
  let rhoD : D →* rho.range := action.domRestrict D
  have hrhoDker : rhoD.ker = action.ker.subgroupOf D := by
    ext x
    simp [rhoD, Subgroup.mem_subgroupOf]
  have hrhoDrange : rhoD.range = C := by
    ext x
    constructor
    · rintro ⟨d, rfl⟩
      exact d.property
    · intro hx
      rcases x.property with ⟨h, hh⟩
      have ha : action h = x := by
        apply Subtype.ext
        exact hh
      refine ⟨⟨h, ?_⟩, ?_⟩
      · change action h ∈ C
        rw [ha]
        exact hx
      exact ha
  have hquot : IsPGroup 2 (D ⧸ rhoD.ker) := by
    let e := QuotientGroup.quotientKerEquivRange rhoD
    have he : IsPGroup 2 rhoD.range := by
      rw [hrhoDrange]
      exact pCore_isPGroup (p := 2) (G := rho.range)
    exact he.of_equiv e.symm
  obtain ⟨Q, hQ⟩ := T.exists_subgroupOf_eq_of_normal D
  have hsup : (Q : Subgroup D) ⊔ rhoD.ker = ⊤ := by
    exact Sylow.sup_eq_top_of_quotient_isPGroup Q rhoD.ker hquot
  have hDprod : D = (Q : Subgroup D).map D.subtype ⊔ action.ker := by
    have hmap := congrArg (Subgroup.map D.subtype) hsup
    have htopmap : (⊤ : Subgroup D).map D.subtype = D := by
      apply le_antisymm
      · exact Subgroup.map_subtype_le _
      · intro x hx
        exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
    rw [hrhoDker, htopmap, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le (by
        intro x hx
        change action x ∈ C
        rw [hx]
        exact C.one_mem)] at hmap
    exact hmap.symm
  have hWcentD : W ≤ Subgroup.centralizer (D : Set H) := by
    intro w hw d hd
    have hd' : d ∈ (Q : Subgroup D).map D.subtype ⊔ action.ker := by
      rw [← hDprod]
      exact hd
    obtain ⟨q, hq, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hd'
    obtain ⟨qD, hqD, rfl⟩ := hq
    have hqT : (qD : H) ∈ (T : Subgroup H) := by
      rw [hQ] at hqD
      exact hqD
    have hqw : (qD : H) * w = w * (qD : H) :=
      Subgroup.mem_centralizer_iff.mp (hcentral hw) (qD : H) hqT
    have hkact : action k = 1 := MonoidHom.mem_ker.mp hk
    have hk' : rho k = 1 := Subtype.ext_iff.mp hkact
    have hkw : (k : H) * w = w * (k : H) := by
      have hh : MulAut.conjNormal k ⟨w, Subgroup.le_normalClosure hw⟩ =
          ⟨w, Subgroup.le_normalClosure hw⟩ := by
        change rho k ⟨w, Subgroup.le_normalClosure hw⟩ = _
        rw [hk', MulAut.one_apply]
      have hh' := congrArg Subtype.val hh
      rw [MulAut.conjNormal_apply] at hh'
      calc
        (k : H) * w = ((k : H) * w * (k : H)⁻¹) * k := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
        _ = w * k := by rw [hh']
    calc
      (qD : H) * k * w = (qD : H) * (k * w) := by rw [mul_assoc]
      _ = (qD : H) * (w * k) := by rw [hkw]
      _ = ((qD : H) * w) * k := by rw [mul_assoc]
      _ = (w * (qD : H)) * k := by rw [hqw]
      _ = w * ((qD : H) * k) := by rw [mul_assoc]
  have hVcentD : V ≤ Subgroup.centralizer (D : Set H) :=
    Subgroup.normalClosure_le_normal hWcentD
  change C = ⊥
  apply bot_unique
  intro x hx
  obtain ⟨h, rfl⟩ := rho.rangeRestrict_surjective x
  have hd : h ∈ D := hx
  have hfix : rho h = 1 := by
    apply MulEquiv.ext
    intro v
    change MulAut.conjNormal h v = v
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hv : (v : H) ∈ V := v.property
    have hcomm := Subgroup.mem_centralizer_iff.mp (hVcentD hv) h hd
    calc
      h * (v : H) * h⁻¹ = ((v : H) * h) * h⁻¹ := by rw [hcomm]
      _ = (v : H) * (h * h⁻¹) := by rw [mul_assoc]
      _ = (v : H) := by rw [mul_inv_cancel, mul_one]
  have hxone : action h = 1 := by
    apply Subtype.ext
    exact hfix
  exact hxone
