module
public import Theory.GroupTheory.InvolutionTransferResidual
public import Theory.GroupTheory.PResidual.CentralSylowCharacter
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.SylowNormalRestriction
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Data.ZMod.Basic

/-!
# Removing a dihedral factor from a two-residual

For a marked Sylow D₈ × D₈, suppose the second factor lies in O²(H), the
first central involution is central in H, and first-factor reflections have
no Sylow fusion to rotations. Transfer through the first rotation-index-two
character excludes those reflections. The first coordinates of the residual
Sylow are therefore rotations, giving a cyclic-four character. Central
transfer on O²(H), which is itself two-perfect, then excludes its central
involution and hence every nontrivial first coordinate. The second factor is
therefore the literal residual Sylow.

The final lemma derives the required reflection fusion from the original
ambient involution class being exactly the two coordinate axes: multiplying
by the fixed central involution rules out fusion to the second axis.

Source: Aschbacher–Smith 13.9.5, printed p.971. This is the transfer argument
needed by its final ambient-fusion contradiction; no residual recognition
or classification theorem is assumed.
-/


@[expose] public noncomputable section
open Subgroup
namespace DihedralProductTransfer
abbrev D := DihedralGroup 4
abbrev C2 := Multiplicative (ZMod 2)
abbrev C4 := Multiplicative (ZMod 4)

def orientation : D →* C2 where
  toFun x := match x with | .r _ => 1 | .sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by decide +kernel

def rotationCoordinate : D → C4
  | .r i => Multiplicative.ofAdd i
  | .sr i => Multiplicative.ofAdd i

private theorem orientation_rot (i : ZMod 4) : orientation (.r i) = 1 := rfl
private theorem orientation_reflection (i : ZMod 4) : orientation (.sr i) ≠ 1 := by change (Multiplicative.ofAdd (1:ZMod 2)) ≠ 1;decide
private theorem reflection_order (i : ZMod 4) : orderOf (DihedralGroup.sr i : D) = 2 :=
  orderOf_eq_prime (by simpa only [pow_two] using DihedralGroup.sr_mul_self i) (by intro h; cases h)
private theorem rotationCoordinate_mul (a b : D) (ha : orientation a = 1)
    (hb : orientation b = 1) : rotationCoordinate (a*b) = rotationCoordinate a * rotationCoordinate b :=
  (by decide +kernel : ∀ a b:D, orientation a=1 → orientation b=1 →
    rotationCoordinate (a*b)=rotationCoordinate a*rotationCoordinate b) a b ha hb
private theorem rotation_power (a : D) (ha : orientation a=1) (hne : a≠1) :
    ∃ n : Fin 4, a^n.val=DihedralGroup.r 2 :=
  (by decide +kernel : ∀ a:D, orientation a=1 → a≠1 →
    ∃ n:Fin 4,a^n.val=DihedralGroup.r 2) a ha hne

variable {H : Type*} [Group H] [Finite H]

/-- The first dihedral coordinate disappears from the two-residual when its
reflections have no fusion to the other factor and its central involution is
ambient central. The second factor lies in the actual residual. -/
theorem first_eq_one_of_residual
    (S : Sylow 2 H) (e : S ≃* D×D)
    (hc : (e.symm (DihedralGroup.r 2,1) : H) ∈ center H)
    (hfusion : ∀ (i : ZMod 4) (y : S),
      IsConj (e.symm (DihedralGroup.sr i,1) : H) (y : H) →
      ∃ j : ZMod 4, (e y).1 = DihedralGroup.sr j)
    (hsecond : ∀ b : D, (e.symm (1,b) : H) ∈ pResidual 2 H)
    (s : S) (hs : (s : H) ∈ pResidual 2 H) : (e s).1 = 1 := by
  let R := pResidual 2 H
  let f : S →* D := (MonoidHom.fst D D).comp e.toMonoidHom
  let chi : S →* C2 := orientation.comp f
  have hreflection (i : ZMod 4) : (e.symm (DihedralGroup.sr i,1) : H) ∉ R := by
    apply S.not_mem_twoResidual_of_nonfusion_character chi (by simp [C2])
      (e.symm (DihedralGroup.sr i,1))
    · rw [e.symm.orderOf_eq,Prod.orderOf_mk,reflection_order,orderOf_one]
      decide
    · intro y hy
      obtain ⟨j,hj⟩ := hfusion i y hy
      change orientation (e y).1 ≠ 1
      rw [hj]
      exact orientation_reflection j
  have hpure (x : S) (hx : (x:H)∈R) :
      (e.symm ((e x).1,1) : H)∈R := by
    have hh := R.mul_mem hx (R.inv_mem (hsecond (e x).2))
    have he : x * (e.symm (1,(e x).2))⁻¹ = e.symm ((e x).1,1) := by
      apply e.injective
      apply Prod.ext <;> simp
    simpa only [← Subgroup.coe_mul, ← Subgroup.coe_inv, he] using hh
  have hrot (x : S) (hx : (x:H)∈R) : orientation (f x)=1 := by
    have hp := hpure x hx
    change orientation (e x).1=1
    cases he : (e x).1 with
    | r i => exact orientation_rot i
    | sr i => exact (hreflection i (he ▸ hp)).elim
  obtain ⟨Q,hQ⟩ := S.exists_sylow_map_eq_inf_of_normal R
  let j : Q →* S := {
    toFun q := ⟨((q : R) : H),(hQ ▸ mem_map_of_mem R.subtype q.property).1⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let phi : Q →* C4 := {
    toFun q := rotationCoordinate (f (j q))
    map_one' := by simp only [map_one];rfl
    map_mul' a b := by
      rw [map_mul,map_mul]
      exact rotationCoordinate_mul _ _ (hrot _ (a : R).property) (hrot _ (b : R).property) }
  have hcenter_not : (e.symm (DihedralGroup.r 2,1) : H)∉R := by
    intro hr
    have ht : (e.symm (DihedralGroup.r 2,1) : H)∈ (Q : Subgroup R).map R.subtype := by
      rw [hQ]
      exact ⟨(e.symm _).property,hr⟩
    obtain ⟨q,hq,hqe⟩ := ht
    change (q:H) = (e.symm (DihedralGroup.r 2,1) : H) at hqe
    let qq : Q := ⟨q,hq⟩
    have hcen : (qq : R) ∈ center R := by
      apply mem_center_iff.mpr
      intro a
      apply Subtype.ext
      have hh := (mem_center_iff.mp hc) (a:H)
      change (a:H) * (q:H) = (q:H) * (a:H)
      rw [hqe]
      exact hh
    have hR : pResidual 2 R = ⊤ := (pResidual_eq_top_iff 2 R).mpr (isPPerfect_pResidual 2)
    have hh := Q.character_eq_one_of_central_mem_pResidual phi
      (IsPGroup.of_card (p:=2) (n:=2) (by simp [C4])) qq hcen (hR ▸ mem_top q)
    have hj : j qq = e.symm (DihedralGroup.r 2,1) := Subtype.ext hqe
    have hn : rotationCoordinate (DihedralGroup.r 2) ≠ 1 := by decide
    apply hn
    change rotationCoordinate (f (j qq))=1 at hh
    simpa only [hj,f,MonoidHom.comp_apply,MonoidHom.coe_fst,MulEquiv.coe_toMonoidHom,
      e.apply_symm_apply] using hh
  by_contra hn
  obtain ⟨n,hn⟩ := rotation_power (e s).1 (hrot s hs) hn
  apply hcenter_not
  have hp := R.pow_mem (hpure s hs) n.val
  have he : (e.symm ((e s).1,1))^n.val=e.symm (DihedralGroup.r 2,1) := by
    rw [← map_pow]
    simp only [Prod.pow_mk,hn,one_pow]
  simpa only [← Subgroup.coe_pow,he] using hp
/-- The second factor is the literal image of a Sylow subgroup of the residual. -/
theorem exists_residual_sylow
    (S : Sylow 2 H) (e : S ≃* D×D)
    (hc : (e.symm (DihedralGroup.r 2,1) : H) ∈ center H)
    (hfusion : ∀ (i : ZMod 4) (y : S),
      IsConj (e.symm (DihedralGroup.sr i,1) : H) (y : H) →
      ∃ j : ZMod 4, (e y).1 = DihedralGroup.sr j)
    (hsecond : ∀ b : D, (e.symm (1,b) : H) ∈ pResidual 2 H) :
    ∃ Q : Sylow 2 (pResidual 2 H),
      (Q : Subgroup (pResidual 2 H)).map (pResidual 2 H).subtype =
        ((⊥ : Subgroup D).prod ⊤).map ((S : Subgroup H).subtype.comp e.symm.toMonoidHom) := by
  obtain ⟨Q,hQ⟩ := S.exists_sylow_map_eq_inf_of_normal (pResidual 2 H)
  refine ⟨Q,hQ.trans ?_⟩
  apply le_antisymm
  · intro x hx
    let y : S := ⟨x,hx.1⟩
    have hy := first_eq_one_of_residual S e hc hfusion hsecond y hx.2
    refine ⟨e y,⟨hy,mem_top _⟩,?_⟩
    change (e.symm (e y) : H)=x
    simp [y]
  · rintro x ⟨⟨a,b⟩,⟨ha,_⟩,rfl⟩
    have ha : a=1 := ha
    subst a
    exact ⟨(e.symm (1,b)).property,hsecond b⟩

private theorem conjugate_order {A : Type*} [Group A] {x y : A}
    (h : IsConj x y) : orderOf x=orderOf y := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq x).symm

private theorem reflection_pair_order (i : ZMod 4) :
    orderOf (DihedralGroup.sr i, (1:D))=2 := by
  rw [Prod.orderOf_mk,reflection_order,orderOf_one]
  decide

private theorem central_reflection_order (i : ZMod 4) :
    orderOf ((DihedralGroup.r 2 : D)*DihedralGroup.sr i, (1:D))=2 := by
  rw [DihedralGroup.r_mul_sr]
  exact reflection_pair_order _

private theorem reflection_of_square (a : D) (h2 : a^2=1) (h1 : a≠1)
    (hc : a≠DihedralGroup.r 2) : ∃i:ZMod 4,a=DihedralGroup.sr i :=
  (by decide +kernel : ∀a:D,a^2=1 → a≠1 → a≠DihedralGroup.r 2 →
    ∃i:ZMod 4,a=DihedralGroup.sr i) a h2 h1 hc

omit [Finite H] in
/-- The original axis description of an ambient involution class forces the
reflection fusion needed by the transfer theorem. -/
theorem reflection_fusion_of_axes {G : Type*} [Group G]
    (k : H →* G) (S : Sylow 2 H) (e : S ≃* D×D)
    (hc : (e.symm (DihedralGroup.r 2,1) : H) ∈ center H)
    (haxes : ∀ x:S, orderOf x=2 →
      (IsConj (k (e.symm (DihedralGroup.r 2,1))) (k x) ↔
        (e x).1=1 ∨ (e x).2=1))
    (i : ZMod 4) (y:S) (h : IsConj (e.symm (DihedralGroup.sr i,1) : H) (y:H)) :
    ∃j:ZMod 4,(e y).1=DihedralGroup.sr j := by
  let c : S := e.symm (DihedralGroup.r 2,1)
  let a : S := e.symm (DihedralGroup.sr i,1)
  have ha : orderOf a=2 := (e.symm.orderOf_eq _).trans (reflection_pair_order i)
  have hca : orderOf (c*a)=2 := by
    rw [← e.orderOf_eq (c*a),map_mul]
    simpa only [c,a,e.apply_symm_apply,Prod.mk_mul_mk,mul_one] using central_reflection_order i
  have hy : orderOf y=2 := (orderOf_coe y).symm.trans
    ((conjugate_order h).symm.trans ((orderOf_coe a).trans ha))
  have hcy : IsConj ((c*a:S):H) ((c*y:S):H) := by
    obtain ⟨g,hg⟩ := isConj_iff.mp h
    refine isConj_iff.mpr ⟨g,?_⟩
    change g*((c:H)*(a:H))*g⁻¹=(c:H)*(y:H)
    calc
      _ = (g*(c:H))*((a:H)*g⁻¹) := by group
      _ = ((c:H)*g)*((a:H)*g⁻¹) := by rw [mem_center_iff.mp hc g]
      _ = (c:H)*(g*(a:H)*g⁻¹) := by group
      _ = (c:H)*(y:H) := by rw [hg]
  have hcyo : orderOf (c*y)=2 := (orderOf_coe (c*y)).symm.trans
    ((conjugate_order hcy).symm.trans ((orderOf_coe (c*a)).trans hca))
  have hay : IsConj (k c) (k y) :=
    ((haxes a ha).mpr (Or.inr (by simp [a]))).trans (k.map_isConj h)
  have hcay : IsConj (k c) (k (c*y)) :=
    ((haxes (c*a) hca).mpr (Or.inr (by simp [c,a]))).trans (k.map_isConj hcy)
  have hb : (e y).2=1 := by
    rcases (haxes y hy).mp hay with hfirst|hsecond
    · rcases (haxes (c*y) hcyo).mp hcay with hfirst'|hsecond'
      · have hh : (DihedralGroup.r (2:ZMod 4):D)=1 := by simpa [c,hfirst] using hfirst'
        exact (by decide : (DihedralGroup.r (2:ZMod 4):D)≠1) hh |>.elim
      · simpa [c] using hsecond'
    · exact hsecond
  apply reflection_of_square
  · let f : S →* D := (MonoidHom.fst D D).comp e.toMonoidHom
    have hh := congrArg f (hy ▸ pow_orderOf_eq_one y)
    rw [map_pow,map_one] at hh
    exact hh
  · intro hf
    have hey : e y=1 := Prod.ext hf hb
    have hy1 : y=1 := e.injective (hey.trans (map_one e).symm)
    have ho := hy
    rw [hy1,orderOf_one] at ho
    omega
  · intro hf
    have hyc : y=c := e.injective (by apply Prod.ext <;> simp [c,hf,hb])
    have hh : (a:H)=(c:H) := (hyc ▸ h).eq_of_right_mem_center hc
    have he := congrArg (fun q:S=>(e q).1) (Subtype.ext hh)
    have hn : (DihedralGroup.sr i:D)≠DihedralGroup.r 2 := by intro hh;cases hh
    exact hn (by simpa only [a,c,e.apply_symm_apply] using he)

end DihedralProductTransfer
