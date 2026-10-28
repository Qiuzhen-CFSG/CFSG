module

public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerCoreAction
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerQuotientCard
public import Theory.GroupAction.OddTransitiveTwoCore
public import Theory.GroupAction.SixteenOddComplements.ThirtySix

/-!
# Recognition of the original plane normalizer quotient

The nine root-class elements span A₂ because a proper subgroup of the
elementary sixteen has at most eight elements. Their permutation action
therefore has kernel C_G(A₂)=A₂. Transitivity on this odd set makes the
two-core of N_G(A₂)/A₂ trivial. Its computed order36 and the elementary
four image of R now give S₃ × S₃ by the reduced degree-four recognition.

Source: Aschbacher--Smith F.5.4(4), printed p.301. The action and quotient
maps are the original ambient conjugation maps throughout.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (t : G) (hf : FusionFacts c i z t)

def planeRootClass : Set G := {x | x ∈ A c i true ∧ IsConj (rootElement c i z) x}

omit [Finite G] in
include hf in
theorem planeRootClass_card : Nat.card (planeRootClass c i z) = 9 := by
  let e : planeRootClass c i z ≃ classIntersection (rootElement c i z) (A c i true) := {
    toFun := fun x => ⟨⟨x.val,x.property.1⟩,x.property.2⟩
    invFun := fun x => ⟨x.val.val,x.val.property,x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans hf.root_class_A_plane

include hf in
theorem planeRootClass_closure : closure (planeRootClass c i z) = A c i true := by
  let S := closure (planeRootClass c i z)
  have hSA : S ≤ A c i true := (closure_le _).mpr fun _ hx => hx.1
  let j : planeRootClass c i z → S := fun x => ⟨x.val,subset_closure x.property⟩
  have hj : Function.Injective j := fun x y he => Subtype.ext (congrArg (fun a : S => a.val) he)
  have hlarge : 9 ≤ Nat.card S := by
    have hh := Nat.card_le_card_of_injective j hj
    rwa [planeRootClass_card c i z t hf] at hh
  have hd : Nat.card S ∣ 16 := hf.A_card true ▸ card_dvd_of_le hSA
  have hc : Nat.card S = 16 :=
    (Nat.eq_of_dvd_of_lt_two_mul (by decide : 16 ≠ 0) hd (by omega)).symm
  exact eq_of_le_of_card_ge hSA (by rw [hf.A_card,hc])

def planeRootAction : normalizer (A c i true : Set G) →* Equiv.Perm (planeRootClass c i z) where
  toFun g := {
    toFun := fun x => ⟨g.val*x.val*g.val⁻¹,
      (mem_normalizer_iff.mp g.property x.val).mp x.property.1,
      x.property.2.trans (isConj_iff.mpr ⟨g.val,rfl⟩)⟩
    invFun := fun x => ⟨g.val⁻¹*x.val*g.val,
      (mem_normalizer_iff''.mp g.property x.val).mp x.property.1,
      x.property.2.trans (isConj_iff.mpr ⟨g.val⁻¹,by simp⟩)⟩
    left_inv := by intro x; apply Subtype.ext; change g.val⁻¹*(g.val*x.val*g.val⁻¹)*g.val=x.val; group
    right_inv := by intro x; apply Subtype.ext; change g.val*(g.val⁻¹*x.val*g.val)*g.val⁻¹=x.val; group }
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change 1*x.val*1⁻¹=x.val
    simp
  map_mul' := by
    intro g k
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (g.val*k.val)*x.val*(g.val*k.val)⁻¹=g.val*(k.val*x.val*k.val⁻¹)*g.val⁻¹
    group

include hf in
theorem planeRootAction_ker : (planeRootAction c i z).ker =
    (A c i true).subgroupOf (normalizer (A c i true : Set G)) := by
  ext g
  change planeRootAction c i z g=1 ↔ g.val ∈ A c i true
  constructor
  · intro hg
    have hc : g.val ∈ centralizer (planeRootClass c i z) := by
      intro x hx
      have he := congrArg (fun p : Equiv.Perm (planeRootClass c i z) => (p ⟨x,hx⟩).val) hg
      change g.val*x*g.val⁻¹=x at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    rw [←centralizer_closure,planeRootClass_closure c i z t hf,
      A_self_centralizer c i z t hf true] at hc
    exact hc
  · intro hg
    have hc : g.val ∈ centralizer (A c i true : Set G) := by
      rw [A_self_centralizer c i z t hf true]
      exact hg
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change g.val*x.val*g.val⁻¹=x.val
    rw [←mem_centralizer_iff.mp hc x.val x.property.1,mul_inv_cancel_right]

def planeNormalizerRootAction : normalizerQuotient c i true →*
    Equiv.Perm (planeRootClass c i z) :=
  QuotientGroup.lift _ (planeRootAction c i z) (planeRootAction_ker c i z t hf).symm.le

theorem planeNormalizerRootAction_mk_apply
    (g : normalizer (A c i true : Set G)) (x : planeRootClass c i z) :
    (planeNormalizerRootAction c i z t hf
      (QuotientGroup.mk' ((A c i true).subgroupOf (normalizer (A c i true : Set G))) g) x).val =
      g.val*x.val*g.val⁻¹ := rfl

theorem planeNormalizerRootAction_injective :
    Function.Injective (planeNormalizerRootAction c i z t hf) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  exact (planeRootAction_ker c i z t hf).symm

include hf in
/-- Root transitivity makes the literal plane quotient two-reduced. -/
theorem normalizer_plane_twoCore_of_transitive
    (ht : ∀ x ∈ A c i true, IsConj (rootElement c i z) x →
      ∃ n ∈ normalizer (A c i true : Set G), MulAut.conj n (rootElement c i z) = x) :
    pCore 2 (normalizerQuotient c i true) = ⊥ := by
  apply (planeNormalizerRootAction c i z t hf).twoCore_eq_bot_of_transitive_odd
    (planeNormalizerRootAction_injective c i z t hf)
    (by rw [planeRootClass_card c i z t hf]; decide)
  intro x y
  obtain ⟨nx,hnx,hx⟩ := ht x.val x.property.1 x.property.2
  obtain ⟨ny,hny,hy⟩ := ht y.val y.property.1 y.property.2
  let n : normalizer (A c i true : Set G) :=
    ⟨ny*nx⁻¹,mul_mem hny (inv_mem hnx)⟩
  refine ⟨QuotientGroup.mk' ((A c i true).subgroupOf (normalizer (A c i true : Set G))) n,?_⟩
  apply Subtype.ext
  rw [planeNormalizerRootAction_mk_apply]
  change (ny*nx⁻¹)*x.val*(ny*nx⁻¹)⁻¹=y.val
  rw [← hx,← hy]
  simp only [MulAut.conj_apply]
  group

include hf in
/-- The exact original plane normalizer quotient is S₃ × S₃. -/
theorem normalizer_plane_quotient_of_transitive (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R : Subgroup (C c i)))
    (ht : ∀ x ∈ A c i true, IsConj (rootElement c i z) x →
      ∃ n ∈ normalizer (A c i true : Set G), MulAut.conj n (rootElement c i z) = x)
    (hl : M c i false ⊓ normalizer (A c i true : Set G) = Tcentralizer c i t) :
    Nonempty (normalizerQuotient c i true ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  let := hf.A_elementary true
  obtain ⟨P,hPe,hPc⟩ := normalizer_quotient_has_elementary_four c i z t hf R hR true
  let := hPe
  exact SixteenOddComplements.equiv_of_reduced_thirty_six (hf.A_card true)
    (normalizerCoreAction c i z t hf true) (normalizerCoreAction_injective c i z t hf true)
    (normalizer_plane_quotient_card_of_transitive c i z t hf ht hl)
    (normalizer_plane_twoCore_of_transitive c i z t hf ht) P hPc

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
