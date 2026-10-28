module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.CyclicLocalization.SmallModule
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.CyclicLocalization.Layer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.LinearActions

/-!
# Transporting small invariant subspaces to the actual group layer

Conjugation on an elementary normal subgroup centralized by the projection
kernel descends to the actual SL3(2) quotient. The given natural coordinates
identify its Z-subgroup, and component commutators give the trivial quotient
action. No coordinates on the subgroup being localized are assumed.

Source: MS93, printed p.883, the cyclic localization before (1.7)(i).
-/
public section
open Subgroup Representation Representation.OneCohomology
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.CyclicLocalization
open RankOnePairing

/-- Localization in an actual elementary group extension with its given natural subgroup. -/
theorem small_layer_le_natural {G : Type*} [Group G] [Finite G]
    (π : G →* SL) (hπ : Function.Surjective π)
    (Q E Z H K : Subgroup G) [H.Normal] [Z.Normal] [IsElementaryAbelian 2 H]
    (hker : π.ker = Q) (hE : E.map π = ⊤)
    (n : NaturalFactor π ⊤ Z ⊥) (hZH : Z ≤ H) (hKH : K ≤ H) (hHQ : H ≤ Q)
    (hcentral : ⁅H,Q⁆ = ⊥) (hcomm : ⁅H,E⁆ ≤ Z)
    (hfixed : Q ⊓ centralizer (E : Set G) = ⊥)
    (flag : SL) (i : Bool) (hcard : Nat.card K ≤ 4)
    (hn : parabolic π flag i ≤ normalizer (K : Set G)) : K ≤ Z := by
  let c : G →* MulAut H := MulAut.conjNormal
  have hkill : π.ker ≤ c.ker := by
    rw [hker]
    intro g hg
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change g * (x : G) * g⁻¹ = (x : G)
    have hxc := commutator_eq_bot_iff_le_centralizer.mp hcentral x.property g hg
    rw [hxc, mul_inv_cancel_right]
  let ρ : SL →* MulAut H := π.liftOfSurjective hπ ⟨c,hkill⟩
  have hρ (g : G) : ρ (π g) = c g := MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  let σ := Offenders.linearize ρ
  have hσ (g : G) (x : Additive H) : σ (π g) x = Additive.ofMul (c g x.toMul) := by
    change Additive.ofMul (ρ (π g) x.toMul) = _
    rw [hρ]
  let N : Subrepresentation σ := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 (Z.subgroupOf H).toAddSubgroup
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨g₀,rfl⟩ := hπ g
      change (σ (π g₀) v).toMul.val ∈ Z
      rw [hσ g₀ v]
      exact (mem_normalizer_iff.mp (n.normalized (mem_top g₀)) v.toMul.val).mp hv }
  let eZ := n.equivOfBot
  let F₀ := ((inclusion hZH).comp eZ.symm.toMonoidHom).toAdditiveRight.toZModLinearMap 2
  have hF₀ (v : Fin 3 → ZMod 2) : F₀ v ∈ N.toSubmodule :=
    (eZ.symm (Multiplicative.ofAdd v)).property
  let F : (Fin 3 → ZMod 2) →ₗ[ZMod 2] N.toSubmodule := F₀.codRestrict _ hF₀
  have hFinj : Function.Injective F := by
    intro v w h
    have hh := congrArg (fun z : N.toSubmodule => z.val.toMul.val) h
    exact congrArg Multiplicative.toAdd (eZ.symm.injective (Subtype.ext hh))
  have hFsurj : Function.Surjective F := by
    intro v
    let z : Z := ⟨v.val.toMul.val,v.property⟩
    refine ⟨(eZ z).toAdd, Subtype.ext ?_⟩
    change Additive.ofMul (inclusion hZH (eZ.symm (eZ z))) = v.val
    rw [eZ.symm_apply_apply]
    rfl
  let e := (LinearEquiv.ofBijective F ⟨hFinj,hFsurj⟩).symm
  have he : ∀ g v, e (N.toRepresentation g v) =
      specialLinearNatural (k := ZMod 2) 3 (n.marking g) (e v) := by
    intro g v
    obtain ⟨g₀,rfl⟩ := hπ g
    let z : Z := ⟨v.val.toMul.val,v.property⟩
    let z' : Z := ⟨g₀ * (z : G) * g₀⁻¹,
      (mem_normalizer_iff.mp (n.normalized (mem_top g₀)) z).mp z.property⟩
    have ev : e v = (eZ z).toAdd := by
      apply e.symm.injective
      rw [e.symm_apply_apply]
      apply Subtype.ext
      change v.val = Additive.ofMul (inclusion hZH (eZ.symm (eZ z)))
      rw [eZ.symm_apply_apply]
      rfl
    have ev' : e (N.toRepresentation (π g₀) v) = (eZ z').toAdd := by
      apply e.symm.injective
      rw [e.symm_apply_apply]
      apply Subtype.ext
      change σ (π g₀) v.val = Additive.ofMul (inclusion hZH (eZ.symm (eZ z')))
      rw [eZ.symm_apply_apply, hσ g₀ v.val]
      rfl
    rw [ev,ev']
    exact n.action g₀ (mem_top _) z z' rfl
  have htriv : HasTrivialQuotient N := by
    intro g w
    obtain ⟨g₀,hg₀,rfl⟩ := Subgroup.mem_map.mp (hE ▸ (mem_top g))
    change (σ (π g₀) w - w).toMul.val ∈ Z
    rw [hσ g₀ w]
    change (g₀ * w.toMul.val * g₀⁻¹) / w.toMul.val ∈ Z
    have hh : ⁅g₀,w.toMul.val⁆ ∈ ⁅H,E⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator hg₀ w.toMul.property
    simpa only [div_eq_mul_inv, commutatorElement_def] using hcomm hh
  have hfixedσ : fixed σ = ⊥ := by
    apply le_bot_iff.mp
    intro w hw
    change w = 0
    have hc : w.toMul.val ∈ centralizer (E : Set G) := by
      intro g hg
      have hh := hw (π g)
      rw [hσ g w] at hh
      have hh' : g * w.toMul.val * g⁻¹ = w.toMul.val := congrArg (fun x : Additive H => x.toMul.val) hh
      have hh'' := congrArg (fun x : G => x*g) hh'
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh''
    have hzero : w.toMul.val = 1 := hfixed.le ⟨hHQ w.toMul.property,hc⟩
    exact congrArg Additive.ofMul (Subtype.ext hzero : w.toMul = 1)
  let A : Submodule (ZMod 2) (Additive H) :=
    AddSubgroup.toZModSubmodule 2 (K.subgroupOf H).toAddSubgroup
  have hcA : Nat.card A ≤ 4 := by
    have hc : Nat.card A = Nat.card K :=
      Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv
    rwa [hc]
  have hiA : ∀ g ∈ modelParabolic flag i, ∀ w ∈ A, σ g w ∈ A := by
    intro g hg w hw
    obtain ⟨g₀,rfl⟩ := hπ g
    rw [hσ g₀ w]
    exact (mem_normalizer_iff.mp (hn hg) w.toMul.val).mp hw
  have hA := small_invariant_le_natural_sup_fixed σ N n.marking e he htriv flag i A hcA hiA
  rw [hfixedσ,sup_bot_eq] at hA
  intro k hk
  exact hA (show Additive.ofMul (⟨k,hKH hk⟩ : H) ∈ A from hk)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.CyclicLocalization
