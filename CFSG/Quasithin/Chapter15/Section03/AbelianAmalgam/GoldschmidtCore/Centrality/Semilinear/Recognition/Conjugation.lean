module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.Fano
public import Theory.Representation.NormalElementaryQuotient
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The Fano reconstruction for literal ambient conjugation

Linear generation follows from the actual equality W = ⟨Zᴴ⟩ and |Z| = 2.
A compatible quotient marking then transports fixation of Z by G₂ and
normalization of the actual four-group F by G₁ to the hypotheses of the
Fano reconstruction. The result is an equivalence of the given representation
with the natural action composed with the same group marking.

The quotient recognition, faithful action, conjugation identity, elementary
subgroup W, and conjugate-span equality are explicit parent obligations.
This does not assert that these data have been constructed in the bad branch.
Source: the repair of Aschbacher–Smith 15.3.68(2), combined manuscript of
1 March 2004, printed pp.1152–1155.
-/

public section

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

variable {G B : Type*} [Group G] [Group B]

/-- Conjugate generation by the actual order-two seed gives linear generation
by its nonidentity vector under the specified quotient action. -/
theorem span_orbit_of_conjugateSpan
    (H Z W : Subgroup G) [IsElementaryAbelian 2 W]
    (q : H →* B) (ρ : Representation (ZMod 2) B (Additive W))
    (hconj : ∀ (h : H) (w : Additive W),
      ((ρ (q h) w).toMul : G) = (h : G) * (w.toMul : G) * (h : G)⁻¹)
    (hZW : Z ≤ W) (hZ : Nat.card Z = 2)
    (z : Z) (hz : z ≠ 1) (hspan : W = conjugateSpanBy Z H) :
    Submodule.span (ZMod 2)
      (Set.range (fun b => ρ b (Additive.ofMul (⟨z,hZW z.property⟩ : W)))) = ⊤ := by
  let L := Submodule.span (ZMod 2)
    (Set.range (fun b => ρ b (Additive.ofMul (⟨z,hZW z.property⟩ : W))))
  let D : Subgroup G := L.toAddSubgroup.toSubgroup'.map W.subtype
  have hWD : W ≤ D := by
    rw [hspan]
    apply (closure_le _).mpr
    rintro x ⟨h,hh,u,hu,rfl⟩
    by_cases hu1 : u = 1
    · simp [hu1]
    · have huz : u = z := congrArg Subtype.val
        (((Nat.card_eq_two_iff' (1 : Z)).mp hZ).unique
          (show (⟨u,hu⟩ : Z) ≠ 1 from fun h => hu1 (congrArg Subtype.val h)) hz)
      subst u
      exact ⟨(ρ (q ⟨h,hh⟩) (Additive.ofMul (⟨z,hZW z.property⟩ : W))).toMul,
        (show ρ (q ⟨h,hh⟩) (Additive.ofMul (⟨z,hZW z.property⟩ : W)) ∈ L from
          Submodule.subset_span ⟨q ⟨h,hh⟩,rfl⟩),hconj ⟨h,hh⟩ _⟩
  apply top_unique
  intro w _
  obtain ⟨u,hu,he⟩ := hWD w.toMul.property
  have hue : Additive.ofMul u = w := congrArg Additive.ofMul (Subtype.ext he)
  exact hue ▸ hu

/-- An actual conjugation action with compatible point/line marking is the
natural module. The four-group and order-two seed are literal ambient subgroups. -/
theorem natural_of_conjugation_marking
    (H Z F W G₁ G₂ : Subgroup G) [IsElementaryAbelian 2 W]
    (q : H →* B)
    (ρ : Representation (ZMod 2) B (Additive W)) (hfaith : Function.Injective ρ)
    (hconj : ∀ (h : H) (w : Additive W),
      ((ρ (q h) w).toMul : G) = (h : G) * (w.toMul : G) * (h : G)⁻¹)
    (hZF : Z ≤ F) (hFW : F ≤ W) (hZ : Nat.card Z = 2) (hF : Nat.card F = 4)
    (hspan : W = conjugateSpanBy Z H)
    (h₁ : G₁ ≤ normalizer (F : Set G)) (h₂ : G₂ ≤ centralizer (Z : Set G))
    (m : B ≃* Matrix.PSL3Two.SL)
    (hm₁ : (G₁.subgroupOf H).map (m.toMonoidHom.comp q) = Matrix.PSL3Two.lineParabolicSL)
    (hm₂ : (G₂.subgroupOf H).map (m.toMonoidHom.comp q) = Matrix.PSL3Two.pointParabolicSL) :
    Nonempty (ρ.Equiv (BinaryLinearThree.W.comp m.toMonoidHom)) := by
  classical
  obtain ⟨z,hz,_⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  let zW : Additive W := Additive.ofMul ⟨z,hFW (hZF z.property)⟩
  let σ := ρ.comp m.symm.toMonoidHom
  let F₀ : Submodule (ZMod 2) (Additive W) :=
    NormalElementaryQuotient.subspace W (F.subgroupOf W)
  have hzW : zW ≠ 0 := by
    intro h
    apply hz
    exact Subtype.ext (congrArg (fun a : Additive W => (a.toMul : G)) h)
  have hfσ : Function.Injective σ := hfaith.comp m.symm.injective
  have hfix : ∀ g ∈ Matrix.PSL3Two.pointParabolicSL, σ g zW = zW := by
    intro g hg
    rw [← hm₂] at hg
    obtain ⟨h,hh,rfl⟩ := hg
    change ρ (m.symm (m (q h))) zW = zW
    rw [m.symm_apply_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hconj]
    have hc := h₂ hh z z.property
    change (h : G) * (z : G) * (h : G)⁻¹ = z
    change (z : G) * (h : G) = (h : G) * (z : G) at hc
    rw [← hc,mul_inv_cancel_right]
  have hcard : Nat.card F₀ = 4 := by
    let e : F₀ ≃ F := {
      toFun a := ⟨a.val.toMul,a.property⟩
      invFun a := ⟨Additive.ofMul ⟨a,hFW a.property⟩,a.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    exact (Nat.card_congr e).trans hF
  have hstable : ∀ g ∈ Matrix.PSL3Two.lineParabolicSL, ∀ a ∈ F₀, σ g a ∈ F₀ := by
    intro g hg a ha
    rw [← hm₁] at hg
    obtain ⟨h,hh,rfl⟩ := hg
    change ((ρ (m.symm (m (q h))) a).toMul : G) ∈ F
    rw [m.symm_apply_apply,hconj]
    exact (mem_normalizer_iff.mp (h₁ hh) (a.toMul : G)).mp ha
  have hs := span_orbit_of_conjugateSpan H Z W q ρ hconj (hZF.trans hFW) hZ z hz hspan
  have hsσ : Submodule.span (ZMod 2) (Set.range (fun g => σ g zW)) = ⊤ := by
    have hr : Set.range (fun g => σ g zW) = Set.range (fun b => ρ b zW) := by
      ext a
      constructor
      · rintro ⟨g,rfl⟩; exact ⟨m.symm g,rfl⟩
      · rintro ⟨b,rfl⟩; exact ⟨m b,by change ρ (m.symm (m b)) zW = _; rw [m.symm_apply_apply]⟩
    rw [hr]
    exact hs
  obtain ⟨e,_⟩ := natural_equiv_of_marked_four σ hfσ zW hzW hfix F₀ hcard
    (show zW ∈ F₀ from hZF z.property) hstable hsσ
  refine ⟨{ e.toLinearEquiv.symm with isIntertwining' := ?_ }⟩
  intro b
  apply LinearMap.ext
  intro a
  have he := Representation.IntertwiningMap.isIntertwining σ BinaryLinearThree.W
    e.symm.toIntertwiningMap (m b) a
  change e.symm (ρ (m.symm (m b)) a) = BinaryLinearThree.W (m b) (e.symm a) at he
  change e.symm (ρ b a) = BinaryLinearThree.W (m b) (e.symm a)
  simpa only [m.symm_apply_apply] using he

/-- Transport the seven-element nonzero orbit through the same actual quotient
isomorphism as the natural representation. -/
theorem quotient_natural_orbit_card
    {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    (ρ : Representation (ZMod 2) B A) (m : B ≃* Matrix.PSL3Two.SL)
    (e : ρ.Equiv (BinaryLinearThree.W.comp m.toMonoidHom)) (z : A) (hz : z ≠ 0) :
    Nat.card (Set.range (fun b => ρ b z)) = 7 := by
  let σ := ρ.comp m.symm.toMonoidHom
  let e' : BinaryLinearThree.W.Equiv σ := {
    e.toLinearEquiv.symm with
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro v
      have he := Representation.IntertwiningMap.isIntertwining
        (BinaryLinearThree.W.comp m.toMonoidHom) ρ e.symm.toIntertwiningMap (m.symm g) v
      change e.symm (BinaryLinearThree.W (m (m.symm g)) v) = ρ (m.symm g) (e.symm v) at he
      change e.symm (BinaryLinearThree.W g v) = ρ (m.symm g) (e.symm v)
      simpa only [m.apply_symm_apply] using he }
  have hr : Set.range (fun g => σ g z) = Set.range (fun b => ρ b z) := by
    ext a
    constructor
    · rintro ⟨g,rfl⟩; exact ⟨m.symm g,rfl⟩
    · rintro ⟨b,rfl⟩
      exact ⟨m b,by change ρ (m.symm (m b)) z = _; rw [m.symm_apply_apply]⟩
  rw [← hr]
  exact natural_nonzero_orbit_card σ e' z hz

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
