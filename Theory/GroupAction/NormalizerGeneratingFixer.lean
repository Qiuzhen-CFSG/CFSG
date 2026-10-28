module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.Sylow
/-!
# Pointwise fixers detected by generating normalizers

Let U be a finite p-group inside G, and let Qᵢ ≤ U have centralizers
contained in U. An automorphism fixing U sends x⁻¹a(x) into U for each
x in N_G(Qᵢ). These displacements give a homomorphism from the whole fixer
into a product of copies of U. If the normalizers generate G, the map is
injective. In particular, there is no assumption on the orders of the
individual automorphisms. Pointwise fixation also preserves each normalizer.

Sylow conjugacy transfers this bound to every Sylow subgroup of G.
This is the local automorphism argument used in Aschbacher–Smith, B.1.13,
printed pp.73–74 of `refs/quasithin.pdf`.
-/

public section
open Subgroup
namespace Theory.GroupAction.NormalizerGeneratingFixer
variable {G : Type*} [Group G]

/-- Every pointwise fixer preserves the actual normalizer of a fixed subgroup. -/
theorem fixes_normalizer (U Q : Subgroup G) (hQU : Q ≤ U)
    (a : MulAut G) (ha : ∀ x ∈ U, a x = x) :
    (normalizer (Q : Set G)).map a.toMonoidHom = normalizer (Q : Set G) := by
  rw [map_normalizer_eq_of_bijective _ a.bijective]
  congr 1
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change a x ∈ Q
    rw [ha x (hQU hx)]
    exact hx
  · intro x hx
    exact ⟨x, hx, ha x (hQU hx)⟩

/-- Displacement on a normalizer centralizes the subgroup fixed pointwise. -/
theorem displacement_mem_centralizer (Q : Subgroup G) (a : MulAut G)
    (ha : ∀ y ∈ Q, a y = y) (x : G) (hx : x ∈ normalizer (Q : Set G)) :
    x⁻¹ * a x ∈ centralizer (Q : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  have hxy := ha (x * y * x⁻¹) ((mem_normalizer_iff.mp hx y).mp hy)
  rw [map_mul, map_mul, map_inv, ha y hy] at hxy
  have h := congrArg (fun z => x⁻¹ * z * a x) hxy
  simpa only [mul_assoc, inv_mul_cancel, mul_inv_cancel_right, mul_one,
    inv_mul_cancel_left] using h.symm

/-- Generating normalizers detect the entire pointwise automorphism fixer. -/
theorem fixer_isPGroup {p : ℕ} (U : Subgroup G) [Finite U] (hU : IsPGroup p U)
    {ι : Type*} (Q : ι → Subgroup G) (hQU : ∀ i, Q i ≤ U)
    (hC : ∀ i, centralizer (Q i : Set G) ≤ U)
    (hgen : (⨆ i, normalizer (Q i : Set G)) = ⊤) :
    IsPGroup p (fixingSubgroup (MulAut G) (U : Set G)) := by
  let D := fixingSubgroup (MulAut G) (U : Set G)
  have hfix (a : D) (x : G) (hx : x ∈ U) : a.val x = x :=
    (mem_fixingSubgroup_iff _).mp a.property x hx
  let d : D →* (∀ i, normalizer (Q i : Set G) → U) := {
    toFun a i x := ⟨x.val⁻¹ * a.val x, hC i
      (displacement_mem_centralizer (Q i) a.val
        (fun y hy => hfix a y (hQU i hy)) x x.property)⟩
    map_one' := by funext i x; apply Subtype.ext; simp
    map_mul' a b := by
      funext i x
      apply Subtype.ext
      change x.val⁻¹ * a.val (b.val x) =
        (x.val⁻¹ * a.val x) * (x.val⁻¹ * b.val x)
      have hb := hC i (displacement_mem_centralizer (Q i) b.val
        (fun y hy => hfix b y (hQU i hy)) x x.property)
      have ha := hfix a (x.val⁻¹ * b.val x) hb
      rw [map_mul, map_inv] at ha
      calc
        _ = x.val⁻¹ * (a.val x * ((a.val x)⁻¹ * a.val (b.val x))) := by simp
        _ = _ := by rw [ha, mul_assoc]
  }
  have hd : Function.Injective d := by
    intro a b hab
    have hle : (⨆ i, normalizer (Q i : Set G)) ≤
        a.val.toMonoidHom.eqLocus b.val.toMonoidHom := by
      apply iSup_le
      intro i x hx
      exact mul_left_cancel (congrArg Subtype.val (congrFun (congrFun hab i) ⟨x, hx⟩))
    rw [hgen] at hle
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    exact hle (mem_top x)
  have ht : IsPGroup p (∀ i, normalizer (Q i : Set G) → U) := by
    obtain ⟨k, hk⟩ := isPGroup_iff_exists_pow_pow_eq_one.mp hU
    intro f
    exact ⟨k, funext (fun i => funext (fun x => hk (f i x)))⟩
  exact ht.of_injective d hd

/-- Conjugating a subgroup by an automorphism preserves its fixer bound. -/
theorem fixer_map_isPGroup {p : ℕ} (U : Subgroup G)
    (hU : IsPGroup p (fixingSubgroup (MulAut G) (U : Set G))) (e : MulAut G) :
    IsPGroup p (fixingSubgroup (MulAut G) (U.map e.toMonoidHom : Set G)) := by
  let D := fixingSubgroup (MulAut G) (U.map e.toMonoidHom : Set G)
  let C := fixingSubgroup (MulAut G) (U : Set G)
  let j : D →* C := ((MulAut.congr e.symm).toMonoidHom.comp D.subtype).codRestrict C (by
    intro a
    apply (mem_fixingSubgroup_iff _).mpr
    intro x hx
    change e.symm (a.val (e x)) = x
    have h := (mem_fixingSubgroup_iff _).mp a.property (e x) (mem_map_of_mem _ hx)
    change a.val (e x) = e x at h
    rw [h, e.symm_apply_apply])
  exact hU.of_injective j (fun a b h =>
    Subtype.ext ((MulAut.congr e.symm).injective (congrArg Subtype.val h)))

/-- One p-subgroup with a p-group fixer controls the fixer of every Sylow subgroup. -/
theorem sylow_fixer_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    (U : Subgroup G) (hU : IsPGroup p U)
    (hfix : IsPGroup p (fixingSubgroup (MulAut G) (U : Set G))) (S : Sylow p G) :
    IsPGroup p (fixingSubgroup (MulAut G) (S : Set G)) := by
  obtain ⟨P, hUP⟩ := hU.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  have hm : (P : Subgroup G).map (MulAut.conj g).toMonoidHom = S :=
    congrArg (fun R : Sylow p G => (R : Subgroup G)) hg
  apply (fixer_map_isPGroup U hfix (MulAut.conj g)).to_le
  intro a ha
  apply (mem_fixingSubgroup_iff _).mpr
  intro x hx
  exact (mem_fixingSubgroup_iff _).mp ha x
    ((hm ▸ (map_mono (f := (MulAut.conj g).toMonoidHom) hUP)) hx)

end Theory.GroupAction.NormalizerGeneratingFixer
