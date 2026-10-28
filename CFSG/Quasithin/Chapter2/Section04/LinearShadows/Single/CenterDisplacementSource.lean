module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterActionSource
public import Theory.GroupTheory.ElementaryQuotientCocycles

/-!
# Involution displacements on the Thompson center

A nontrivial involution in the actual center action normalizes the regular
cyclic torus. The binary Singer bound and the elementary displacement formula
show that its fixed subgroup has square-root order. Every fixed central element
is therefore a displacement. This is the center calculation in
Aschbacher–Smith, 2.4.14(2), used in the noncentral branch of 2.4.21.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_centerless_center_involution_coboundary
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (a : G) (haT : a ∈ T) (ha2 : a^2=1) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    a ∉ centralizer (Z : Set G) →
    ∀ z ∈ Z, Commute a z → ∃ w ∈ Z, z = w * (a*w*a⁻¹)⁻¹ := by
  intro R Z han z hz haz
  obtain ⟨hTZ,hEA,C,hC,hreg,hn⟩ := source_centerless_center_action_normalizer
    d hG T hST hsingle hL hM hTM hunique c hZ
  let := hEA
  let := hC
  let α := Z.normalizerMonoidHom.comp (inclusion hTZ)
  let t := α ⟨a,haT⟩
  have ht : t ≠ 1 := by
    intro he
    apply han
    intro w hw
    have hh := congrArg (fun f : MulAut Z => (f ⟨w,hw⟩ : G)) he
    change a*w*a⁻¹=w at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have ht2 : t^2=1 := by
    have hh : (⟨a,haT⟩ : T)^2=1 := Subtype.ext ha2
    change (α ⟨a,haT⟩)^2=1
    rw [←map_pow,hh,map_one]
  have hc := regular_cyclic_automorphism_normalizer_involution_fixed_card C hreg t ht ht2
    (hn ⟨⟨a,haT⟩,rfl⟩)
  have hinv (w : Z) : t (t w)=w := by
    simpa only [pow_two,MulAut.mul_apply,MulAut.one_apply] using
      congrArg (fun f : MulAut Z => f w) ht2
  have hzfix : t ⟨z,hz⟩ = ⟨z,hz⟩ := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr haz.eq
  obtain ⟨w,hw⟩ := elementary_fixed_is_coboundary t.toMonoidHom hinv hc ⟨z,hz⟩ hzfix
  refine ⟨w,w.property,?_⟩
  rw [map_inv] at hw
  exact congrArg Subtype.val hw
end CFSG.Quasithin.Chapter2.LinearShadows.Single
