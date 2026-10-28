module
public import Theory.GroupAction.PrimeGroupFixedImage
public import Theory.GroupTheory.NormalCubicSylowSupplement

/-!
# Centralizers in a permuting cubic Sylow supplement

Let D have order three and permute with a prescribed Sylow two-subgroup S.
For a homomorphism with three-free kernel, injective on D, every element of
f(S) centralizing f(D) lifts to C_S(D). Apply prime-group fixed-point lifting
inside SD. Writing the lift as sd, disjointness of f(S) and f(D) forces d=1.
The equality retains the original homomorphism and the chosen Sylow subgroup.

Source application: Aschbacher--Smith 13.2.7, printed pp.883--884, where
D is the selected cubic lift through O₃′(H₀).
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

/-- A cubic complement permuting with a Sylow two-subgroup permits fixed
representatives in that same Sylow, through a three-free kernel. -/
theorem permuting_cubic_sylow_centralizer_image
    (S : Sylow 2 G) (D : Subgroup G) (hD : Nat.card D = 3)
    (hperm : (S : Set G) * (D : Set G) = (D : Set G) * (S : Set G))
    (f : G →* Q) (hker : ¬ 3 ∣ Nat.card f.ker)
    (hinj : Function.Injective (f.comp D.subtype)) :
    ((S : Subgroup G) ⊓ centralizer (D : Set G)).map f =
      (S : Subgroup G).map f ⊓ centralizer (D.map f : Set Q) := by
  let X := (S : Subgroup G) ⊔ D
  let DX := D.subgroupOf X
  let r := f.comp X.subtype
  let a := r.rangeRestrict
  have hDthree : IsPGroup 3 D := IsPGroup.of_card (n := 1) (by simpa using hD)
  have hDX : IsPGroup 3 DX := hDthree.of_equiv
    (subgroupOfEquivOfLe (show D ≤ X from le_sup_right)).symm
  let k : a.ker →* f.ker :=
    { toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => (z : G)) h
  have hka : ¬ 3 ∣ Nat.card a.ker := fun hh =>
    hker (hh.trans (card_dvd_of_injective k hk))
  have hcent := centralizer_map_of_prime_free_kernel a r.rangeRestrict_surjective hka DX hDX
  have hdis : Disjoint (D.map f) ((S : Subgroup G).map f) :=
    IsPGroup.disjoint_of_ne 3 2 (by decide) _ _ (hDthree.map f) (S.isPGroup'.map f)
  apply le_antisymm
  · exact le_inf (map_mono inf_le_left)
      ((map_mono inf_le_right).trans (map_centralizer_le_centralizer_image _ f))
  · rintro y ⟨⟨s,hs,rfl⟩,hc⟩
    let sx : X := ⟨s,mem_sup_left hs⟩
    have hy : a sx ∈ centralizer (DX.map a : Set r.range) := by
      rintro z ⟨d,hd,rfl⟩
      apply Subtype.ext
      exact hc (f d) (mem_map_of_mem f hd)
    rw [←hcent] at hy
    obtain ⟨x,hxc,hxe⟩ := hy
    have he : f x = f s := congrArg Subtype.val hxe
    have hxS : (x : G) ∈ (S : Subgroup G) := by
      have hx : (x : G) ∈ (S : Set G) * (D : Set G) := by
        change (x : G) ∈ ((S : Subgroup G) : Set G) * (D : Set G)
        rw [←coe_sup_of_set_mul_comm (S : Subgroup G) D hperm]
        exact x.property
      obtain ⟨t,ht,d,hd,htd⟩ := hx
      change t * d = (x : G) at htd
      have hfd : f d ∈ (S : Subgroup G).map f := by
        have hdval : f d = (f t)⁻¹ * f s := by
          calc
            f d = (f t)⁻¹ * (f t * f d) := by simp
            _ = (f t)⁻¹ * f s := by rw [←map_mul,htd,he]
        rw [hdval]
        exact ((S : Subgroup G).map f).mul_mem
          (((S : Subgroup G).map f).inv_mem (mem_map_of_mem f ht)) (mem_map_of_mem f hs)
      have hd1 : d = 1 := by
        have hh : f d = 1 := hdis.le_bot ⟨mem_map_of_mem f hd,hfd⟩
        exact congrArg (fun z : D => (z : G)) (hinj (show f.comp D.subtype ⟨d,hd⟩ =
          f.comp D.subtype 1 by simpa using hh))
      rw [hd1,mul_one] at htd
      exact htd ▸ ht
    refine ⟨x,⟨hxS,?_⟩,he⟩
    intro d hd
    exact congrArg X.subtype (hxc ⟨d,mem_sup_right hd⟩ hd)
end Subgroup
