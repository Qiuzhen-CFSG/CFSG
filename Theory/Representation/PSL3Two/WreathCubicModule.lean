module
public import Theory.SpecificGroups.PSL3Two.Parabolics.WreathPair

/-!
# Cubic fixed spaces in the paired natural binary-three module

A cubic plane in SL₃(2) wr C₂ fixes a four-element subgroup of the
product of the two natural binary three-spaces. Sylow conjugacy reduces
to the two independent coordinate cycles. Each cycle fixes exactly the
constant vectors in its three-space; the two binary constants give the
four-element fixed group. The action hypothesis states the full literal
wreath coordinate formula, so the result applies to the original action
without changing its marking. The finite check uses only one eight-element
space, rather than enumerating the wreath group.

Source application: Aschbacher--Smith 10.2.5, printed p.748, tracking the
original module through the collapsed odd-prime enlargement. The matrix
model retains the source attribution and license in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup
open scoped Matrix
namespace Matrix.PSL3Two.WreathCubicModule
open WreathPair
abbrev Space := Bit → Multiplicative (Fin 3 → ZMod 2)
private def cubic : SL := ⟨!![0,1,0;0,0,1;1,0,0], by decide⟩
private theorem cubic_ne_one : cubic ≠ 1 := by decide +kernel
private theorem cubic_order : orderOf cubic = 3 := by
  exact orderOf_eq_prime (by decide +kernel) cubic_ne_one

private def planeHom : (Bit → zpowers cubic) →* Actor where
  toFun a := ⟨fun i => (a i : SL),1⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp

private theorem planeHom_injective : Function.Injective planeHom := by
  intro a b he
  funext i
  exact Subtype.ext (congrArg (fun w : Actor => w.left i) he)

private theorem plane_card : Nat.card planeHom.range = 9 := by
  rw [Nat.card_congr (MonoidHom.ofInjective planeHom_injective).toEquiv.symm,
    Nat.card_fun, Nat.card_zpowers, cubic_order]
  change 3 ^ Nat.card (ZMod 2) = 9
  rw [Nat.card_zmod]
  norm_num

private def planeSylow : Sylow 3 Actor := Sylow.ofCard planeHom.range (by
  rw [plane_card,RegularWreathProduct.card,card_SL]
  change 9 = 3 ^ (168 ^ Nat.card (ZMod 2) * Nat.card (ZMod 2)).factorization 3
  rw [Nat.card_zmod]
  decide +kernel)


private def fixed (ρ : Actor →* MulAut Space) (P : Subgroup Actor) : Subgroup Space where
  carrier := {v | ∀ g ∈ P, ρ g v = v}
  one_mem' := by intro g hg; exact map_one _
  mul_mem' := by intro v w hv hw g hg; rw [map_mul,hv g hg,hw g hg]
  inv_mem' := by intro v hv g hg; rw [map_inv,hv g hg]

private def single (i : Bit) : SL →* Actor where
  toFun a := ⟨Pi.mulSingle i a,1⟩
  map_one' := by ext j <;> simp
  map_mul' a b := by
    apply RegularWreathProduct.ext
    · funext j
      by_cases hj : j=i <;> simp [Pi.mulSingle_apply,hj]
    · rfl

private theorem plane_split (a : Bit → zpowers cubic) :
    planeHom a = single 1 (a 1) * single (Multiplicative.ofAdd 1) (a (Multiplicative.ofAdd 1)) := by
  apply RegularWreathProduct.ext
  · funext i
    have hi : i=1 ∨ i=Multiplicative.ofAdd 1 := (by decide : ∀ i : Bit, i=1 ∨ i=Multiplicative.ofAdd 1) i
    have h01 : (1:Bit) ≠ Multiplicative.ofAdd 1 := by decide
    rcases hi with rfl | rfl <;> simp [planeHom,single,Pi.mulSingle_apply,h01,Ne.symm h01]
  · rfl

private theorem cubic_fixed : ∀ w : Fin 3 → ZMod 2,
    cubic.val *ᵥ w = w ↔ ∀ j, w j = w 0 := by decide +kernel

variable (ρ : Actor →* MulAut Space)
  (hρ : ∀ g v i, ρ g v i = Multiplicative.ofAdd
    ((g.left i).val.mulVec ((v (g.right⁻¹ * i)).toAdd)))

include hρ in
private theorem fixed_plane_iff (v : Space) :
    v ∈ fixed ρ planeHom.range ↔ ∀ i j, (v i).toAdd j = (v i).toAdd 0 := by
  constructor
  · intro hv i
    have hm : single i cubic ∈ planeHom.range := by
      refine ⟨Pi.mulSingle i ⟨cubic,mem_zpowers cubic⟩,?_⟩
      apply RegularWreathProduct.ext
      · funext j
        by_cases hj : j=i <;> simp [planeHom,single,Pi.mulSingle_apply,hj]
      · rfl
    have he := congrFun (hv (single i cubic) hm) i
    rw [hρ] at he
    apply (cubic_fixed _).mp
    simpa [single] using congrArg Multiplicative.toAdd he
  · intro hv
    have hs (i : Bit) (a : zpowers cubic) : ρ (single i a) v = v := by
      let S := (MulAction.stabilizer (MulAut Space) v).comap (ρ.comp (single i))
      have hgen : cubic ∈ S := by
        change ρ (single i cubic) v = v
        funext j
        rw [hρ]
        by_cases hj : j=i
        · subst j
          simpa [single] using congrArg Multiplicative.ofAdd ((cubic_fixed _).mpr (hv i))
        · simp [single,hj]
      exact (zpowers_le.mpr hgen) a.property
    rintro g ⟨a,rfl⟩
    rw [plane_split,map_mul,MulAut.mul_apply,hs,hs]

private def fixedPlaneEquiv : fixed ρ planeHom.range ≃ (Bit → ZMod 2) where
  toFun v i := (v.val i).toAdd 0
  invFun a := ⟨fun i => Multiplicative.ofAdd (fun _ => a i), (fixed_plane_iff ρ hρ _).mpr (by simp)⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    apply Multiplicative.toAdd.injective
    funext j
    exact ((fixed_plane_iff ρ hρ v).mp v.property i j).symm
  right_inv a := rfl

include hρ in
private theorem fixed_plane_card : Nat.card (fixed ρ planeHom.range) = 4 := by
  rw [Nat.card_congr (fixedPlaneEquiv ρ hρ),Nat.card_fun,Nat.card_zmod]
  change 2 ^ Nat.card (ZMod 2) = 4
  rw [Nat.card_zmod]
  norm_num

private def fixedConjEquiv (P : Subgroup Actor) (g : Actor) :
    fixed ρ P ≃ fixed ρ (P.map (MulAut.conj g).toMonoidHom) where
  toFun v := ⟨ρ g v,by
    rintro x ⟨a,ha,rfl⟩
    change ρ (g*a*g⁻¹) (ρ g v) = ρ g v
    rw [map_mul,map_mul,map_inv,MulAut.mul_apply,MulAut.mul_apply,
      MulAut.inv_apply_self,v.property a ha]⟩
  invFun v := ⟨(ρ g)⁻¹ v,by
    intro a ha
    apply (ρ g).injective
    have hh := v.property _ (mem_map_of_mem (MulAut.conj g).toMonoidHom ha)
    change ρ (g*a*g⁻¹) v = v at hh
    simpa only [map_mul,map_inv,MulAut.mul_apply,MulAut.apply_inv_self] using hh⟩
  left_inv v := by apply Subtype.ext; exact MulAut.inv_apply_self Space (ρ g) v
  right_inv v := by apply Subtype.ext; exact MulAut.apply_inv_self Space (ρ g) v

include hρ in
/-- The fixed space of a cubic plane in the paired natural binary-three action has order four. -/
theorem cubic_fixed_card (P : Subgroup Actor) (hP : Nat.card P = 9) :
    Nat.card {v : Space // ∀ g ∈ P, ρ g v = v} = 4 := by
  let S : Sylow 3 Actor := Sylow.ofCard P (by
    rw [hP,RegularWreathProduct.card,card_SL]
    change 9 = 3 ^ (168 ^ Nat.card (ZMod 2) * Nat.card (ZMod 2)).factorization 3
    rw [Nat.card_zmod]
    decide +kernel)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Actor S planeSylow
  have he : P.map (MulAut.conj g).toMonoidHom = planeHom.range := congrArg Sylow.toSubgroup hg
  change Nat.card (fixed ρ P) = 4
  rw [Nat.card_congr (fixedConjEquiv ρ P g),he]
  exact fixed_plane_card ρ hρ
end Matrix.PSL3Two.WreathCubicModule
