module
public import Theory.Representation.BinaryEndpointInduction.ParabolicSeedMarking
public import Theory.Representation.BinaryCubicPairs.FixedCount
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!
# The natural fixed dimension of an endpoint cubic

The fixed first row makes the sum of the three translates of e0 a nonzero
fixed vector. The order-three orbit congruence restricts the fixed-space
cardinality modulo three, while nonidentity makes that space proper.
In dimension four these facts force exactly four fixed vectors, hence
fixed dimension two. No matrix enumeration or normal form is assumed.
-/
public noncomputable section
open Matrix Subgroup
open scoped MatrixGroups
namespace BinaryEndpointInduction

/-- The literal endpoint cubic has natural fixed dimension two. -/
theorem endpoint_cubic_fixed_finrank (a : SL(4,ZMod 2))
    (haP : a ∈ endpointParabolic) (ha : a^3=1) (hne : a≠1) :
    Module.finrank (ZMod 2) (BinaryCubicPairs.fixedKernel a.val)=2 := by
  let V := Fin 4 → ZMod 2
  let g : V ≃ₗ[ZMod 2] V := a.toLin'
  let F := BinaryCubicPairs.fixedKernel a.val
  have hmem (x : V) : x ∈ F ↔ g x=x := by
    change a.val.mulVec x-x=0 ↔ g x=x
    exact sub_eq_zero
  have hg3 : g^3=1 := by
    change SpecialLinearGroup.toLin' a^3=1
    rw [←map_pow,ha,map_one]
  have hzero (x : V) : g x 0=x 0 := by
    change (a.val *ᵥ x) 0=x 0
    simp [Matrix.mulVec,dotProduct,show ∀ k : Fin 4, a.val 0 k=if k=0 then 1 else 0 from haP]
  let u : V := Pi.single 0 1
  let y := u+g u+g (g u)
  have hy : y ∈ F := by
    apply (hmem y).mpr
    have ht : g (g (g u))=u := by
      exact congrArg (fun h : V ≃ₗ[ZMod 2] V => h u) hg3
    dsimp only [y]
    rw [map_add,map_add,ht]
    abel
  have hyn : y≠0 := by
    intro h
    have hh := congrFun h 0
    change u 0+g u 0+g (g u) 0=0 at hh
    rw [hzero,hzero,hzero] at hh
    change (1 : ZMod 2)+1+1=0 at hh
    exact (by decide : (1 : ZMod 2)+1+1≠0) hh
  have hFpos : 0<Module.finrank (ZMod 2) F := by
    let : Nontrivial F := ⟨⟨⟨y,hy⟩,0,fun h => hyn (congrArg Subtype.val h)⟩⟩
    exact Module.finrank_pos
  have hFproper : F≠⊤ := by
    intro ht
    apply hne
    apply Subtype.ext
    apply Matrix.mulVec_injective
    funext x
    change a.val *ᵥ x=(1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x
    rw [Matrix.one_mulVec]
    exact (hmem x).mp (ht ▸ Submodule.mem_top)
  have hFlt : Module.finrank (ZMod 2) F<4 := by
    have hle := F.finrank_le
    have hd : Module.finrank (ZMod 2) V=4 := Module.finrank_fin_fun (ZMod 2)
    rw [hd] at hle
    have hn : Module.finrank (ZMod 2) F≠4 := by
      intro he
      exact hFproper (Submodule.eq_top_of_finrank_eq (he.trans hd.symm))
    omega
  let A := zpowers g
  have hp : IsPGroup 3 A := (IsElementaryAbelian.zpowers_of_pow_eq_one hg3).isPGroup 3 A
  have he : MulAction.fixedPoints A V ≃ F := {
    toFun x := ⟨x.val,(hmem x.val).mpr (x.property ⟨g,mem_zpowers g⟩)⟩
    invFun x := ⟨x.val,by
      rintro ⟨h,hh⟩
      obtain ⟨n,rfl⟩ := hh
      exact MulAction.mem_fixedBy_zpow (G := V ≃ₗ[ZMod 2] V) (α := V)
        (g := g) (a := x.val) ((hmem x.val).mp x.property) n⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hm := hp.card_modEq_card_fixedPoints V
  rw [Nat.card_congr he,Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F),Nat.card_zmod] at hm
  have hc : Nat.card V=16 := by simp [V]
  rw [hc] at hm
  change 16 % 3=2^Module.finrank (ZMod 2) F % 3 at hm
  interval_cases h : Module.finrank (ZMod 2) F <;> norm_num [h] at *

end BinaryEndpointInduction
