module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.Orbit.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.Bray.Tables
/-!
# The retained 3510-point orbit

The point map, its left inverse and the two induced Bray permutations are
checked against the certified full packed tables. The inverse checks prove
injectivity and bijectivity directly, without a centralizer order claim.
The 64-point representative takes 0.75 seconds in the kernel; these checks
are serialized to keep their finite-table working memory bounded.
-/
@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.CentralizerSection.Orbit
open Theory.GroupAction.PackedPermutation

def orbitChecks (i : Fin 3510) : Prop :=
    pointInverse (point i) = i ∧
    smallInv0 (small0 i) = i ∧ small0 (smallInv0 i) = i ∧
    smallInv1 (small1 i) = i ∧ small1 (smallInv1 i) = i ∧
    get 19 Bray.tableH0 (point i) = (point (small0 i)).val ∧
    get 19 Bray.tableH1 (point i) = (point (small1 i)).val
noncomputable instance (i : Fin 3510) : Decidable (orbitChecks i) := inferInstanceAs (Decidable (_ ∧ _))

set_option Elab.async false in
private theorem block0 : ∀ j : Fin 64,
    orbitChecks ⟨(64*0+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block1 : ∀ j : Fin 64,
    orbitChecks ⟨(64*1+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block2 : ∀ j : Fin 64,
    orbitChecks ⟨(64*2+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block3 : ∀ j : Fin 64,
    orbitChecks ⟨(64*3+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block4 : ∀ j : Fin 64,
    orbitChecks ⟨(64*4+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block5 : ∀ j : Fin 64,
    orbitChecks ⟨(64*5+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block6 : ∀ j : Fin 64,
    orbitChecks ⟨(64*6+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block7 : ∀ j : Fin 64,
    orbitChecks ⟨(64*7+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block8 : ∀ j : Fin 64,
    orbitChecks ⟨(64*8+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block9 : ∀ j : Fin 64,
    orbitChecks ⟨(64*9+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block10 : ∀ j : Fin 64,
    orbitChecks ⟨(64*10+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block11 : ∀ j : Fin 64,
    orbitChecks ⟨(64*11+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block12 : ∀ j : Fin 64,
    orbitChecks ⟨(64*12+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block13 : ∀ j : Fin 64,
    orbitChecks ⟨(64*13+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block14 : ∀ j : Fin 64,
    orbitChecks ⟨(64*14+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block15 : ∀ j : Fin 64,
    orbitChecks ⟨(64*15+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block16 : ∀ j : Fin 64,
    orbitChecks ⟨(64*16+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block17 : ∀ j : Fin 64,
    orbitChecks ⟨(64*17+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block18 : ∀ j : Fin 64,
    orbitChecks ⟨(64*18+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block19 : ∀ j : Fin 64,
    orbitChecks ⟨(64*19+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block20 : ∀ j : Fin 64,
    orbitChecks ⟨(64*20+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block21 : ∀ j : Fin 64,
    orbitChecks ⟨(64*21+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block22 : ∀ j : Fin 64,
    orbitChecks ⟨(64*22+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block23 : ∀ j : Fin 64,
    orbitChecks ⟨(64*23+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block24 : ∀ j : Fin 64,
    orbitChecks ⟨(64*24+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block25 : ∀ j : Fin 64,
    orbitChecks ⟨(64*25+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block26 : ∀ j : Fin 64,
    orbitChecks ⟨(64*26+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block27 : ∀ j : Fin 64,
    orbitChecks ⟨(64*27+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block28 : ∀ j : Fin 64,
    orbitChecks ⟨(64*28+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block29 : ∀ j : Fin 64,
    orbitChecks ⟨(64*29+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block30 : ∀ j : Fin 64,
    orbitChecks ⟨(64*30+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block31 : ∀ j : Fin 64,
    orbitChecks ⟨(64*31+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block32 : ∀ j : Fin 64,
    orbitChecks ⟨(64*32+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block33 : ∀ j : Fin 64,
    orbitChecks ⟨(64*33+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block34 : ∀ j : Fin 64,
    orbitChecks ⟨(64*34+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block35 : ∀ j : Fin 64,
    orbitChecks ⟨(64*35+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block36 : ∀ j : Fin 64,
    orbitChecks ⟨(64*36+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block37 : ∀ j : Fin 64,
    orbitChecks ⟨(64*37+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block38 : ∀ j : Fin 64,
    orbitChecks ⟨(64*38+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block39 : ∀ j : Fin 64,
    orbitChecks ⟨(64*39+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block40 : ∀ j : Fin 64,
    orbitChecks ⟨(64*40+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block41 : ∀ j : Fin 64,
    orbitChecks ⟨(64*41+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block42 : ∀ j : Fin 64,
    orbitChecks ⟨(64*42+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block43 : ∀ j : Fin 64,
    orbitChecks ⟨(64*43+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block44 : ∀ j : Fin 64,
    orbitChecks ⟨(64*44+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block45 : ∀ j : Fin 64,
    orbitChecks ⟨(64*45+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block46 : ∀ j : Fin 64,
    orbitChecks ⟨(64*46+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block47 : ∀ j : Fin 64,
    orbitChecks ⟨(64*47+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block48 : ∀ j : Fin 64,
    orbitChecks ⟨(64*48+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block49 : ∀ j : Fin 64,
    orbitChecks ⟨(64*49+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block50 : ∀ j : Fin 64,
    orbitChecks ⟨(64*50+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block51 : ∀ j : Fin 64,
    orbitChecks ⟨(64*51+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block52 : ∀ j : Fin 64,
    orbitChecks ⟨(64*52+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block53 : ∀ j : Fin 64,
    orbitChecks ⟨(64*53+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

set_option Elab.async false in
private theorem block54 : ∀ j : Fin 64,
    orbitChecks ⟨(64*54+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by decide +kernel

theorem orbitChecks_all (i : Fin 3510) : orbitChecks i := by
  let b : Fin 55 := ⟨i.val/64, by omega⟩
  let j : Fin 64 := ⟨i.val%64, Nat.mod_lt _ (by decide)⟩
  have H : ∀ b : Fin 55, ∀ j : Fin 64,
      orbitChecks ⟨(64*b.val+j.val)%3510, Nat.mod_lt _ (by decide)⟩ := by
    intro b
    match b with
    | ⟨0, _⟩ => exact block0
    | ⟨1, _⟩ => exact block1
    | ⟨2, _⟩ => exact block2
    | ⟨3, _⟩ => exact block3
    | ⟨4, _⟩ => exact block4
    | ⟨5, _⟩ => exact block5
    | ⟨6, _⟩ => exact block6
    | ⟨7, _⟩ => exact block7
    | ⟨8, _⟩ => exact block8
    | ⟨9, _⟩ => exact block9
    | ⟨10, _⟩ => exact block10
    | ⟨11, _⟩ => exact block11
    | ⟨12, _⟩ => exact block12
    | ⟨13, _⟩ => exact block13
    | ⟨14, _⟩ => exact block14
    | ⟨15, _⟩ => exact block15
    | ⟨16, _⟩ => exact block16
    | ⟨17, _⟩ => exact block17
    | ⟨18, _⟩ => exact block18
    | ⟨19, _⟩ => exact block19
    | ⟨20, _⟩ => exact block20
    | ⟨21, _⟩ => exact block21
    | ⟨22, _⟩ => exact block22
    | ⟨23, _⟩ => exact block23
    | ⟨24, _⟩ => exact block24
    | ⟨25, _⟩ => exact block25
    | ⟨26, _⟩ => exact block26
    | ⟨27, _⟩ => exact block27
    | ⟨28, _⟩ => exact block28
    | ⟨29, _⟩ => exact block29
    | ⟨30, _⟩ => exact block30
    | ⟨31, _⟩ => exact block31
    | ⟨32, _⟩ => exact block32
    | ⟨33, _⟩ => exact block33
    | ⟨34, _⟩ => exact block34
    | ⟨35, _⟩ => exact block35
    | ⟨36, _⟩ => exact block36
    | ⟨37, _⟩ => exact block37
    | ⟨38, _⟩ => exact block38
    | ⟨39, _⟩ => exact block39
    | ⟨40, _⟩ => exact block40
    | ⟨41, _⟩ => exact block41
    | ⟨42, _⟩ => exact block42
    | ⟨43, _⟩ => exact block43
    | ⟨44, _⟩ => exact block44
    | ⟨45, _⟩ => exact block45
    | ⟨46, _⟩ => exact block46
    | ⟨47, _⟩ => exact block47
    | ⟨48, _⟩ => exact block48
    | ⟨49, _⟩ => exact block49
    | ⟨50, _⟩ => exact block50
    | ⟨51, _⟩ => exact block51
    | ⟨52, _⟩ => exact block52
    | ⟨53, _⟩ => exact block53
    | ⟨54, _⟩ => exact block54
    | ⟨n+55, h⟩ => omega
  have hi : (64*b.val+j.val)%3510=i.val := by
    dsimp [b,j]
    omega
  simpa only [hi, Fin.eta] using H b j

theorem point_injective : Function.Injective point :=
  Function.LeftInverse.injective (fun i => (orbitChecks_all i).1)

noncomputable def smallPerm0 : Equiv.Perm (Fin 3510) where
  toFun := small0
  invFun := smallInv0
  left_inv i := (orbitChecks_all i).2.1
  right_inv i := (orbitChecks_all i).2.2.1
noncomputable def smallPerm1 : Equiv.Perm (Fin 3510) where
  toFun := small1
  invFun := smallInv1
  left_inv i := (orbitChecks_all i).2.2.2.1
  right_inv i := (orbitChecks_all i).2.2.2.2.1

theorem tableH0_point (i : Fin 3510) :
    get 19 Bray.tableH0 (point i) = (point (smallPerm0 i)).val :=
  (orbitChecks_all i).2.2.2.2.2.1
theorem tableH1_point (i : Fin 3510) :
    get 19 Bray.tableH1 (point i) = (point (smallPerm1 i)).val :=
  (orbitChecks_all i).2.2.2.2.2.2
end Sporadic.Fischer.Fi24Prime.CentralizerSection.Orbit
