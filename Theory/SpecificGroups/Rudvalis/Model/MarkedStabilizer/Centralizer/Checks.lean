module
public import Theory.SpecificGroups.Rudvalis.Model.MarkedStabilizer.Centralizer.Data
/-!
# Checked Tits-image centralizer witnesses

Each tree edge is an actual retained Parrott image. Three words fixing1
have common fixed set{0,1}; three fixing6 have common fixed set{0,6}.
The 64-letter representative checks in0.33s at the default resource limits.
These identities imply faithfulness of full point-stabilizer conjugation.
-/
@[expose] public section
namespace Rudvalis.MarkedStabilizer.CentralizerCertificate
open OuterStabilizer.TitsEmbedding.RelationCertificate

def checks (x : Fin 4060) : Prop :=
  (x=0 ∨ x=1 ∨ x=6 ∨ (depth (parent x)<depth x ∧
    permutation (generator (label x)) (parent x)=x)) ∧
  ((∀ j : Fin 3, pin1 j x=x) → x=0 ∨ x=1) ∧
  ((∀ j : Fin 3, pin6 j x=x) → x=0 ∨ x=6)
noncomputable instance (x : Fin 4060) : Decidable (checks x) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem block0 : ∀ i : Fin 64,
    checks ⟨(64*0+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block1 : ∀ i : Fin 64,
    checks ⟨(64*1+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block2 : ∀ i : Fin 64,
    checks ⟨(64*2+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block3 : ∀ i : Fin 64,
    checks ⟨(64*3+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block4 : ∀ i : Fin 64,
    checks ⟨(64*4+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block5 : ∀ i : Fin 64,
    checks ⟨(64*5+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block6 : ∀ i : Fin 64,
    checks ⟨(64*6+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block7 : ∀ i : Fin 64,
    checks ⟨(64*7+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block8 : ∀ i : Fin 64,
    checks ⟨(64*8+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block9 : ∀ i : Fin 64,
    checks ⟨(64*9+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block10 : ∀ i : Fin 64,
    checks ⟨(64*10+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block11 : ∀ i : Fin 64,
    checks ⟨(64*11+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block12 : ∀ i : Fin 64,
    checks ⟨(64*12+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block13 : ∀ i : Fin 64,
    checks ⟨(64*13+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block14 : ∀ i : Fin 64,
    checks ⟨(64*14+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block15 : ∀ i : Fin 64,
    checks ⟨(64*15+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block16 : ∀ i : Fin 64,
    checks ⟨(64*16+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block17 : ∀ i : Fin 64,
    checks ⟨(64*17+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block18 : ∀ i : Fin 64,
    checks ⟨(64*18+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block19 : ∀ i : Fin 64,
    checks ⟨(64*19+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block20 : ∀ i : Fin 64,
    checks ⟨(64*20+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block21 : ∀ i : Fin 64,
    checks ⟨(64*21+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block22 : ∀ i : Fin 64,
    checks ⟨(64*22+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block23 : ∀ i : Fin 64,
    checks ⟨(64*23+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block24 : ∀ i : Fin 64,
    checks ⟨(64*24+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block25 : ∀ i : Fin 64,
    checks ⟨(64*25+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block26 : ∀ i : Fin 64,
    checks ⟨(64*26+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block27 : ∀ i : Fin 64,
    checks ⟨(64*27+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block28 : ∀ i : Fin 64,
    checks ⟨(64*28+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block29 : ∀ i : Fin 64,
    checks ⟨(64*29+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block30 : ∀ i : Fin 64,
    checks ⟨(64*30+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block31 : ∀ i : Fin 64,
    checks ⟨(64*31+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block32 : ∀ i : Fin 64,
    checks ⟨(64*32+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block33 : ∀ i : Fin 64,
    checks ⟨(64*33+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block34 : ∀ i : Fin 64,
    checks ⟨(64*34+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block35 : ∀ i : Fin 64,
    checks ⟨(64*35+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block36 : ∀ i : Fin 64,
    checks ⟨(64*36+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block37 : ∀ i : Fin 64,
    checks ⟨(64*37+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block38 : ∀ i : Fin 64,
    checks ⟨(64*38+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block39 : ∀ i : Fin 64,
    checks ⟨(64*39+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block40 : ∀ i : Fin 64,
    checks ⟨(64*40+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block41 : ∀ i : Fin 64,
    checks ⟨(64*41+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block42 : ∀ i : Fin 64,
    checks ⟨(64*42+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block43 : ∀ i : Fin 64,
    checks ⟨(64*43+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block44 : ∀ i : Fin 64,
    checks ⟨(64*44+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block45 : ∀ i : Fin 64,
    checks ⟨(64*45+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block46 : ∀ i : Fin 64,
    checks ⟨(64*46+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block47 : ∀ i : Fin 64,
    checks ⟨(64*47+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block48 : ∀ i : Fin 64,
    checks ⟨(64*48+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block49 : ∀ i : Fin 64,
    checks ⟨(64*49+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block50 : ∀ i : Fin 64,
    checks ⟨(64*50+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block51 : ∀ i : Fin 64,
    checks ⟨(64*51+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block52 : ∀ i : Fin 64,
    checks ⟨(64*52+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block53 : ∀ i : Fin 64,
    checks ⟨(64*53+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block54 : ∀ i : Fin 64,
    checks ⟨(64*54+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block55 : ∀ i : Fin 64,
    checks ⟨(64*55+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block56 : ∀ i : Fin 64,
    checks ⟨(64*56+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block57 : ∀ i : Fin 64,
    checks ⟨(64*57+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block58 : ∀ i : Fin 64,
    checks ⟨(64*58+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block59 : ∀ i : Fin 64,
    checks ⟨(64*59+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block60 : ∀ i : Fin 64,
    checks ⟨(64*60+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block61 : ∀ i : Fin 64,
    checks ⟨(64*61+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block62 : ∀ i : Fin 64,
    checks ⟨(64*62+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

private theorem block63 : ∀ i : Fin 64,
    checks ⟨(64*63+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by decide +kernel

theorem checks_all (x : Fin 4060) : checks x := by
  let b : Fin 64 := ⟨x.val/64, by omega⟩
  let i : Fin 64 := ⟨x.val%64, Nat.mod_lt _ (by decide)⟩
  have H : ∀ b i : Fin 64, checks ⟨(64*b.val+i.val)%4060,Nat.mod_lt _ (by decide)⟩ := by
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
    | ⟨55, _⟩ => exact block55
    | ⟨56, _⟩ => exact block56
    | ⟨57, _⟩ => exact block57
    | ⟨58, _⟩ => exact block58
    | ⟨59, _⟩ => exact block59
    | ⟨60, _⟩ => exact block60
    | ⟨61, _⟩ => exact block61
    | ⟨62, _⟩ => exact block62
    | ⟨63, _⟩ => exact block63
    | ⟨n+64, h⟩ => omega
  have hx : (64*b.val+i.val)%4060=x.val := by dsimp [b,i]; omega
  simpa only [hx,Fin.eta] using H b i

theorem pin1_fix : ∀j : Fin 3, pin1 j 1=1 := by decide +kernel
theorem pin6_fix : ∀j : Fin 3, pin6 j 6=6 := by decide +kernel
end Rudvalis.MarkedStabilizer.CentralizerCertificate
