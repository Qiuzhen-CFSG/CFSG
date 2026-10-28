module
public import Theory.Representation.BinaryPermutation.EightElementaryCertificate.Multiplication
/-! Closure certificates for adjoining commuting involutions to the elementary rows. -/
@[expose] public section
open BinaryPermutation BinaryPermutation.EightNonsingular
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace BinaryPermutation.EightElementaryCertificate
set_option maxRecDepth 4096 in
private theorem ext_block_0 : ∀ a : Fin 16, extension ⟨(0*16+a.val)%241, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
set_option maxRecDepth 4096 in
private theorem ext_block_1 : ∀ a : Fin 16, extension ⟨(1*16+a.val)%241, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
set_option maxRecDepth 4096 in
private theorem ext_block_2 : ∀ a : Fin 16, extension ⟨(2*16+a.val)%241, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
set_option maxRecDepth 4096 in
private theorem ext_block_3 : ∀ a : Fin 16, extension ⟨(3*16+a.val)%241, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
set_option maxRecDepth 4096 in
private theorem ext_block_4 : ∀ a : Fin 16, extension ⟨(4*16+a.val)%241, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
set_option maxRecDepth 4096 in
private theorem ext_block_5 : ∀ a : Fin 16, extension ⟨(5*16+a.val)%241, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
set_option maxRecDepth 4096 in
private theorem ext_block_6 : ∀ a : Fin 16, extension ⟨(6*16+a.val)%241, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
set_option maxRecDepth 4096 in
private theorem ext_block_7 : ∀ a : Fin 16, extension ⟨(7*16+a.val)%241, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
set_option maxRecDepth 4096 in
private theorem ext_block_8 : ∀ a : Fin 16, extension ⟨(8*16+a.val)%241, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
set_option maxRecDepth 4096 in
private theorem ext_block_9 : ∀ a : Fin 16, extension ⟨(9*16+a.val)%241, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
set_option maxRecDepth 4096 in
private theorem ext_block_10 : ∀ a : Fin 16, extension ⟨(10*16+a.val)%241, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
set_option maxRecDepth 4096 in
private theorem ext_block_11 : ∀ a : Fin 16, extension ⟨(11*16+a.val)%241, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
set_option maxRecDepth 4096 in
private theorem ext_block_12 : ∀ a : Fin 16, extension ⟨(12*16+a.val)%241, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
set_option maxRecDepth 4096 in
private theorem ext_block_13 : ∀ a : Fin 16, extension ⟨(13*16+a.val)%241, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
set_option maxRecDepth 4096 in
private theorem ext_block_14 : ∀ a : Fin 16, extension ⟨(14*16+a.val)%241, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
set_option maxRecDepth 4096 in
private theorem ext_block_15 : ∀ a : Fin 16, extension ⟨(15*16+a.val)%241, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
theorem extensions (r : Fin 241) : extension r := by
  have aux (d m : Fin 16) :
      extension ⟨(d.val*16+m.val)%241, Nat.mod_lt _ (by decide)⟩ := by
    fin_cases d
    · exact ext_block_0 m
    · exact ext_block_1 m
    · exact ext_block_2 m
    · exact ext_block_3 m
    · exact ext_block_4 m
    · exact ext_block_5 m
    · exact ext_block_6 m
    · exact ext_block_7 m
    · exact ext_block_8 m
    · exact ext_block_9 m
    · exact ext_block_10 m
    · exact ext_block_11 m
    · exact ext_block_12 m
    · exact ext_block_13 m
    · exact ext_block_14 m
    · exact ext_block_15 m
  let d : Fin 16 := ⟨r.val / 16, by omega⟩
  let m : Fin 16 := ⟨r.val % 16, Nat.mod_lt _ (by decide)⟩
  have he : (⟨(d.val*16+m.val)%241, Nat.mod_lt _ (by decide)⟩ : Fin 241) = r := by
    apply Fin.ext
    dsimp [d,m]
    omega
  exact he ▸ aux d m
end BinaryPermutation.EightElementaryCertificate
