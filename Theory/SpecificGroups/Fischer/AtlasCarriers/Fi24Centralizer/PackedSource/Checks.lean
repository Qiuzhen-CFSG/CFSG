module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.PackedSource.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorData
/-!
# Block certificates for the original Fi24 generator lookups

A closed check compares 256 consecutive fields at once with the existing
source-certified generator tables. The final block contains eight zero fields.
All arithmetic equalities are checked by the kernel; the data generator is
not part of the trusted proof.
-/
namespace Sporadic.Fischer.Fi24Prime.CentralizerSection.PackedSource
open Fi23Lift.Certificate.Ambient

private def checkBlock (x : Nat) (blocks : Nat → Nat) (b : Nat) : Bool :=
  if b < 1199 then (((x >>> (19*256*b)) % 2^(19*256)) == blocks b) else true

private def check64 (x : Nat) (blocks : Nat → Nat) (k : Nat) : Bool :=
  (List.range 64).all fun i => checkBlock x blocks (64*k+i)
private theorem aCheck0 : check64 packedA aBlocks 0 = true := by decide +kernel
private theorem aCheck1 : check64 packedA aBlocks 1 = true := by decide +kernel
private theorem aCheck2 : check64 packedA aBlocks 2 = true := by decide +kernel
private theorem aCheck3 : check64 packedA aBlocks 3 = true := by decide +kernel
private theorem aCheck4 : check64 packedA aBlocks 4 = true := by decide +kernel
private theorem aCheck5 : check64 packedA aBlocks 5 = true := by decide +kernel
private theorem aCheck6 : check64 packedA aBlocks 6 = true := by decide +kernel
private theorem aCheck7 : check64 packedA aBlocks 7 = true := by decide +kernel
private theorem aCheck8 : check64 packedA aBlocks 8 = true := by decide +kernel
private theorem aCheck9 : check64 packedA aBlocks 9 = true := by decide +kernel
private theorem aCheck10 : check64 packedA aBlocks 10 = true := by decide +kernel
private theorem aCheck11 : check64 packedA aBlocks 11 = true := by decide +kernel
private theorem aCheck12 : check64 packedA aBlocks 12 = true := by decide +kernel
private theorem aCheck13 : check64 packedA aBlocks 13 = true := by decide +kernel
private theorem aCheck14 : check64 packedA aBlocks 14 = true := by decide +kernel
private theorem aCheck15 : check64 packedA aBlocks 15 = true := by decide +kernel
private theorem aCheck16 : check64 packedA aBlocks 16 = true := by decide +kernel
private theorem aCheck17 : check64 packedA aBlocks 17 = true := by decide +kernel
private theorem aCheck18 : check64 packedA aBlocks 18 = true := by decide +kernel

private theorem aChecks (k : Fin 19) : check64 packedA aBlocks k = true :=
  match k with
  | ⟨0,_⟩ => aCheck0
  | ⟨1,_⟩ => aCheck1
  | ⟨2,_⟩ => aCheck2
  | ⟨3,_⟩ => aCheck3
  | ⟨4,_⟩ => aCheck4
  | ⟨5,_⟩ => aCheck5
  | ⟨6,_⟩ => aCheck6
  | ⟨7,_⟩ => aCheck7
  | ⟨8,_⟩ => aCheck8
  | ⟨9,_⟩ => aCheck9
  | ⟨10,_⟩ => aCheck10
  | ⟨11,_⟩ => aCheck11
  | ⟨12,_⟩ => aCheck12
  | ⟨13,_⟩ => aCheck13
  | ⟨14,_⟩ => aCheck14
  | ⟨15,_⟩ => aCheck15
  | ⟨16,_⟩ => aCheck16
  | ⟨17,_⟩ => aCheck17
  | ⟨18,_⟩ => aCheck18
  | ⟨n+19,h⟩ => False.elim (by omega)

public theorem packedA_block (b : Nat) (hb : b < 1199) :
    (packedA >>> (19*(256*b))) % 2^(19*256) = aBlocks b := by
  have hk : b/64 < 19 := by omega
  have h := (List.all_eq_true.mp (aChecks ⟨b/64,hk⟩)) (b%64)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have he : 64*(b/64)+b%64=b := Nat.div_add_mod b 64
  change checkBlock packedA aBlocks (64*(b/64)+b%64) = true at h
  rw [he] at h
  simpa only [checkBlock, hb, ↓reduceIte, beq_iff_eq, Nat.mul_assoc] using h

private theorem bCheck0 : check64 packedB bBlocks 0 = true := by decide +kernel
private theorem bCheck1 : check64 packedB bBlocks 1 = true := by decide +kernel
private theorem bCheck2 : check64 packedB bBlocks 2 = true := by decide +kernel
private theorem bCheck3 : check64 packedB bBlocks 3 = true := by decide +kernel
private theorem bCheck4 : check64 packedB bBlocks 4 = true := by decide +kernel
private theorem bCheck5 : check64 packedB bBlocks 5 = true := by decide +kernel
private theorem bCheck6 : check64 packedB bBlocks 6 = true := by decide +kernel
private theorem bCheck7 : check64 packedB bBlocks 7 = true := by decide +kernel
private theorem bCheck8 : check64 packedB bBlocks 8 = true := by decide +kernel
private theorem bCheck9 : check64 packedB bBlocks 9 = true := by decide +kernel
private theorem bCheck10 : check64 packedB bBlocks 10 = true := by decide +kernel
private theorem bCheck11 : check64 packedB bBlocks 11 = true := by decide +kernel
private theorem bCheck12 : check64 packedB bBlocks 12 = true := by decide +kernel
private theorem bCheck13 : check64 packedB bBlocks 13 = true := by decide +kernel
private theorem bCheck14 : check64 packedB bBlocks 14 = true := by decide +kernel
private theorem bCheck15 : check64 packedB bBlocks 15 = true := by decide +kernel
private theorem bCheck16 : check64 packedB bBlocks 16 = true := by decide +kernel
private theorem bCheck17 : check64 packedB bBlocks 17 = true := by decide +kernel
private theorem bCheck18 : check64 packedB bBlocks 18 = true := by decide +kernel

private theorem bChecks (k : Fin 19) : check64 packedB bBlocks k = true :=
  match k with
  | ⟨0,_⟩ => bCheck0
  | ⟨1,_⟩ => bCheck1
  | ⟨2,_⟩ => bCheck2
  | ⟨3,_⟩ => bCheck3
  | ⟨4,_⟩ => bCheck4
  | ⟨5,_⟩ => bCheck5
  | ⟨6,_⟩ => bCheck6
  | ⟨7,_⟩ => bCheck7
  | ⟨8,_⟩ => bCheck8
  | ⟨9,_⟩ => bCheck9
  | ⟨10,_⟩ => bCheck10
  | ⟨11,_⟩ => bCheck11
  | ⟨12,_⟩ => bCheck12
  | ⟨13,_⟩ => bCheck13
  | ⟨14,_⟩ => bCheck14
  | ⟨15,_⟩ => bCheck15
  | ⟨16,_⟩ => bCheck16
  | ⟨17,_⟩ => bCheck17
  | ⟨18,_⟩ => bCheck18
  | ⟨n+19,h⟩ => False.elim (by omega)

public theorem packedB_block (b : Nat) (hb : b < 1199) :
    (packedB >>> (19*(256*b))) % 2^(19*256) = bBlocks b := by
  have hk : b/64 < 19 := by omega
  have h := (List.all_eq_true.mp (bChecks ⟨b/64,hk⟩)) (b%64)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have he : 64*(b/64)+b%64=b := Nat.div_add_mod b 64
  change checkBlock packedB bBlocks (64*(b/64)+b%64) = true at h
  rw [he] at h
  simpa only [checkBlock, hb, ↓reduceIte, beq_iff_eq, Nat.mul_assoc] using h

end Sporadic.Fischer.Fi24Prime.CentralizerSection.PackedSource
