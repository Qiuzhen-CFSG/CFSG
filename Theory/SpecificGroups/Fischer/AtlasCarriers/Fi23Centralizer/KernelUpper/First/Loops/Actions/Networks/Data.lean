module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Actions.Networks.Source
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Actions.Networks.Core0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Actions.Networks.Core1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Actions.Networks.Core2

/-!
# Numerical bit transforms for Fi23 loop certificates

The transforms are fixed before any family check. The source-map and
core-map semantic certificates are independent of the loop mask equalities.

Source: retained ATLAS F23G1-p31671B0, inverse-cycle convention; GLS3
Table 5.3u. The generator and provenance are in `Actions/source/`.
-/

set_option Elab.async false

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops.Actions
open Sporadic.Fischer.Fi22.KernelCertificate

def coreNetwork (i : Nat) : List BitNetwork.Stage :=
  match i with
  | 1 => network1
  | 2 => network2
  | 3 => network3
  | 4 => network4
  | 7 => network7
  | 9 => network9
  | 11 => network11
  | 16 => network16
  | 18 => network18
  | 20 => network20
  | 35 => network35
  | 48 => network48
  | 49 => network49
  | 50 => network50
  | 52 => network52
  | 54 => network54
  | 66 => network66
  | 67 => network67
  | 72 => network72
  | 74 => network74
  | 76 => network76
  | 91 => network91
  | 101 => network101
  | 102 => network102
  | 103 => network103
  | 105 => network105
  | 107 => network107
  | 116 => network116
  | 117 => network117
  | 128 => network128
  | 137 => network137
  | 138 => network138
  | 139 => network139
  | 141 => network141
  | 143 => network143
  | 154 => network154
  | 158 => network158
  | 159 => network159
  | 179 => network179
  | 181 => network181
  | 182 => network182
  | 192 => network192
  | 193 => network193
  | 200 => network200
  | 202 => network202
  | 203 => network203
  | 214 => network214
  | 217 => network217
  | 218 => network218
  | _ => []

def coreTransform (i : Nat) : Nat → Nat := BitNetwork.apply (coreNetwork i)

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops.Actions
