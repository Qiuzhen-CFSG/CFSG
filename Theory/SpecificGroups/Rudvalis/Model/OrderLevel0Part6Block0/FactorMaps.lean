module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Soundness
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.FirstCheck
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Checks0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Checks1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Checks2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Checks3
import Mathlib.Tactic.FinCases

/-!
# Certified cached factor maps for Rudvalis block 0

Shared-word composition certificates certify at most ten cached lookups per
factor. Twenty-point slice checks then transfer to the original transition
identities, using the decoded factor words and the two representative words.
Source: the ATLAS witnesses in FactorWords and FactorMaps/source/README.md.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
set_option Elab.async false
set_option maxRecDepth 30000

private theorem compositions : ∀ j, CompositionCheck j := by
  intro j
  fin_cases j
  · exact comp4
  · exact comp5
  · exact comp6
  · exact comp7
  · exact comp8
  · exact comp9
  · exact comp10
  · exact comp11
  · exact comp12
  · exact comp13
  · exact comp14
  · exact comp15
  · exact comp16
  · exact comp17
  · exact comp18
  · exact comp19
  · exact comp20
  · exact comp21
  · exact comp22
  · exact comp23
  · exact comp24
  · exact comp25
  · exact comp26
  · exact comp27
  · exact comp28
  · exact comp29
  · exact comp30
  · exact comp31
  · exact comp32
  · exact comp33
  · exact comp34
  · exact comp35
  · exact comp36
  · exact comp37
  · exact comp38
  · exact comp39
  · exact comp40
  · exact comp41
  · exact comp42
  · exact comp43
  · exact comp44
  · exact comp45
  · exact comp46
  · exact comp47
  · exact comp48
  · exact comp49
  · exact comp50
  · exact comp51
  · exact comp52
  · exact comp53
  · exact comp54
  · exact comp55
  · exact comp56
  · exact comp57
  · exact comp58
  · exact comp59
  · exact comp60
  · exact comp61
  · exact comp62
  · exact comp63
  · exact comp64
  · exact comp65
  · exact comp66
  · exact comp67
  · exact comp68
  · exact comp69
  · exact comp70
  · exact comp71
  · exact comp72
  · exact comp73
  · exact comp74
  · exact comp75
  · exact comp76
  · exact comp77
  · exact comp78
  · exact comp79
  · exact comp80
  · exact comp81
  · exact comp82
  · exact comp83
  · exact comp84
  · exact comp85
  · exact comp86
  · exact comp87
  · exact comp88
  · exact comp89
  · exact comp90
  · exact comp91
  · exact comp92
  · exact comp93
  · exact comp94
  · exact comp95
  · exact comp96
  · exact comp97
  · exact comp98
  · exact comp99
  · exact comp100
  · exact comp101
  · exact comp102
  · exact comp103
  · exact comp104
  · exact comp105
  · exact comp106
  · exact comp107
  · exact comp108
  · exact comp109
  · exact comp110
  · exact comp111
  · exact comp112
  · exact comp113
  · exact comp114
  · exact comp115
  · exact comp116
  · exact comp117
  · exact comp118
  · exact comp119
  · exact comp120
  · exact comp121
  · exact comp122
  · exact comp123
  · exact comp124

/-- The cached evaluator agrees with the published factor-word action. -/
public theorem map_eq (k : Fin 100) (x : Fin 4060) : map k x.val =
    (Part6Tables.eval Part6Tables.gen1 (FactorWords.word k) x).val :=
  map_eq_of_compositions compositions k x

/-- A twenty-point transition check using the certified factor cache. -/
@[expose] public def slice (k : Fin 100) (w v : List (Fin 4)) (b : Fin 203) : Bool :=
  cachedSlice (map k) (FactorWords.row k).1 w v b

/-- Cached slices and the two representative words certify the original step. -/
public theorem ofSlices (k : Fin 100) (w v : List (Fin 4))
    (hw : L0RepWord (FactorWords.row k).2 = w)
    (hv : L0RepWord (L0Act ((FactorWords.row k).1.castLE (by decide))
      (FactorWords.row k).2) = v)
    (h : ∀ b, slice k w v b = true) :
    stepCheck (FactorWords.row k).1 (FactorWords.row k).2 :=
  ofCachedSlices k (map k) (map_eq k) w v hw hv h

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
