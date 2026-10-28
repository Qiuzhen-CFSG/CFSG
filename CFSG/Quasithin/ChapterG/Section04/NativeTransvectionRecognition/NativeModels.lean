module
public import CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition.CarrierRows
public import CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition.ExceptionalModels

/-!
# The actual one-centralizer degree-four shortlist

The exceptional degree-four exclusions complete the carrier dispatcher.
Nonsolvability, one literal involution with two-group centralizer, and the
faithful characteristic-two symplectic four-space action leave precisely
A₅, A₆, binary PSL₂, Suzuki and binary PSp₄. No normalizing rank-one actor
or all-involution centralizer premise is used. Coefficient-model recognition
is a separate representation statement. Source: Aschbacher--Smith G.4.1,
printed p.342, the first model inspection.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition
open Subgroup Theory.SpecificGroups.SymplecticFour
open ChapterA.Section02
variable {H F:Type*} [Group H] [Field F] [CharP F 2]

/-- Complete native carrier shortlist from the literal degree-four action
and one two-group involution centralizer. -/
theorem native_of_theoremC (hns:¬Group.IsSolvable H) (hm:IsTheoremCModel H)
    (t:H) (ht:orderOf t=2) (hc:IsPGroup 2 (centralizer ({t}:Set H)))
    (j:H→*Sp F) (hj:Function.Injective j) : IsNativeDegreeFourCarrier H := by
  rcases native_or_exceptional_of_theoremC hns hm t ht hc j hj with h|h
  · exact h
  rcases h with ⟨n,hn,h⟩|⟨m,_,h⟩|h
  · exact (not_binary_triality_model (by omega) j hj h).elim
  · exact (not_ree_model m j hj h).elim
  · exact (not_tits_model j hj h).elim

/-- The same complete shortlist for the original embedded subgroup and its
literal c₂ witness. -/
theorem subgroup_native_of_one_isC2 [Finite F] {n:ℕ} (hF:Nat.card F=2^n)
    (N:Subgroup (Sp F)) (hns:¬Group.IsSolvable N) (hm:IsTheoremCModel N)
    (i:N) (hi:InvolutionTypes.IsC2 (i:Sp F)) : IsNativeDegreeFourCarrier N := by
  rcases subgroup_native_or_exceptional_of_one_isC2 hF N hns hm i hi with h|h
  · exact h
  rcases h with ⟨f,hf,h⟩|⟨m,_,h⟩|h
  · exact (not_binary_triality_model (by omega) N.subtype N.subtype_injective h).elim
  · exact (not_ree_model m N.subtype N.subtype_injective h).elim
  · exact (not_tits_model N.subtype N.subtype_injective h).elim
end CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition
