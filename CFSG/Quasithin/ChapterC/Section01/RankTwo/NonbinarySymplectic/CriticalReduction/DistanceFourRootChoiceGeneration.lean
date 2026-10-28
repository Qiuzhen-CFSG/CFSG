module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalTerminalPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TerminalKernelSaturation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootSplitting
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalTerminalPaths

/-!
# Same-selector generation from the retained root-choice disjunction

An existing source choice has two alternatives: individual residual generation
by the same actor, or failure of the full X decomposition. If a root successor
retains the same selected vertex and its directed index is q, reciprocal
critical-index transport gives the q-sized root image at the selected vertex.
The root X decomposition then transports to the preceding vertex, eliminating
the nonsplitting alternative. Thus the retained selector gives the exact
individual-generation inclusion needed by the full-kernel budget, without a
strict backward-index obstruction or a selector substitution.

The same-actor choice certificate remains an explicit hypothesis. This lemma
does not construct it from the equal/small three-generator certificate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

private theorem x_split_transport
    {M : Type*} [Group M] {S : Subgroup M}
    {a c : Vertex S} (ha : color S a=false) (hc : color S c=false)
    (hs : X S a=U S a ⊔ (X S a ⊓ centralizer (stabilizer S a : Set (FreeAmalgam S)))) :
    X S c=U S c ⊔ (X S c ⊓ centralizer (stabilizer S c : Set (FreeAmalgam S))) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color S ha
  obtain ⟨j,hj⟩ := exists_mVertex_of_color S hc
  have hy : act S (g⁻¹*j) a=c := by
    rw [hg,act_mVertex,mul_inv_cancel_left,←hj]
  have hm := congrArg (Subgroup.map (MulAut.conj (g⁻¹*j)⁻¹).toMonoidHom) hs
  rw [Subgroup.map_sup,map_inf _ _ _ (MulAut.conj (g⁻¹*j)⁻¹).injective,
    Theory.GroupTheory.map_centralizer_equiv] at hm
  change (X S a).map (MulAut.conj (g⁻¹*j)⁻¹).toMonoidHom =
    (U S a).map (MulAut.conj (g⁻¹*j)⁻¹).toMonoidHom ⊔
    (X S a).map (MulAut.conj (g⁻¹*j)⁻¹).toMonoidHom ⊓
      centralizer (((stabilizer S a).map (MulAut.conj (g⁻¹*j)⁻¹).toMonoidHom :
        Subgroup (FreeAmalgam S)) : Set _) at hm
  rwa [←X_act,←U_act,←stabilizer_act,hy] at hm

include h

theorem Input.replacement_distance_four_root_choice_generation
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    {a v s : Vertex d.radical}
    (hb : 4 ≤ geometry.b d.radical)
    (next : CriticalPath d.radical geometry v a)
    (hroot : (Q d.radical a).relIndex (Z d.radical v)=Nat.card F)
    (hchoice : unequalPathChoice geometry (Nat.card F) p v s) :
    Ltilde d.radical p.first ≤
      Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical p.last := by
  have hsmall : (Q d.radical v).relIndex (Z d.radical a)<Nat.card F^2 := by
    rw [←h.replacement_critical_indices_equal d next hb,hroot]
    have hq : 1<Nat.card F := Finite.one_lt_card
    nlinarith
  have hsplitV := h.replacement_root_X_decomposition_center d next hb hsmall
  have hsplit := x_split_transport next.start_color p.path.start_color hsplitV
  exact hchoice.2.2.2.resolve_right (fun hbad => hbad hsplit)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
