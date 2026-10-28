module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.CentralKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.Doubled

/-!
# The complete trichotomy for the actual moving layer

The U action is faithful, commutator-generated and an FF-module. Recognition
and the cohomological kernel bound yield exactly three possibilities: U is
natural, U is two commonly marked natural copies, or U has a fixed subgroup
of order two with natural quotient. Every assertion uses actual equivariant
maps on U = [Z,Ltilde]. The one-copy isomorphism is constructed only after
proving its kernel trivial.

These are moving-layer conclusions. The reconstruction of X and Z, and the
bad-case local estimates, remain required for the full MS93 (3.2) alternatives.
Source: Meierfrankenfeld–Stellmacher (1993), printed p.863.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- A one-copy quotient with zero central kernel identifies the actual U
with the natural module, with the original marking and action equation. -/
noncomputable def MovingQuotient.oneNatural (source : LocalSource L R)
    (q : MovingQuotient source 1) (hd : Disjoint (fixedPart R) (U R (alpha R))) :
    NaturalU R source.projection := by
  let p : U R (alpha R) →* Multiplicative (Fin 3 → ZMod 2) := {
    toFun := fun u => Multiplicative.ofAdd ((q.projection u).toAdd 0)
    map_one' := by rw [q.projection.map_one]; rfl
    map_mul' := fun u v => by rw [q.projection.map_mul]; rfl }
  have hi : Function.Injective p := by
    apply p.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro u hu
    change (q.projection u).toAdd 0 = 0 at hu
    have hq : q.projection u = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      change (q.projection u).toAdd i = 0
      simpa only [Subsingleton.elim i 0] using hu
    have hc : (u : FreeAmalgam R) ∈ fixedPart R := by
      have hk : u ∈ q.projection.ker := hq
      rwa [q.kernel] at hk
    have he : (u : FreeAmalgam R) = 1 := disjoint_iff_inf_le.mp hd ⟨hc, u.property⟩
    exact Subtype.ext he
  have hs : Function.Surjective p := by
    intro v
    obtain ⟨u, hu⟩ := q.onto (Multiplicative.ofAdd (fun _ => v.toAdd))
    exact ⟨u, congrArg (fun w => Multiplicative.ofAdd (w.toAdd 0)) hu⟩
  refine {
    marking := q.marking
    equiv := MulEquiv.ofBijective p ⟨hi, hs⟩
    normalized := ?_
    action := ?_ }
  · simpa only [alpha, stabilizer_m_base] using U_normalized (R := R) (alpha R)
  · intro g u v hv
    exact q.action g u v hv 0

variable [Finite M]

/-- The complete moving-layer trichotomy, proved on U = [Z,Ltilde]: natural,
two natural copies with one marking, or a central extension of a natural module
with kernel of order two. Reconstructing X and Z is a further source obligation. -/
theorem moving_layer_trichotomy (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) :
    (Nonempty (NaturalU R source.projection) ∧ Disjoint (fixedPart R) (U R (alpha R))) ∨
    (Nonempty (MovingCopies source 2) ∧ Disjoint (fixedPart R) (U R (alpha R))) ∨
    (Nonempty (MovingQuotient source 1) ∧
      Nat.card (fixedPart R ⊓ U R (alpha R) : Subgroup (FreeAmalgam R)) = 2) := by
  rcases moving_quotient_or_double source geometry hb with h | h
  · obtain ⟨q⟩ := h
    have hc := q.one_kernel_card_le_two source geometry hb
    by_cases he : Nat.card (fixedPart R ⊓ U R (alpha R) : Subgroup (FreeAmalgam R)) = 2
    · exact Or.inr (Or.inr ⟨⟨q⟩, he⟩)
    have hfinite : Finite (fixedPart R ⊓ U R (alpha R) : Subgroup (FreeAmalgam R)) := by
      let := finite_X R (alpha R)
      exact Finite.of_injective (inclusion (inf_le_left.trans (show fixedPart R ≤ X R (alpha R) from inf_le_left)))
        (inclusion_injective _)
    let := hfinite
    have hpos : 0 < Nat.card (fixedPart R ⊓ U R (alpha R) : Subgroup (FreeAmalgam R)) := Nat.card_pos
    have hone : Nat.card (fixedPart R ⊓ U R (alpha R) : Subgroup (FreeAmalgam R)) = 1 := by omega
    have hd : Disjoint (fixedPart R) (U R (alpha R)) :=
      disjoint_iff.mpr (Subgroup.card_eq_one.mp hone)
    exact Or.inl ⟨⟨q.oneNatural source hd⟩, hd⟩
  · exact Or.inr (Or.inl h)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
