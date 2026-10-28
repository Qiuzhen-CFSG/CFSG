module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.ModelGeometry.Basic
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.ModelGeometry.RootGeneration
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.ModelGeometry.PlaneResidual
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.ModelGeometry.Transitivity

/-!
# Concrete model inputs for the G.2.5 dual geometry

The exact model equivalence supplies the marked natural frame, identifies the
printed natural and dual root groups, proves stabilization of the indicated
second point, and computes the common dual fixed space of the first two point
radicals. These results concern the actual matrix action over F, including F₂.

The two roots through each frame point generate its point radical, and the
six frame roots generate SL₃(F). The pair-plane stabilizer is the literal
product of the first two radicals' join and the common point stabilizer;
that join is its embedded relative prime-to-two residual. Ordered frames,
distinct point pairs and incident flags are transitive, and each flag
stabilizer is transitive on the other points of its axis, for both the natural
and genuine dual actions. All of these model inputs include F₂.

The ambient U* identification, lifting to I, global binary quotient point
map and Projective.Criterion assembly remain with their source owners.

Source: Aschbacher–Smith, G.1.1–4 and G.2.5, printed pp.327–328,335–336.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
open Subgroup Setup Projective
namespace DualGeometry.ModelGeometry
open CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)

/-- An actor fixing the actual dual point factors as a product of an element
of the two-radical group and an actor fixing both natural marks. This is the
model factorization used to extend the marked dual-point assignment in G.2.5. -/
theorem dualPoint_stabilizer_decomposition (a : D.star D.L)
    (ha : (dualPoint d).val.map (dualAction d a) = (dualPoint d).val) :
    ∃ r ∈ rootGroup (naturalAction d) d.point d.point ⊔
        rootGroup (naturalAction d) (conjugatePoint d ⟨g, d.g_mem⟩).val
          (conjugatePoint d ⟨g, d.g_mem⟩).val,
      ∃ t : D.star D.L, d.point.map (naturalAction d t) = d.point ∧
        (conjugatePoint d ⟨g, d.g_mem⟩).val.map (naturalAction d t) =
          (conjugatePoint d ⟨g, d.g_mem⟩).val ∧ a = r * t := by
  have hp : a ∈ naturalStabilizer d (pairPlane d) :=
    (mem_naturalStabilizer_iff d _ a).mpr ((dualPoint_stabilizer_iff d a).mp ha)
  have hs : a ∈ (naturalStabilizer d (pairPlane d) : Set (D.star D.L)) := hp
  rw [pair_plane_factorization] at hs
  obtain ⟨r, hr, t, ht, he⟩ := Set.mem_mul.mp hs
  exact ⟨r, hr, t, (mem_naturalStabilizer_iff d _ t).mp ht.1,
    (mem_naturalStabilizer_iff d _ t).mp ht.2, he.symm⟩

/-- The embedded relative prime-to-two residual fixes exactly the marked
annihilator line in the genuine F-linear dual representation. -/
theorem pair_plane_residual_dual_fixed :
    Representation.invariants ((dualAction d).comp
      ((piResidual {p : Nat.Primes | p.val ≠ 2} (naturalStabilizer d (pairPlane d))).map
        (naturalStabilizer d (pairPlane d)).subtype).subtype) = pairAnnihilator d := by
  rw [← pair_plane_oddResidual]
  exact pair_radicals_dual_fixed d

end DualGeometry.ModelGeometry
end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
