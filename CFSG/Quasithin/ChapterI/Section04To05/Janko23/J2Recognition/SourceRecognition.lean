module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.ConcreteSystem.Recognition
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.ConcreteSystem.TriangleCertificate

/-!
# The simple-source specialization of I.4.7(1)

The original involution-centralizer seed constructs compatible vertex and local
isomorphisms, including both edge stabilizer conditions. The checked cycle base
of the literal ATLAS subgroup graph extends their inverses to a surjective
homomorphism onto the arbitrary source group. The independently established
source and target orders make this homomorphism bijective.

Thus neither local comparison nor any graph, generation, order, catalogue or
recognition callback remains in the final J₂-type theorem. The cycle base uses
a finite triangle reduction on the target; no target simplicity theorem is
required. The source simplicity hypothesis is exactly the one available in
the original terminal-solvability context.

Source: Aschbacher–Smith I.4.7(1), p.418; Aschbacher, *Sporadic Groups*
(1994), §§34–37 and 47, especially 47.10, pp.266–267.
-/

public section
namespace CFSG.Quasithin.Janko23.J2Recognition
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The actual source seed recognizes the concrete Hall–Janko carrier. -/
theorem recognition_of_seed (D : Seed G) :
    Nonempty (G ≃* Sporadic.LeechRelated.J2.Carrier) :=
  ConcreteSystem.recognition_of_concrete_base D ConcreteSystem.TriangleCertificate.isBase

/-- I.4.7(1) in the original simple-source context, with no additional premises. -/
theorem recognition (h : J2Type G) :
    Nonempty (G ≃* Sporadic.LeechRelated.J2.Carrier) := by
  obtain ⟨D⟩ := exists_seed h
  exact recognition_of_seed D

end CFSG.Quasithin.Janko23.J2Recognition
