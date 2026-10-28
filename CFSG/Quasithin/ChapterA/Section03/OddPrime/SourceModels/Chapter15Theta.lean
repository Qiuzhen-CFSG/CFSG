module

public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
public import CFSG.Quasithin.Chapter15.Section03.Constructions

/-!
# The theta clause in the Chapter 15 convention

A.3.18 states an equality internal to H. Section 15.3 uses theta(I) as
an ambient subgroup of G. Mapping through the actual inclusion I → G
identifies these definitions, preserving the order-three generators.
This supplies the literal theta equality needed by the 15.3.26 rank sieve.

Source: Aschbacher--Smith, A.3.17--18, pp.51--52, and 15.3.26, p.1130.
-/

@[expose] public section
noncomputable section

open Subgroup

namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels

variable {G : Type*} [Group G]

/-- The actual inclusion takes intrinsic theta to Section 15.3's ambient theta. -/
theorem theta_map_subtype (I : Subgroup G) :
    (theta I).map I.subtype = Chapter15.Section03.theta I := by
  rw [theta, Chapter15.Section03.theta, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, (Subgroup.orderOf_coe y).trans hy⟩
  · rintro ⟨hx, ho⟩
    exact ⟨⟨x, hx⟩, (Subgroup.orderOf_coe ⟨x, hx⟩).symm.trans ho, rfl⟩

/-- A.3.18(3a) becomes exactly the ambient equality used in the rank sieve. -/
theorem theta_clause_iff {L I : Subgroup G} (hLI : L ≤ I) :
    L.subgroupOf I = theta I ↔ L = Chapter15.Section03.theta I := by
  constructor
  · intro h
    calc
      L = (L.subgroupOf I).map I.subtype := (map_subgroupOf_eq_of_le hLI).symm
      _ = (theta I).map I.subtype := congrArg (Subgroup.map I.subtype) h
      _ = Chapter15.Section03.theta I := theta_map_subtype I
  · intro h
    apply Subgroup.map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le hLI, theta_map_subtype, h]

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
