module
public import GorensteinWalter.NormalSL2ProjectiveImage
public import GorensteinWalter.NormalPSL2IndexTwoPGL

/-!
# PGL₂ projection from a central SL₂ extension

A central quotient containing the actual image of a normal `SL₂(F)` subgroup
has a canonical `PSL₂(F)` subgroup.  When that subgroup has index two and the
quotient has dihedral Sylow two-subgroups, the prescribed index-two recognition
identifies the quotient with `PGL₂(F)`.  Composing this recognition with the
quotient map gives the required surjection; the element equation is retained
through the supplied `SL₂` identification, and the inverse image of the
canonical projective `PSL₂` range is exactly the central join.

This is the quotient-and-projection step in Alperin--Brauer--Gorenstein,
Chapter II, Section 3, Proposition 3 (article page 26).  The central subgroup
is not required to be the full ambient center, and no odd-core or field-action
hypothesis is added.
-/

namespace GorensteinWalter

universe u v

public theorem exists_pgl2_projection_of_central_sl2_join_index_two
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (C M : Subgroup G) [C.Normal] [M.Normal]
    (hCcentral : C ≤ Subgroup.center G)
    (hSC : (Subgroup.center (S : Subgroup G)).map
      (S : Subgroup G).subtype ≤ C)
    (hjoin : (C ⊔ M).index = 2)
    (hGd : HasDihedralSylowTwo (G ⧸ C))
    (F : Type v) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F))
    (eM : M ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ f : G →* PGL2 F, Function.Surjective f ∧ f.ker = C ∧
      (∀ m : M, f m = Matrix.ProjectiveSpecialLinearGroup.toPGL (sl2ProjectiveProjection F (eM m))) ∧
      (Subgroup.comap f (Matrix.ProjectiveSpecialLinearGroup.toPGL.range)) = C ⊔ M := by
  classical
  let q : G →* (G ⧸ C) := QuotientGroup.mk' C
  let N : Subgroup (G ⧸ C) := M.map q
  let : N.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective C)
  have hNindex : N.index = 2 := by
    change (M.map q).index = 2
    rw [Subgroup.index_map, QuotientGroup.ker_mk',
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective C),
      Subgroup.index_top, mul_one, sup_comm]
    simpa [sup_comm] using hjoin
  obtain ⟨eImage, heImage⟩ := exists_normal_sl2_projective_image S C M
    hCcentral hSC F hF eM
  let eN : N ≃* PSL2 F := eImage
  obtain ⟨eQ, heQ⟩ := exists_mulEquiv_pgl2_of_normal_psl2_index_two
    hGd N hNindex F hF eN
  let f : G →* PGL2 F := eQ.toMonoidHom.comp q
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨n, hn⟩ := eQ.surjective y
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective C n
    exact ⟨g, by simpa [f, q, hn] using congrArg eQ hg⟩
  have hfker : f.ker = C := by
    ext g
    change eQ (q g) = 1 ↔ g ∈ C
    constructor
    · intro hg
      apply (QuotientGroup.eq_one_iff g).mp
      exact eQ.injective (hg.trans (eQ.map_one).symm)
    · intro hg
      have hq : q g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
      simpa only [map_one] using congrArg eQ hq
  have hNmap : N.map eQ.toMonoidHom = Matrix.ProjectiveSpecialLinearGroup.toPGL.range := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨eN ⟨n, hn⟩, (heQ ⟨n, hn⟩).symm⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨n, hn⟩ := eImage.surjective a
      exact ⟨n, n.property, (heQ n).trans (congrArg
        (Matrix.ProjectiveSpecialLinearGroup.toPGL) hn)⟩
  have hfpre : Subgroup.comap f Matrix.ProjectiveSpecialLinearGroup.toPGL.range =
      C ⊔ M := by
    change Subgroup.comap q (Subgroup.comap eQ.toMonoidHom Matrix.ProjectiveSpecialLinearGroup.toPGL.range) = _
    have hcomap : Subgroup.comap eQ.toMonoidHom Matrix.ProjectiveSpecialLinearGroup.toPGL.range = N := by
      rw [← hNmap, Subgroup.comap_map_eq]
      rw [MonoidHom.ker_eq_bot _ eQ.injective]
      simp
    rw [hcomap, Subgroup.comap_map_eq]
    simp [q, sup_comm]
  refine ⟨f, hf_surj, hfker, ?_, hfpre⟩
  intro m
  change eQ (q m) = _
  calc
    eQ (q m) = Matrix.ProjectiveSpecialLinearGroup.toPGL (eN ⟨q m, ⟨m, m.property, rfl⟩⟩) :=
      heQ ⟨q m, ⟨m, m.property, rfl⟩⟩
    _ = Matrix.ProjectiveSpecialLinearGroup.toPGL (sl2ProjectiveProjection F (eM m)) := by
      exact congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL (heImage m)

end GorensteinWalter
