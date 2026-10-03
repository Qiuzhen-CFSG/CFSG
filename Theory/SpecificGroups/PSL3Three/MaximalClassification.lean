module

public import Theory.SpecificGroups.PSL3Three.CandidateMaximality
public import Theory.SpecificGroups.PSL3Three.ProperCover

/-!
# Maximal subgroups of PSL₃(3)

The maximal subgroups are precisely the conjugates of the specified line
stabilizer, plane stabilizer, monomial subgroup, and Singer normalizer.
In particular the irreducible monomial subgroup is included as an actual
matrix subgroup, without identifying it by its order or abstract isomorphism type.

The checked finite extension certificate in `ProperCover` places every proper
SL₃(3) subgroup in a conjugate of one of the four candidates. Independently,
`CandidateMaximality` proves that each candidate is maximal. The canonical
isomorphism SL₃(3) ≃ PSL₃(3) preserves conjugation and transports both results;
maximality then turns the covering inclusions into equalities.

Source: GLS III, Theorem 6.5.3(a–c), in `refs/KGroup/GLS3/chapter6.tex`.
The printed statement omits the necessary proper-subgroup restriction and
only gives abstract-isomorphism alternatives. Here the finite certificate
proves the stronger inclusion and conjugacy statements for the concrete
subgroups from `Subgroups`; neither gap is assumed away.
-/

namespace Matrix.PSL3Three

private theorem equiv_toMonoidHom : equiv.toMonoidHom = project := by
  ext g
  exact equiv_apply g

private theorem isCoatom_project (H : Subgroup SL) (hH : IsCoatom H) :
    IsCoatom (H.map project) := by
  rw [← equiv_toMonoidHom]
  exact (OrderIso.isCoatom_iff equiv.mapSubgroup H).2 hH

/-- The coordinate line stabilizer is a maximal proper subgroup of PSL₃(3). -/
public theorem isCoatom_lineStabilizer : IsCoatom lineStabilizer :=
  isCoatom_project lineStabilizerSL isCoatom_lineStabilizerSL

/-- The coordinate plane stabilizer is a maximal proper subgroup of PSL₃(3). -/
public theorem isCoatom_planeStabilizer : IsCoatom planeStabilizer :=
  isCoatom_project planeStabilizerSL isCoatom_planeStabilizerSL

/-- The specified monomial subgroup is a maximal proper subgroup of PSL₃(3). -/
public theorem isCoatom_monomial : IsCoatom monomial :=
  isCoatom_project monomialSL isCoatom_monomialSL

/-- The specified Singer normalizer is a maximal proper subgroup of PSL₃(3). -/
public theorem isCoatom_singerNormalizer : IsCoatom singerNormalizer :=
  isCoatom_project singerNormalizerSL isCoatom_singerNormalizerSL

private theorem project_conjugate (H : Subgroup SL) (g : SL) :
    (H.map (MulAut.conj g).toMonoidHom).map project =
      (H.map project).map (MulAut.conj (project g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem le_project_conjugate (H : Subgroup PSL) (K : Subgroup SL) (g : SL)
    (h : H.comap project ≤ K.map (MulAut.conj g).toMonoidHom) :
    H ≤ (K.map project).map (MulAut.conj (project g)).toMonoidHom := by
  simpa only [Subgroup.map_comap_eq_self_of_surjective project_surjective,
    project_conjugate] using Subgroup.map_mono (f := project) h

/-- Every proper subgroup of PSL₃(3) is contained in a conjugate of one of
the four concrete candidates. -/
public theorem proper_subgroup_le_conjugate_PSL (H : Subgroup PSL) (hH : H ≠ ⊤) :
    ∃ g : PSL,
      H ≤ lineStabilizer.map (MulAut.conj g).toMonoidHom ∨
      H ≤ planeStabilizer.map (MulAut.conj g).toMonoidHom ∨
      H ≤ monomial.map (MulAut.conj g).toMonoidHom ∨
      H ≤ singerNormalizer.map (MulAut.conj g).toMonoidHom := by
  have hproper : H.comap project ≠ ⊤ := by
    intro heq
    apply hH
    apply Subgroup.comap_injective project_surjective
    simpa using heq
  rcases proper_subgroup_le_named_conjugate (H.comap project) hproper with
    ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩
  · exact ⟨project g, Or.inl (le_project_conjugate H _ g hg)⟩
  · exact ⟨project g, Or.inr (Or.inl (le_project_conjugate H _ g hg))⟩
  · exact ⟨project g, Or.inr (Or.inr (Or.inl (le_project_conjugate H _ g hg)))⟩
  · exact ⟨project g, Or.inr (Or.inr (Or.inr (le_project_conjugate H _ g hg)))⟩

private theorem isCoatom_conjugate (H : Subgroup PSL) (g : PSL) (hH : IsCoatom H) :
    IsCoatom (H.map (MulAut.conj g).toMonoidHom) :=
  (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup H).2 hH

/-- Exact maximal-subgroup classification of PSL₃(3), expressed by conjugacy
to the four specified subgroups rather than abstract isomorphism. -/
public theorem isCoatom_iff_conjugate (M : Subgroup PSL) :
    IsCoatom M ↔ ∃ g : PSL,
      M = lineStabilizer.map (MulAut.conj g).toMonoidHom ∨
      M = planeStabilizer.map (MulAut.conj g).toMonoidHom ∨
      M = monomial.map (MulAut.conj g).toMonoidHom ∨
      M = singerNormalizer.map (MulAut.conj g).toMonoidHom := by
  constructor
  · intro hM
    obtain ⟨g, hg⟩ := proper_subgroup_le_conjugate_PSL M hM.ne_top
    have close (K : Subgroup PSL) (hK : IsCoatom K)
        (h : M ≤ K.map (MulAut.conj g).toMonoidHom) :
        M = K.map (MulAut.conj g).toMonoidHom :=
      ((hM.le_iff_eq (isCoatom_conjugate K g hK).ne_top).1 h).symm
    refine ⟨g, ?_⟩
    rcases hg with h | h | h | h
    · exact Or.inl (close _ isCoatom_lineStabilizer h)
    · exact Or.inr (Or.inl (close _ isCoatom_planeStabilizer h))
    · exact Or.inr (Or.inr (Or.inl (close _ isCoatom_monomial h)))
    · exact Or.inr (Or.inr (Or.inr (close _ isCoatom_singerNormalizer h)))
  · rintro ⟨g, rfl | rfl | rfl | rfl⟩
    · exact isCoatom_conjugate _ g isCoatom_lineStabilizer
    · exact isCoatom_conjugate _ g isCoatom_planeStabilizer
    · exact isCoatom_conjugate _ g isCoatom_monomial
    · exact isCoatom_conjugate _ g isCoatom_singerNormalizer

end Matrix.PSL3Three
