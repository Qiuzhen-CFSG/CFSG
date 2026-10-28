module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage.Annihilator
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Decomposability from the wedge annihilator

A projective vector in the `d`th exterior power is the Plücker point of a
`d`-dimensional subspace if and only if its wedge annihilator has dimension
at least `d`. The criterion holds over every field and in every degree,
including degree zero.

For the reverse implication, choose `d` independent annihilating vectors
and extend them to a basis. Multiplication by an additional basis vector
sends each exterior basis monomial not containing that vector to a distinct
monomial, up to a unit sign. Thus every nonzero coefficient contains all
`d` selected vectors, and the exterior vector belongs to their top exterior
line. Unit signs keep the argument valid in characteristic two.

This is the linear-algebraic decomposability step in the flag-variety
construction used in Borel, *Linear Algebraic Groups*, §11.1
(`refs/KGroup/Bor1/Chapter4.tex`). Closedness of the rank locus and the
reconstruction of full flags are separate geometric steps.
-/

public section

open scoped ExteriorAlgebra LinearAlgebra.Projectivization
open Module Set Set.powersetCard
namespace Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry

universe u v w
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
variable {I : Type w} [LinearOrder I] (b : Basis I k V)

private theorem basis_singleton (i : I) :
    b.ExteriorAlgebra {i} = ExteriorAlgebra.ι k (b i) := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_singleton i)]
  simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    powersetCard.ofFinEmbEquiv_symm_apply, ofCard]

private theorem mul_basis_of_mem (s : Finset I) (i : I) (hi : i ∈ s) :
    ExteriorAlgebra.ι k (b i) * b.ExteriorAlgebra s = 0 := by
  rw [← basis_singleton]
  exact ExteriorAlgebra.basis_mul_of_not_disjoint b
    (ofCard (Finset.card_singleton i)) (ofCard (s := s) rfl) (by simpa using hi)

private theorem mul_basis_of_notMem (s : Finset I) (i : I) (hi : i ∉ s) :
    ∃ ε : ℤˣ, ExteriorAlgebra.ι k (b i) * b.ExteriorAlgebra s =
      ε • b.ExteriorAlgebra (insert i s) := by
  have hd : Disjoint ({i} : Finset I) s := by simpa using hi
  refine ⟨(permOfDisjoint (s := ofCard (Finset.card_singleton i))
    (t := ofCard (s := s) rfl) hd).sign, ?_⟩
  rw [← basis_singleton]
  have hu : (disjUnion (s := ofCard (Finset.card_singleton i))
      (t := ofCard (s := s) rfl) hd).val = insert i s := by
    change ({i} : Finset I).disjUnion s hd = insert i s
    rw [Finset.disjUnion_eq_union, Finset.singleton_union]
  have hmul := ExteriorAlgebra.basis_mul_of_disjoint b
    (ofCard (Finset.card_singleton i)) (ofCard (s := s) rfl) hd
  change b.ExteriorAlgebra {i} * b.ExteriorAlgebra s =
    (permOfDisjoint (s := ofCard (Finset.card_singleton i))
      (t := ofCard (s := s) rfl) hd).sign •
        b.ExteriorAlgebra (disjUnion (s := ofCard (Finset.card_singleton i))
          (t := ofCard (s := s) rfl) hd).val at hmul
  rw [hu] at hmul
  exact hmul

private theorem coeff_mul_basis_ne_zero (s : Finset I) (i : I) (hi : i ∉ s) :
    b.ExteriorAlgebra.coord (insert i s)
      (ExteriorAlgebra.ι k (b i) * b.ExteriorAlgebra s) ≠ 0 := by
  obtain ⟨ε, hε⟩ := mul_basis_of_notMem b s i hi
  rw [hε, Units.smul_def, map_zsmul]
  simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]
  exact (smul_ne_zero_iff_ne ε).mpr one_ne_zero

private theorem coeff_mul_basis_eq_zero (s t : Finset I) (i : I)
    (hi : i ∉ s) (ht : t ≠ s) :
    b.ExteriorAlgebra.coord (insert i s)
      (ExteriorAlgebra.ι k (b i) * b.ExteriorAlgebra t) = 0 := by
  by_cases hit : i ∈ t
  · rw [mul_basis_of_mem b t i hit, map_zero]
  · obtain ⟨ε, hε⟩ := mul_basis_of_notMem b t i hit
    have hst : insert i s ≠ insert i t := by
      intro h
      apply ht
      have := congrArg (fun x : Finset I => x.erase i) h
      simpa [hi, hit] using this.symm
    rw [hε, Units.smul_def, map_zsmul]
    simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne hst, smul_zero]

-- An annihilating basis vector belongs to every monomial with nonzero coefficient.
private theorem coeff_eq_zero_of_wedge_eq_zero (a : ExteriorAlgebra k V)
    (s : Finset I) (i : I) (hi : i ∉ s)
    (ha : ExteriorAlgebra.ι k (b i) * a = 0) : b.ExteriorAlgebra.repr a s = 0 := by
  let c := b.ExteriorAlgebra.coord (insert i s)
    (ExteriorAlgebra.ι k (b i) * b.ExteriorAlgebra s)
  have hc : c ≠ 0 := coeff_mul_basis_ne_zero b s i hi
  have hmap : (b.ExteriorAlgebra.coord (insert i s)).comp
      (LinearMap.mulLeft k (ExteriorAlgebra.ι k (b i))) =
      c • b.ExteriorAlgebra.coord s := by
    apply b.ExteriorAlgebra.ext
    intro t
    by_cases hts : t = s
    · subst t
      simp [c, Basis.coord_apply]
    · simpa [Basis.coord_apply, hts, Ne.symm hts] using
        coeff_mul_basis_eq_zero b s t i hi hts
  have h := LinearMap.congr_fun hmap a
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, ha, map_zero,
    LinearMap.smul_apply, Basis.coord_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hc

private theorem grade_coord_eq (d : ℕ) (a : ⋀[k]^d V) (s : powersetCard I d) :
    b.ExteriorAlgebra.repr (a : ExteriorAlgebra k V) s.val =
      (b.exteriorPower d).repr a s := by
  have h : (b.ExteriorAlgebra.coord s.val).comp (⋀[k]^d V).subtype =
      (b.exteriorPower d).coord s := by
    apply (b.exteriorPower d).ext
    intro t
    simp only [LinearMap.comp_apply, Submodule.subtype_apply,
      ← ExteriorAlgebra.basis_eq_coe_basis, Basis.coord_apply, Basis.repr_self]
    by_cases hst : s = t
    · simp [hst]
    · simp [hst, show s.val ≠ t.val from fun h => hst (Subtype.ext h)]
  exact LinearMap.congr_fun h a

-- In degree d, containing d fixed indices leaves only one possible monomial.
private theorem eq_smul_basis_of_annihilates (d : ℕ) (a : ⋀[k]^d V)
    (s : powersetCard I d)
    (ha : ∀ i ∈ s, ExteriorAlgebra.ι k (b i) * (a : ExteriorAlgebra k V) = 0) :
    a = (b.exteriorPower d).repr a s • b.exteriorPower d s := by
  apply (b.exteriorPower d).ext_elem
  intro t
  by_cases hts : t = s
  · subst t
    simp
  · have hst := Ne.symm hts
    obtain ⟨i, his, hit⟩ := (exists_mem_notMem_iff_ne s t).mp hst
    have hc := coeff_eq_zero_of_wedge_eq_zero b (a : ExteriorAlgebra k V)
      t.val i hit (ha i his)
    rw [grade_coord_eq] at hc
    simp only [map_smul, Finsupp.smul_apply, Basis.repr_self,
      Finsupp.single_eq_of_ne hts, smul_zero, hc]


private theorem exists_subspace_basis_line [FiniteDimensional k V] (d : ℕ)
    (s : powersetCard I d) : ∃ W : Submodule k V, finrank k W = d ∧
      b.exteriorPower d s ∈ pluckerLine d W := by
  let f : Fin d ↪ I := (ofFinEmbEquiv.symm s).toEmbedding
  have hf : LinearIndependent k (b ∘ f) := b.linearIndependent.comp f f.injective
  let W := Submodule.span k (Set.range (b ∘ f))
  have hW : finrank k W = d := by
    rw [finrank_span_eq_card hf, Fintype.card_fin]
  refine ⟨W, hW, ?_⟩
  refine ⟨exteriorPower.ιMulti k d (Basis.span hf), ?_⟩
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  ext i
  exact congrArg Subtype.val (Basis.span_apply hf i)

private theorem exists_basis_containing (d : ℕ) (v : Fin d → V)
    (hv : LinearIndependent k v) :
    ∃ (J : Type v) (b : Basis J k V) (j : Fin d ↪ J), ∀ i, b (j i) = v i := by
  let S := hv.linearIndepOn_id.extend (Set.subset_univ (Set.range v))
  let b : Basis S k V := Basis.extend hv.linearIndepOn_id
  let j : Fin d ↪ S :=
    ⟨fun i => ⟨v i, Basis.subset_extend hv.linearIndepOn_id ⟨i, rfl⟩⟩,
      fun i j h => hv.injective (congrArg Subtype.val h)⟩
  exact ⟨S, b, j, fun i => Basis.extend_apply_self hv.linearIndepOn_id (j i)⟩

/-- An exterior line is a Plücker line exactly when its wedge annihilator has
at least the exterior degree as its dimension. This holds for every degree
and over every field; no algebraic-closedness hypothesis is needed. -/
theorem exists_subspacePlucker_iff_le_finrank_pluckerAnnihilator
    [FiniteDimensional k V] (d : ℕ) (p : ℙ k (⋀[k]^d V)) :
    (∃ W : Submodule k V, ∃ hW : finrank k W = d, subspacePlucker d W hW = p) ↔
      d ≤ finrank k (pluckerAnnihilator p) := by
  classical
  constructor
  · rintro ⟨W, hW, rfl⟩
    rw [pluckerAnnihilator_subspacePlucker, hW]
  · intro h
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank h
    let f : Fin d → V := (pluckerAnnihilator p).subtype ∘ v
    have hf : LinearIndependent k f := hv.map'
      (pluckerAnnihilator p).subtype (LinearMap.ker_eq_bot.mpr
        (Submodule.subtype_injective _))
    obtain ⟨J, b, j, hj⟩ := exists_basis_containing d f hf
    let : LinearOrder J := linearOrderOfSTO WellOrderingRel
    let s : powersetCard J d := ofFinEmb d J j
    have hann : ∀ i ∈ s,
        ExteriorAlgebra.ι k (b i) * (p.rep : ExteriorAlgebra k V) = 0 := by
      intro i hi
      obtain ⟨m, rfl⟩ := (mem_ofFinEmb_iff_mem_range d J j i).mp hi
      rw [hj]
      exact (v m).property p.rep (by
        rw [p.submodule_eq]
        exact Submodule.mem_span_singleton_self _)
    obtain ⟨W, hW, hb⟩ := exists_subspace_basis_line b d s
    have ha : p.rep ∈ pluckerLine d W := by
      rw [eq_smul_basis_of_annihilates b d p.rep s hann]
      exact Submodule.smul_mem _ _ hb
    refine ⟨W, hW, Projectivization.submodule_injective ?_⟩
    rw [subspacePlucker_submodule]
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [p.submodule_eq]
      exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ha)
    · rw [p.finrank_submodule, finrank_pluckerLine d W hW]

end Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry
