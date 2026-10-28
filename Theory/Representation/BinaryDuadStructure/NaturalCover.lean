module

public import Theory.Representation.BinaryDuadStructure.LineQuotient
public import Theory.Representation.FirstCohomologyDuality

/-!
# A concrete five-dimensional cover of the polar natural module

Sending each duad basis vector to its polar vector kills every line relation.
The resulting surjection has one-dimensional, hence fixed, binary kernel.
Transitivity and the vanishing constant vector prove commutator generation.
Transport through the actual quotient equivalence gives a covering map on U₀/D.
No radical identity is inferred from its dimension.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.5.3,
printed pp.343–345 (PDF pp.354–356).
-/

@[expose] public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation BinaryDuadModule
namespace BinaryDuadStructure

/-- Send a point basis vector to the corresponding nonzero natural vector. -/
def pointSum : Full Duad →ₗ[ZMod 2] NaturalModule where
  toFun u := ∑ d : Duad, u d • (polarVector d).val
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a u := by simp [mul_smul, Finset.smul_sum]

@[simp] theorem pointSum_single (d : Duad) :
    pointSum (Pi.single d 1) = (polarVector d).val := by
  simp [pointSum]

theorem pointSum_equivariant (g : A6) (u : Full Duad) :
    pointSum (alternatingPointAction g u) = alternatingNaturalAction g (pointSum u) := by
  change (∑ d : Duad, u (g⁻¹ • d) • (polarVector d).val) =
    alternatingNaturalAction g (∑ d : Duad, u d • (polarVector d).val)
  rw [map_sum]
  simp only [map_smul]
  have hv (d : Duad) : alternatingNaturalAction g (polarVector d).val =
      (polarVector (g • d)).val := polarAction_vector g.val d
  simp_rw [hv]
  exact (Equiv.sum_comp (MulAction.toPerm g)
    (fun d => u (g⁻¹ • d) • (polarVector d).val)).symm.trans (by
      simp only [MulAction.toPerm_apply, inv_smul_smul])

theorem pointSum_line (s : Syntheme) : pointSum (line s) = 0 := by
  fin_cases s <;> decide

theorem lineSpan_le_pointSum_ker : lineSpan ≤ pointSum.ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, rfl⟩
  exact pointSum_line s

def naturalProjection : LineQuotient →ₗ[ZMod 2] NaturalModule :=
  lineSpan.liftQ pointSum lineSpan_le_pointSum_ker

theorem naturalProjection_equivariant (g : A6) (q : LineQuotient) :
    naturalProjection (lineQuotientAction g q) = alternatingNaturalAction g (naturalProjection q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ u => exact pointSum_equivariant g u

theorem naturalProjection_surjective : Function.Surjective naturalProjection := by
  intro v
  by_cases hv : v = 0
  · exact ⟨0, by simp [hv]⟩
  obtain ⟨d, hd⟩ := polarVector_bijective.2 ⟨v, hv⟩
  refine ⟨lineSpan.mkQ (Pi.single d 1), ?_⟩
  exact (pointSum_single d).trans (congrArg Subtype.val hd)

noncomputable def naturalProjectionHom :
    lineQuotientAction.IntertwiningMap alternatingNaturalAction :=
  naturalProjection.intertwiningMap_of_isIntertwiningMap _ _ naturalProjection_equivariant

theorem naturalProjection_ker_finrank :
    Module.finrank (ZMod 2) naturalProjection.ker = 1 := by
  have h := naturalProjection.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr naturalProjection_surjective, finrank_top,
    naturalModule_finrank, lineQuotient_finrank] at h
  omega

theorem naturalProjection_ker_fixed {q : LineQuotient} (hq : naturalProjection q = 0)
    (g : A6) : lineQuotientAction g q = q := by
  by_cases hz : q = 0
  · simp [hz]
  let K := naturalProjectionHom.ker
  have hdim : Module.finrank (ZMod 2) K.toSubmodule = 1 := naturalProjection_ker_finrank
  have hne : (⟨q, hq⟩ : K.toSubmodule) ≠ 0 := fun h => hz (congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hdim hne
    (K.toRepresentation g ⟨q, hq⟩)
  have han : a ≠ 0 := by
    intro he
    rw [he, zero_smul] at ha
    have hh := congrArg (K.toRepresentation g⁻¹) ha
    simp only [map_zero, Representation.inv_self_apply] at hh
    exact hne hh.symm
  have ha1 : a = 1 := (show ∀ a : ZMod 2, a ≠ 0 → a = 1 by decide) a han
  rw [ha1, one_smul] at ha
  exact (congrArg Subtype.val ha).symm


def pointClass (d : Duad) : LineQuotient := lineSpan.mkQ (Pi.single d 1)

theorem pointClass_equivariant (g : A6) (d : Duad) :
    pointClass (g • d) = lineQuotientAction g (pointClass d) := by
  change lineSpan.mkQ (Pi.single (g • d) 1) =
    lineSpan.mkQ (alternatingPointAction g (Pi.single d 1))
  congr 1
  ext e
  change (Pi.single (g • d) (1 : ZMod 2) : Full Duad) e =
    (Pi.single d (1 : ZMod 2) : Full Duad) (g⁻¹ • e)
  simp only [Pi.single_apply, inv_smul_eq_iff]

theorem sum_pointClass : ∑ d : Duad, pointClass d = 0 := by
  change (∑ d : Duad, lineSpan.mkQ (Pi.single d 1)) = 0
  rw [← map_sum]
  have h : (∑ d : Duad, (Pi.single d (1 : ZMod 2) : Full Duad)) = allOne Duad := by
    ext e
    simp [allOne]
  rw [h]
  exact (Submodule.Quotient.mk_eq_zero lineSpan).mpr allOne_mem_lineSpan

theorem lineQuotient_generated : Representation.Coinvariants.ker lineQuotientAction = ⊤ := by
  let C := Representation.Coinvariants.ker lineQuotientAction
  have hp (d : Duad) : pointClass d ∈ C := by
    have hs : (∑ e : Duad, (pointClass d - pointClass e)) ∈ C := by
      apply Submodule.sum_mem
      intro e _
      obtain ⟨g, hg⟩ := a6_duad_transitive e d
      rw [← hg, pointClass_equivariant]
      exact Representation.Coinvariants.sub_mem_ker g (pointClass e)
    have he : (∑ e : Duad, (pointClass d - pointClass e)) = pointClass d := by
      rw [Finset.sum_sub_distrib, sum_pointClass, sub_zero, Finset.sum_const,
        Finset.card_univ]
      change 15 • pointClass d = pointClass d
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
      rw [show ((15 : ℕ) : ZMod 2) = 1 by decide, one_smul]
    exact he ▸ hs
  apply top_unique
  intro q _
  induction q using Submodule.Quotient.induction_on with
  | _ u =>
    have hu : u = ∑ d : Duad, u d • (Pi.single d (1 : ZMod 2) : Full Duad) := by
      ext e
      simp [Pi.single_apply, mul_ite]
    change lineSpan.mkQ u ∈ C
    rw [hu, map_sum]
    apply Submodule.sum_mem
    intro d _
    rw [map_smul]
    exact C.smul_mem _ (hp d)

theorem naturalProjection_isCover :
    Representation.OneCohomology.IsCover naturalProjectionHom :=
  ⟨naturalProjection_surjective, fun _ hq g => naturalProjection_ker_fixed hq g,
    lineQuotient_generated⟩
/-- The line-relation identification as an equivalence of the actual actions. -/
noncomputable def coreLineRepresentationEquiv : coreQuotientAction.Equiv lineQuotientAction :=
  Representation.Equiv.mk coreLineEquiv (fun g => LinearMap.ext (coreLineEquiv_equivariant g))

/-- The cover map on the literal even-core quotient in G.5.3(3). -/
noncomputable def coreNaturalProjection : coreQuotientAction.IntertwiningMap alternatingNaturalAction :=
  naturalProjectionHom.comp coreLineRepresentationEquiv.toIntertwiningMap

@[simp] theorem coreNaturalProjection_mk (u : core Duad) :
    coreNaturalProjection (CoreRelations.mkQ u) = pointSum u.val := rfl

theorem coreQuotient_generated : Representation.Coinvariants.ker coreQuotientAction = ⊤ := by
  let C := Representation.Coinvariants.ker coreQuotientAction
  have h : Representation.Coinvariants.ker lineQuotientAction ≤ C.map coreLineEquiv.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, q⟩, rfl⟩
    obtain ⟨u, rfl⟩ := coreLineEquiv.surjective q
    refine ⟨coreQuotientAction g u - u, Representation.Coinvariants.sub_mem_ker g u, ?_⟩
    exact (map_sub coreLineEquiv _ _).trans (by rw [coreLineEquiv_equivariant])
  rw [lineQuotient_generated] at h
  apply top_unique
  intro u _
  obtain ⟨v, hv, he⟩ := h (show coreLineEquiv u ∈ ⊤ from Submodule.mem_top)
  exact (coreLineEquiv.injective he) ▸ hv

theorem coreNaturalProjection_isCover :
    Representation.OneCohomology.IsCover coreNaturalProjection := by
  refine ⟨naturalProjection_surjective.comp coreLineEquiv.surjective, ?_, coreQuotient_generated⟩
  intro q hq g
  apply coreLineEquiv.injective
  rw [coreLineEquiv_equivariant]
  exact naturalProjection_ker_fixed hq g

end BinaryDuadStructure
