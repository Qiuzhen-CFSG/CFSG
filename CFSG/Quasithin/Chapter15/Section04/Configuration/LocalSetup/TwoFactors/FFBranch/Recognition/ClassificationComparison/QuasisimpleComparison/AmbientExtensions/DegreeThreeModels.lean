module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.Targets
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.AmbientExtensions.Rows
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.AmbientExtensions.DegreeThreeModels.Parameters
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.AmbientExtensions.DegreeThreeModels.UnitaryComparison

/-!
# The degree-three ambient rows in the FF comparison

The odd cube divisibility forces the unitary parameter three. The two
literal F.6.18 rows then give G₂(2)′ and G₂(2), respectively, through actual
special/projective and conjugation equivalences. The component maps below
compose the existing `componentEquiv` with these ambient equivalences, so
they commute with the original inclusions F*(N) ≤ N ≤ D. The transported
representation restricts to precisely rho on the marked offender subgroup.

These results are conditional on the small offender model supplied by the
caller; they neither prune the actor catalogue nor assume N = D. The
existing `offenderEquiv`, `offenderQuotientEquiv`, `marked_derived` and
`marked_centralizer` apply to the same constructed ambient equivalences.

Source: Aschbacher–Smith, F.6.18(10)–(11), pp.309–310; B.5.1/B.5.6,
pp.99–110; the comparison in 15.4.18, p.1163.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.QuasisimpleComparison.AmbientExtensions
open GoldschmidtAlternatives Atlas.G2.LieAutomorphismExtensions DegreeThreeModels
universe u v w
variable {D : Type u} [Group D] [Finite D]
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D} {K : GroupClass.{u}}

private noncomputable def componentModelEquiv {M : Type w} [Group M]
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (e : D ≃* M) (L : Subgroup M)
    (he : (componentImage ρ).map e.toMonoidHom = L) :
    generalizedFitting (offenderSubgroup ρ) ≃* L :=
  (componentEquiv h b).trans ((e.subgroupMap (generalizedFitting D)).trans
    (MulEquiv.subgroupCongr (by rwa [fitting_eq_componentImage h b])))

private theorem componentModelEquiv_coe {M : Type w} [Group M]
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (e : D ≃* M) (L : Subgroup M)
    (he : (componentImage ρ).map e.toMonoidHom = L)
    (x : generalizedFitting (offenderSubgroup ρ)) :
    (componentModelEquiv h b e L he x : M) = e ((x : offenderSubgroup ρ) : D) := rfl

/-- Row (10) gives the actual binary G₂ commutator model, carrying the
embedded actor component and the restriction of the original representation. -/
theorem case10_marked_equiv (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : Case10 G₁ G₂) :
    ∃ e : D ≃* BinaryDerived,
      (componentImage ρ).map e.toMonoidHom = ⊤ ∧
      ∃ c : generalizedFitting (offenderSubgroup ρ) ≃* BinaryDerived,
      (∀ x, c x = e ((x : offenderSubgroup ρ) : D)) ∧
      ((ρ.comp e.symm.toMonoidHom).comp
        ((offenderSubgroup ρ).map e.toMonoidHom).subtype).comp
          (offenderEquiv (ρ := ρ) e).toMonoidHom =
        ρ.comp (offenderSubgroup ρ).subtype := by
  obtain ⟨e⟩ := unitary_three_equiv (case10_unitary_three h s hr)
  let : IsQuasisimple BinaryDerived := binaryDerived_quasisimple
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
  have he : (componentImage ρ).map e.toMonoidHom = ⊤ := by
    rw [← fitting_eq_componentImage h b, generalizedFitting_eq_top_of_quasisimple,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  exact ⟨e, he, (componentModelEquiv h b e ⊤ he).trans topEquiv,
    componentModelEquiv_coe h b e ⊤ he, marked_restriction e⟩

/-- Row (11) gives the full binary G₂ model. Its literal derived subgroup
is the image of F*(N), and its marked action restricts to the original rho on N. -/
theorem case11_marked_equiv (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : Case11 G₁ G₂) :
    ∃ e : D ≃* Atlas.G2.Model (ZMod 2),
      (componentImage ρ).map e.toMonoidHom = BinaryDerived ∧
      ∃ c : generalizedFitting (offenderSubgroup ρ) ≃* BinaryDerived,
      (∀ x, (c x : Atlas.G2.Model (ZMod 2)) = e ((x : offenderSubgroup ρ) : D)) ∧
      ((ρ.comp e.symm.toMonoidHom).comp
        ((offenderSubgroup ρ).map e.toMonoidHom).subtype).comp
          (offenderEquiv (ρ := ρ) e).toMonoidHom =
        ρ.comp (offenderSubgroup ρ).subtype := by
  obtain ⟨e, he⟩ := unitary_graph_three_equiv (case11_unitary_three h s hr) h.twoCore
  have hm : (componentImage ρ).map e.toMonoidHom = BinaryDerived := by
    rwa [fitting_eq_componentImage h b] at he
  exact ⟨e, hm, componentModelEquiv h b e BinaryDerived hm,
    componentModelEquiv_coe h b e BinaryDerived hm, marked_restriction e⟩

/-- The first degree-three row is a genuine small ambient model. -/
theorem case10_model (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : Case10 G₁ G₂) :
    SmallAmbientModel D := by
  obtain ⟨e, _⟩ := case10_marked_equiv h b s hr
  exact Or.inl (.g2Derived e)

/-- The graph-extension row is a genuine small ambient model. -/
theorem case11_model (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : Case11 G₁ G₂) :
    SmallAmbientModel D := by
  obtain ⟨e, _⟩ := case11_marked_equiv h b s hr
  exact Or.inl (.g2 e)

/-- Both literal F.6.18 degree-three rows satisfy the requested ambient catalogue. -/
theorem degreeThree_model (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : DegreeThreeRows G₁ G₂) :
    SmallAmbientModel D := by
  rcases hr with hr | hr
  · exact case10_model h b s hr
  · exact case11_model h b s hr

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.QuasisimpleComparison.AmbientExtensions
