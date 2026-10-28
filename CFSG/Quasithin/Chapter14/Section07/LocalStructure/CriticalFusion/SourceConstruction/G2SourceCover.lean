module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.Section
public import Theory.Representation.G2NaturalExtensions

/-!
# The central-cover step in the G₂ source recognition

A central natural cover for the actual derived binary G₂ group is a quotient
of the trace-zero octonion module. Its dimension is six or seven; surjectivity
then identifies it equivariantly with the natural or Weyl module, preserving
the specified natural projection. The original-section application derives
full movement from the natural L₃(2) action and uses the literal K/O₂(K) map.

This proves the cover step in 14.7.54, not the full source recognition. Descent
of the original action and the existence of its central natural projection
still require the chief-factor argument using B.4.2, B.4.5 and F.9.18. Neither
the module identification nor the later Data record is an input here.

Source: Aschbacher–Smith, 14.7.54, printed pp.1065–1066, using B.4.6(1),
printed p.88. The imported octonion cover retains LICENSES/ATLAS.txt.
-/

public noncomputable section

open Subgroup Representation Representation.OneCohomology
open Atlas.G2 Atlas.G2.Natural
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (commutator (Model (ZMod 2))) W}

private theorem natural_or_weyl_of_cover
    (p : σ.IntertwiningMap (OrthogonalCover.binaryNatural (ZMod 2)))
    (hp : Function.Surjective p)
    (hfixed : p.toLinearMap.ker ≤ fixed σ)
    (hgen : Coinvariants.ker σ = ⊤) :
    (∃ e : Space (ZMod 2) ≃ₗ[ZMod 2] W,
      (∀ g v, e (derivedAction (ZMod 2) g v) = σ g (e v)) ∧
      ∀ v, p (e v) = v) ∨
    (∃ e : TraceZero (ZMod 2) ≃ₗ[ZMod 2] W,
      (∀ g v, e (traceZeroAction (ZMod 2) g.val v) = σ g (e v)) ∧
      ∀ v, p (e v) = mk (ZMod 2) v) := by
  obtain ⟨f,hf,hover⟩ := OrthogonalCover.exists_quotient (ZMod 2) p ⟨hp,hfixed,hgen⟩
  have hlo : 6 ≤ Module.finrank (ZMod 2) W := by
    simpa only [finrank_space] using LinearMap.finrank_le_finrank_of_surjective hp
  have hhi : Module.finrank (ZMod 2) W ≤ 7 := by
    simpa only [OrthogonalCover.finrank_traceZero] using
      LinearMap.finrank_le_finrank_of_surjective hf
  by_cases hdim : Module.finrank (ZMod 2) W = 6
  · left
    have hi : Function.Injective p :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (hdim.trans (finrank_space (ZMod 2)).symm)).mpr hp
    let e := (LinearEquiv.ofBijective p.toLinearMap ⟨hi,hp⟩).symm
    have he (v : Space (ZMod 2)) : p (e v) = v :=
      (LinearEquiv.ofBijective p.toLinearMap ⟨hi,hp⟩).apply_symm_apply v
    refine ⟨e,?_,he⟩
    intro g v
    apply hi
    rw [he,p.isIntertwining,he]
    rfl
  · right
    have hdim : Module.finrank (ZMod 2) W = 7 := by omega
    have hi : Function.Injective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        ((OrthogonalCover.finrank_traceZero (ZMod 2)).trans hdim.symm)).mpr hf
    refine ⟨LinearEquiv.ofBijective f.toLinearMap ⟨hi,hf⟩,?_,hover⟩
    intro g v
    exact LinearMap.congr_fun (f.isIntertwining' g) v

open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [FiniteDimensional (ZMod 2) W] in
/-- The cover deduction applied to the original section. The natural central
projection and descent of the residual action are earlier inputs; full
commutator generation is derived from the original L₃(2) action. -/
theorem natural_or_weyl_of_source_projection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Model (ZMod 2)))
    (hact : ∀ (k : K F) w,
      ρ ⟨k,map_subtype_le _ k.property⟩ w =
        σ (eK (QuotientGroup.mk' (pCore 2 (K F)) k)) w)
    (p : σ.IntertwiningMap (OrthogonalCover.binaryNatural (ZMod 2)))
    (hp : Function.Surjective p)
    (hfixed : p.toLinearMap.ker ≤ fixed σ) :
    (∃ e : Space (ZMod 2) ≃ₗ[ZMod 2] W,
      (∀ (k : K F) v,
        e (derivedAction (ZMod 2) (eK (QuotientGroup.mk' (pCore 2 (K F)) k)) v) =
          ρ ⟨k,map_subtype_le _ k.property⟩ (e v)) ∧
      ∀ v, p (e v) = v) ∨
    (∃ e : TraceZero (ZMod 2) ≃ₗ[ZMod 2] W,
      (∀ (k : K F) v,
        e (traceZeroAction (ZMod 2)
          (eK (QuotientGroup.mk' (pCore 2 (K F)) k)).val v) =
          ρ ⟨k,map_subtype_le _ k.property⟩ (e v)) ∧
      ∀ v, p (e v) = mk (ZMod 2) v) := by
  let : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let r : K F →* commutator (Model (ZMod 2)) :=
    eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (K F)))
  have hgen : Coinvariants.ker σ = ⊤ :=
    c.coinvariants_eq_top_of_group_generation (K F) (map_subtype_le _) σ r hact (by
      rw [commutator_comm,commutator_U h F,sup_eq_left.mpr c.kernel_le])
  rcases natural_or_weyl_of_cover p hp hfixed hgen with ⟨e,he,hover⟩ | ⟨e,he,hover⟩
  · exact Or.inl ⟨e,fun k v => (he _ v).trans (hact k (e v)).symm,hover⟩
  · exact Or.inr ⟨e,fun k v => (he _ v).trans (hact k (e v)).symm,hover⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
