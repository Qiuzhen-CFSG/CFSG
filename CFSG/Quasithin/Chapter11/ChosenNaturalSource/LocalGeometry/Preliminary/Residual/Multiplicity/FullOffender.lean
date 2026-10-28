module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Multiplicity.Thompson
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Multiplicity.SuzukiEndpoint

/-!
# The full-module FF branch of cubic containment

For the literal normalizer action on V_M, a minimum cubic actor of ratio
at most one contains a nontrivial best offender. The completed Suzuki
endpoint exclusion makes that actor faithful on the original SL₃ component.
The component/normal-subgroup dichotomy therefore places the component in
the full offender subgroup: the centralizing alternative would kill this
best offender. B.5 now bounds the natural multiplicity by two, and the
checked A.3.19 argument gives cubic containment on the original D,S.

Thus an escaping cubic forces the full module to be non-FF, with literal
cubic ratio strictly greater than one and at most two. Applying B.2.7 to
this same full module shows that J(T) centralizes all of V_M, strengthening
the previous centralization of the seed V. The faithful image and its
original conjugation equations are preserved in the transfer.

Excluding this remaining non-FF configuration is still required for
unconditional 11.0.4 and stays with qt-d-1222-natural-preliminary-source.
The final earlier-source assembly remains with
qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith B.2.7, B.5.1/B.5.6, D.3.8 and K.3.6;
A.3.19, printed pp.54--55; 3.2.5, p.580; and 11.0.4, p.760,
combined manuscript of 1 March 2004.
-/

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups ENNReal IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The full-module FF condition forces the actual marked SL₃ component into
the offender subgroup; actor faithfulness excludes centralization. -/
theorem sl3_fullAction_component_le_offender_of_ff
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree)
    (hff : letI := fullModule_elementary D S
      IsFFModule (imageRepresentation (fullModuleConjugation D S))) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ) ≤
      offenderSubgroup (imageRepresentation ρ) := by
  let := fullModule_elementary D S
  let ρ := fullModuleConjugation D S
  let τ := imageRepresentation ρ
  let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
  let O := offenderSubgroup τ
  let : O.Normal := offenderSubgroup_normal τ
  rcases (sl3_fullAction_component_isComponent D S m).normal_dichotomy O with hK | hc
  · exact hK
  · obtain ⟨A,hA⟩ := fullAction_exists_starred_actor D S
    have hq : actionRatio τ A ≤ 1 := hA.1.2.2.2.le.trans
      ((isFFModule_iff_cubicRatio_le_one τ).mp hff)
    have hoff : IsOffender τ A := ⟨hA.1.2.1,(actionRatio_le_one_iff τ hA.1.2.1).mp hq⟩
    obtain ⟨B,hBA,hB⟩ := hoff.exists_bestOffender τ
    have hBO := hB.le_offenderSubgroup τ
    have hOC : O ≤ centralizer (K : Set (actionImage ρ)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
    have hbot : B = ⊥ := bot_unique ((le_inf hBA (hBO.trans hOC)).trans_eq
      (sl3_fullAction_starred_kernel_eq_bot D S m heven A hA))
    exact (hB.1.1 hbot).elim

/-- The full-module FF branch has at most two natural copies, retaining the
original component marking and its scalar center. -/
theorem fullModule_sl3_copies_le_two_of_fullAction_ff
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree)
    (hff : letI := fullModule_elementary D S
      IsFFModule (imageRepresentation (fullModuleConjugation D S)))
    {s : ℕ} (hs : 0 < s) (h : FullModuleNaturalCopies D S m s) : s ≤ 2 :=
  fullModule_sl3_copies_le_two_of_component_le_offender D S m heven
    (sl3_fullAction_component_le_offender_of_ff D S m heven hff) hs h

/-- Source 11.0.4 in the full-module FF branch, on the original D,S.
No Thompson-commutator or multiplicity premise remains in this branch. -/
theorem sl3_orderThree_mem_of_fullAction_ff
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree)
    (hff : letI := fullModule_elementary D S
      IsFFModule (imageRepresentation (fullModuleConjugation D S)))
    {x : G} (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3) : x ∈ L := by
  obtain ⟨s,hs,h⟩ := fullModule_sl3_natural_copies D S m
  have hb := fullModule_sl3_copies_le_two_of_fullAction_ff D S m heven hff hs h
  apply sl3_orderThree_mem_of_fullModule_finrank_lt D S m heven ?_ hxM hx
  rw [h.finrank]
  nlinarith [S.field.degree_pos]

/-- An escaping cubic forces the actual full normalizer module to be non-FF. -/
theorem sl3_fullAction_not_ff_of_cubic_outside
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) {x : G}
    (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3) (hxL : x ∉ L) :
    letI := fullModule_elementary D S
    ¬ IsFFModule (imageRepresentation (fullModuleConjugation D S)) := by
  intro hff
  exact hxL (sl3_orderThree_mem_of_fullAction_ff D S m heven hff hxM hx)

/-- The precise remaining numerical interval on the full faithful action,
not on the component restriction or the seed quotient. -/
theorem sl3_fullAction_ratio_interval_of_cubic_outside
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) {x : G}
    (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3) (hxL : x ∉ L) :
    letI := fullModule_elementary D S
    let τ := imageRepresentation (fullModuleConjugation D S)
    1 < cubicRatio τ ∧ cubicRatio τ ≤ 2 := by
  let := fullModule_elementary D S
  refine ⟨lt_of_not_ge ?_,fullAction_cubicRatio_le_two D S⟩
  intro hq
  exact sl3_fullAction_not_ff_of_cubic_outside D S m heven hxM hx hxL
    ((isFFModule_iff_cubicRatio_le_one _).mpr hq)

/-- B.2.7 transfers from the literal internal conjugation image to the
full-module action image and forces Thompson centralization when it is non-FF. -/
theorem fullModule_thompson_centralizes_of_fullAction_not_ff
    (hnf : letI := fullModule_elementary D S
      ¬ IsFFModule (imageRepresentation (fullModuleConjugation D S))) :
    Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (componentOrbit V (normalizer (L : Set G)) : Set G) := by
  let := fullModule_elementary D S
  by_contra hn
  apply hnf
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hnormal := le_normalizer_componentOrbit V M
  have hUT : U ≤ (T : Subgroup G) := by
    have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      S.source.simpleQTKE T S.source.maximal_faithful.1
    have ht := (D.fundamentalSetup S.source.toHypothesis1221).fullModule_le_sylow hu
    rwa [D.fundamentalSetup_fullModule] at ht
  let ρ := fullModuleConjugation D S
  let σ := ChapterD.UniqueFactor.imageRepresentation M U hnormal
  let f : ChapterD.internalActionImage M U hnormal →* actionImage ρ :=
    σ.asGroupHom.codRestrict _ (by
      rintro ⟨a,g,rfl⟩
      exact ⟨g,rfl⟩)
  have hf : Function.Injective f := by
    intro a b he
    apply ChapterD.UniqueFactor.imageRepresentation_injective M U hnormal
    exact congrArg (fun z => imageRepresentation ρ z) he
  have hff := Chapter3.internalActionImage_isFFModule_of_thompson_not_le T M U
    D.sylow_normalizes_component hUT hnormal hn
  exact hff.map_equivariant σ (imageRepresentation ρ) f hf
    (LinearEquiv.refl (ZMod 2) (Additive U)) (fun _ _ => rfl)

/-- An escaping cubic forces J(T) to centralize the entire original V_M.
This supplies the full-module Thompson premise for the remaining qrc analysis. -/
theorem sl3_thompson_centralizes_fullModule_of_cubic_outside
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) {x : G}
    (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3) (hxL : x ∉ L) :
    Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (componentOrbit V (normalizer (L : Set G)) : Set G) :=
  fullModule_thompson_centralizes_of_fullAction_not_ff D S
    (sl3_fullAction_not_ff_of_cubic_outside D S m heven hxM hx hxL)

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
