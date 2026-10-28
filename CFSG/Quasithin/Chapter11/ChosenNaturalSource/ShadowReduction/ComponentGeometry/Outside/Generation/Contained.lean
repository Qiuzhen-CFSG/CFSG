module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.Section
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.OddIndex.Sylow
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.SylowNormalizerFrattini

/-!
# The contained component and the first radical

For a nonsolvable outside H inside KT, intersect the solvable radical of KT
with H. The proved 11.4.1 radical theorem makes the original R₁ a Sylow
subgroup of this intersection. Its solvable Sylow supplement is proper in H,
so H-star minimality puts it in M. If the normalizer of R₁ in H were proper,
minimality and the Frattini argument would put H in M too. Hence H normalizes
R₁, and R₁ lies in the actual O₂(H).

The completed quotient-centralizing Hall branch puts every hypothetical H
with n(H)>1 inside KT. Consequently the N_G(R₁)≤M branch of earlier 11.1.5
now proves n(H)=1 for every original H, including the strict component rows.
Selection supplies an actual H with this bound and its O² residual alternative.
The full 11.1.5 alternative reduces the remaining case to field four and the
SL₃(4) or Sp₄(4) blocks, retaining the literal core and omega-center clauses.
Their exclusion, and hence universal 11.4.4, remains with this owner.

Earlier 11.1.5, geometry, fixed spaces, 11.3.2 and component equality retain
qt-d-1222-natural-local-geometry, qt-d-1222-shadow-linear-geometry,
qt-d-1222-shadow-component-triangle and qt-d-1222-shadow-component-comparison.
The exact OddKernelNormalizer premise remains with
qt-d-1222-natural-odd-kernel-normalizer. Their final source discharge belongs
to qt-d-1222-shadow-components; no new component-uniqueness assumption is used.

Source: Aschbacher--Smith, 11.1.5, 11.4.1(3) and 11.4.4,
printed pp.765--766,775--776 and778 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

private theorem normalizes_solvable_sylow
    {M H R P : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : ¬ Group.IsSolvable H) (hRH : R ≤ H)
    (hHR : H ≤ normalizer (R : Set G)) (hR : Group.IsSolvable R)
    (hP : Chapter1.IsSylowIn 2 P R) (hTP : (T : Subgroup G) ≤ normalizer (P : Set G)) :
    H ≤ normalizer (P : Set G) := by
  let : Group.IsSolvable R := hR
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) := hH.1.1.2.trans hHR
  let : Group.IsSolvable (R ⊔ (T : Subgroup G) : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes R (T : Subgroup G) hTR
  have hproper : R ⊔ (T : Subgroup G) < H := by
    apply lt_of_le_of_ne (sup_le hRH hH.1.1.2)
    intro he
    exact hs (he ▸ inferInstance)
  have hRM : R ≤ M := le_sup_left.trans
    (Chapter3.HStar.proper_overgroup_le T hH le_sup_right hproper)
  let R' := R.subgroupOf H
  let P' := P.subgroupOf H
  have hPH := (Chapter1.isSylowIn_iff.mp hP).2.1.trans hRH
  let : R'.Normal := normal_subgroupOf_of_le_normalizer hHR
  have hP' : Chapter1.IsSylowIn 2 P' R' :=
    (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mp (by
      simpa only [P', R', map_subgroupOf_eq_of_le hPH,
        map_subgroupOf_eq_of_le hRH] using hP)
  obtain ⟨U,hU⟩ := hP'
  have hfr : normalizer (P' : Set H) ⊔ R' = ⊤ := by
    rw [← hU]
    exact U.normalizer_sup_eq_top
  have hnmap : (normalizer (P' : Set H)).map H.subtype =
      H ⊓ normalizer (P : Set G) := by
    rw [← subgroupOf_normalizer_eq hPH, subgroupOf_map_subtype, inf_comm]
  have hfrG : (H ⊓ normalizer (P : Set G)) ⊔ R = H := by
    have hh := congrArg (map H.subtype) hfr
    simpa only [Subgroup.map_sup, hnmap, R', map_subgroupOf_eq_of_le hRH,
      ← MonoidHom.range_eq_map, range_subtype] using hh
  by_contra hn
  have hlt : H ⊓ normalizer (P : Set G) < H :=
    lt_of_le_of_ne inf_le_left (fun he => hn (he ▸ inf_le_right))
  have hNM := Chapter3.HStar.proper_overgroup_le T hH
    (le_inf hH.1.1.2 hTP) hlt
  exact hH.1.2 (hfrG ▸ sup_le hNM hRM)

variable {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- The original R₁ is normalized by every nonsolvable outside H contained
in KT. The Sylow and solvable-radical inputs are proved from the source list. -/
theorem ofFlag_contained_nonsolvable_normalizes_radical
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHK : H ≤ (ofFlag S f X z H).K ⊔ (T : Subgroup G))
    (hs : ¬ Group.IsSolvable H) :
    H ≤ normalizer (f.Ri 0 : Set G) := by
  let E := ofFlag S f X z H
  let C := E.K ⊔ (T : Subgroup G)
  let R := (solvableRadical C).map C.subtype
  have hKc : Source.NormalComponentIn (centralizer (f.Vi 0 : Set G)) E.K :=
    ⟨⟨h.line_component_centralizes,h.line_component.2.subgroupOf_of_le
      h.line_component_centralizes (Subgroup.centralizer_le_normalizer _)⟩,
      normal_subgroupOf_of_le_normalizer
        ((Subgroup.centralizer_le_normalizer _).trans E.G₁_normalizes_K)⟩
  have hSyl := Radical.ofFlag_surviving_sylow_radical S f X z H E.K hKc
    (le_conjugateSpanBy _ _) ((f.invariant 0).trans E.G₁_normalizes_K) hcase
  have hPR : f.Ri 0 ≤ R := (Chapter1.isSylowIn_iff.mp hSyl).2.1
  have hPH : f.Ri 0 ≤ H := (LocalGeometry.localRadical_le_sylow _).trans hH.1.1.2
  have hCR : C ≤ normalizer (R : Set G) :=
    C.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image C (solvableRadical C))
  have hHR : H ≤ normalizer ((H ⊓ R : Subgroup G) : Set G) :=
    (le_inf H.le_normalizer (hHK.trans hCR)).trans inf_normalizer_le_normalizer_inf
  let : Group.IsSolvable R := Group.isSolvable_of_surjective
    (C.subtype.subgroupMap_surjective (solvableRadical C))
  have hsol : Group.IsSolvable (H ⊓ R : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective inf_le_right)
  exact normalizes_solvable_sylow hH hs inf_le_left hHR hsol
    (hSyl.restrict (le_inf hPH hPR) inf_le_right)
    (le_sup_right.trans ((f.Li 0 ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))

/-- Large generation forces the literal R₁ inside O₂(H), without assuming
normality of the escaping E.2.2 component or a quotient model for H. -/
theorem ofFlag_large_generation_radical_le_core
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hn : 1 < ChapterE.generationParameter H) :
    f.Ri 0 ≤ H.pCoreIn 2 := by
  obtain ⟨I,_,_,_,_,hjoin,_,hIK⟩ :=
    ofFlag_large_generation_component_le S f X z H h he hlinear h1132 hcontrol hH hHz hn
  have hHK : H ≤ (ofFlag S f X z H).K ⊔ (T : Subgroup G) := by
    rw [← hjoin]
    exact sup_le_sup_right hIK _
  have hs : ¬ Group.IsSolvable H := by
    intro hh
    let := hh
    exact (not_lt_of_ge (ChapterE.generationParameter_le_one_of_solvable (G := H))) hn
  exact le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le (LocalGeometry.localRadical_le_sylow _))
    ((LocalGeometry.localRadical_le_sylow _).trans hH.1.1.2)
    (ofFlag_contained_nonsolvable_normalizes_radical S f X z H h hcase hH hHK hs)

/-- Source 11.4.4 in the first branch of earlier 11.1.5, for every original H.
Both the contained-component and quotient-centralizing branches are discharged. -/
theorem ofFlag_generation_eq_one_of_radical_normalizer
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hN : normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) :
    ChapterE.generationParameter H = 1 := by
  apply Nat.le_antisymm ?_ (selected_generation_spec (ofFlag S f X z H) h hH hHz).1
  change ChapterE.generationParameter H ≤ 1
  by_contra! hn
  obtain ⟨I,_,_,_,_,hjoin,_,hIK⟩ :=
    ofFlag_large_generation_component_le S f X z H h he hlinear h1132 hcontrol hH hHz hn
  have hs : ¬ Group.IsSolvable H := by
    intro hh
    let := hh
    exact (not_lt_of_ge (ChapterE.generationParameter_le_one_of_solvable (G := H))) hn
  exact hH.1.2 ((ofFlag_contained_nonsolvable_normalizes_radical S f X z H h hcase hH
    (by rw [← hjoin]; exact sup_le_sup_right hIK _) hs).trans hN)

/-- The equality-row Hall theorem and surviving list leave only field four. -/
theorem ofFlag_large_generation_field_four
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hn : 1 < ChapterE.generationParameter H) : S.field.degree = 2 := by
  cases hcase with
  | equal heq =>
    have hh := ofFlag_equal_generation_eq_one S f X z H h he heq.symm
      hlinear h1132 hcontrol hH hHz
    omega
  | sl2Prime _ hfour _ _ _ => exact hfour
  | psl2Prime _ hfour _ _ _ _ _ => exact hfour

/-- Apply the actual earlier 11.1.5 alternative to the original outside H.
The remaining block alternative keeps all its geometric clauses and O₂(H). -/
theorem ofFlag_generation_one_or_exceptional_block
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (h1115 : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    ChapterE.generationParameter H = 1 ∨
      (S.field.degree = 2 ∧ f.Ri 0 ≤ H.pCoreIn 2 ∧
        V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
        (ChapterC.IsSL3EvenBlock L 2 ∨ ChapterC.IsSp4FourBlock L) ∧
        (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
        f.Vi 0 = omegaOneAmbient ((center (f.Ri 0)).map (f.Ri 0).subtype)) := by
  by_cases hn : ChapterE.generationParameter H = 1
  · exact Or.inl hn
  have hpos := (selected_generation_spec (ofFlag S f X z H) h hH hHz).1
  change 0 < ChapterE.generationParameter H at hpos
  have hl : 1 < ChapterE.generationParameter H := by omega
  have hfour := ofFlag_large_generation_field_four S f X z H h hcase he
    hlinear h1132 hcontrol hH hHz hl
  have hcore := ofFlag_large_generation_radical_le_core S f X z H h hcase he
    hlinear h1132 hcontrol hH hHz hl
  rcases h1115 with hN | ⟨hV,hblock,hC,hcenter⟩
  · exact (hn (ofFlag_generation_eq_one_of_radical_normalizer S f X z H h hcase he
      hlinear h1132 hcontrol hH hHz hN)).elim
  · exact Or.inr ⟨hfour,hcore,hV,hfour ▸ hblock,hC,hcenter⟩

/-- The chosen-flag consumer: construct a source-selected H and prove its
generation bound under the first normalizer alternative of 11.1.5. -/
theorem ofFlag_selected_generation_one_of_radical_normalizer
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hN : normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z J) ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      ChapterE.generationParameter J = 1 := by
  obtain ⟨J,hJ,hJz,hsel⟩ := Models.ofFlag_surviving_selected_H S f X z H h hcase he hNT h1132
  refine ⟨J,hJ,hJz,hsel,?_⟩
  exact ofFlag_generation_eq_one_of_radical_normalizer S f X z J
    ⟨h.point_mem,h.point_fixed,h.point_ne_one,h.seed_centralizes,
      h.line_component,h.point_component,h.normalizer_split⟩
    hcase he hlinear h1132 hcontrol hJ hJz hN

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
