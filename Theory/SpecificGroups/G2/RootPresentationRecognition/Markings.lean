module
public import Theory.SpecificGroups.G2.RootPresentationRecognition.Recognition
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.BorelOvergroups
public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.Irreducibility

/-!
# Full Borel and both parabolic markings on the literal G₂ source quotient

The presentation equivalence identifies the positive subgroup by its six root
maps. Sylow normalizers then identify the entire Borel. Each marked source
parabolic is proper and contains the Borel; the specified Weyl element selects
the short or long concrete parabolic. The short endpoint is the null-plane
stabilizer and the long endpoint is the singular-point stabilizer.

All three restricted maps come from the same ambient equivalence and compose
with the existing quotient marking. An explicit short-endpoint index retains
both orientations. No Cartan equality, target simplicity, or quotient order is
assumed. Source field construction, equations and placements remain inputs.
Source: DGS, Groups and Graphs, Theorem D, p.224; Aschbacher–Smith F.1.11–12.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace Atlas.G2.RootPresentationRecognition
open LieParabolicSetup Atlas.SplitOctonion Explicit
variable {F Y X : Type*} [Field F] [Group Y] [Group X]

/-- Any equivalence preserving the six roots preserves their full generated group. -/
theorem map_positive (d : BorelWeylData F Y) (e : Y ≃* Model F)
    (he : ∀ i a, e (d.x i a) = (modelData (F := F)).x i a) :
    d.toPositiveRoots.generated.map e.toMonoidHom = unipotent := by
  rw [← model_positive, PositiveRoots.generated,MonoidHom.map_closure]
  change Subgroup.closure _ = Subgroup.closure (Set.range (fun p : Fin 6 × F => (modelData (F := F)).x p.1 p.2))
  congr 1
  ext g
  constructor
  · rintro ⟨_,⟨⟨i,a⟩,rfl⟩,rfl⟩
    exact ⟨(i,a),(he i a).symm⟩
  · rintro ⟨⟨i,a⟩,rfl⟩
    exact ⟨d.x i a,⟨(i,a),rfl⟩,he i a⟩

/-- The short reflection does not fix the first singular point. -/
theorem weylS_not_long : (weylS : Model F) ∉ parabolic₂ := by
  intro h
  obtain ⟨a,ha⟩ := (mem_pointStabilizer_iff _).mp (parabolic_le_pointStabilizer h)
  have hz := congrArg (fun x : Carrier F => x 1) ha
  simp [weylS,weylSEquiv,weylSLinear,weylSApply,basisVector] at hz

/-- The long reflection does not preserve the standard null plane. -/
theorem weylR_not_short : (weylR : Model F) ∉ parabolic₁ := by
  intro h
  have hz := (parabolic₁_le_shortPlaneStabilizer h).1 (basisVector 1)
    (basis_mem_shortPlane 1 (by decide)) 2 (by decide)
  simp [weylR,weylREquiv,weylRLinear,weylRApply,basisVector] at hz

variable [CharP F 2]

/-- Proper Borel overgroups containing S are exactly the short parabolic. -/
theorem short_overgroup (H : Subgroup (Model F)) (hB : borel ≤ H)
    (hH : H < ⊤) (hS : weylS ∈ H) : H = parabolic₁ := by
  apply le_antisymm
  · rcases EvenLocal.BorelOvergroups.le_parabolic H hB hH with h | h
    · exact h
    · exact (weylS_not_long (h hS)).elim
  · exact sup_le hB ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hS))

/-- Proper Borel overgroups containing R are exactly the long parabolic. -/
theorem long_overgroup (H : Subgroup (Model F)) (hB : borel ≤ H)
    (hH : H < ⊤) (hR : weylR ∈ H) : H = parabolic₂ := by
  apply le_antisymm
  · rcases EvenLocal.BorelOvergroups.le_parabolic H hB hH with h | h
    · exact (weylR_not_short (h hR)).elim
    · exact h
  · exact sup_le hB ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hR))

variable {P : Fin 2 → Subgroup X}

/-- Literal source equations and placements, on the very same marked quotient.
The first model endpoint is short; `shortIndex` records an explicit reversal. -/
structure RootData (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (F : Type*) [Field F] (shortIndex : Fin 2) where
  data : BorelWeylData F (X ⧸ Q.D)
  relations : data.Relations
  generate : data.whole = ⊤
  positive : data.toPositiveRoots.generated = split.U
  highest_nontrivial : data.x 0 1 ≠ 1
  short_placement : data.s ∈ Q.tits.standardParabolic {Q.simple shortIndex}
  long_placement : data.r ∈ Q.tits.standardParabolic {Q.simple (1 - shortIndex)}

variable [Finite F] (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {shortIndex : Fin 2} (d : RootData Q split F shortIndex)

/-- The constructed root-marked equivalence on the literal source quotient. -/
def quotientEquiv : (X ⧸ Q.D) ≃* Model F :=
  d.data.equivalence d.relations d.generate d.highest_nontrivial

@[simp] theorem quotientEquiv_root (i : Fin 6) (a : F) :
    quotientEquiv Q split d (d.data.x i a) = (modelData (F := F)).x i a :=
  d.data.equivalence_root d.relations d.generate d.highest_nontrivial i a

@[simp] theorem quotientEquiv_torus (p : Fˣ × Fˣ) :
    quotientEquiv Q split d (d.data.torus p) = torusHom p :=
  d.data.equivalence_torus d.relations d.generate d.highest_nontrivial p

@[simp] theorem quotientEquiv_r : quotientEquiv Q split d d.data.r = weylR :=
  d.data.equivalence_r d.relations d.generate d.highest_nontrivial

@[simp] theorem quotientEquiv_s : quotientEquiv Q split d d.data.s = weylS :=
  d.data.equivalence_s d.relations d.generate d.highest_nontrivial

theorem quotientEquiv_unipotent : split.U.map (quotientEquiv Q split d).toMonoidHom = unipotent := by
  rw [← d.positive]
  exact map_positive d.data _ (quotientEquiv_root Q split d)

/-- Normalizers identify the entire Borel without assuming any Cartan equality. -/
theorem quotientEquiv_borel : Q.tits.B.map (quotientEquiv Q split d).toMonoidHom = borel := by
  rw [← split.normalizer_eq, map_normalizer_eq_of_bijective _ (quotientEquiv Q split d).bijective,
    quotientEquiv_unipotent, SylowNormalizer.normalizer_unipotent]

theorem quotientEquiv_short :
    (Q.tits.standardParabolic {Q.simple shortIndex}).map
      (quotientEquiv Q split d).toMonoidHom = parabolic₁ := by
  have hp : IsCoatom ((Q.tits.standardParabolic {Q.simple shortIndex}).map
      (quotientEquiv Q split d).toMonoidHom) :=
    (OrderIso.isCoatom_iff (quotientEquiv Q split d).mapSubgroup _).mpr (Q.parabolic_isCoatom _)
  refine short_overgroup _ ?_ (lt_top_iff_ne_top.mpr hp.ne_top) ?_
  · rw [← quotientEquiv_borel Q split d]
    exact map_mono (Q.tits.B_le_standardParabolic _)
  · rw [← quotientEquiv_s Q split d]
    exact mem_map_of_mem _ d.short_placement

theorem quotientEquiv_long :
    (Q.tits.standardParabolic {Q.simple (1 - shortIndex)}).map
      (quotientEquiv Q split d).toMonoidHom = parabolic₂ := by
  have hp : IsCoatom ((Q.tits.standardParabolic {Q.simple (1 - shortIndex)}).map
      (quotientEquiv Q split d).toMonoidHom) :=
    (OrderIso.isCoatom_iff (quotientEquiv Q split d).mapSubgroup _).mpr (Q.parabolic_isCoatom _)
  refine long_overgroup _ ?_ (lt_top_iff_ne_top.mpr hp.ne_top) ?_
  · rw [← quotientEquiv_borel Q split d]
    exact map_mono (Q.tits.B_le_standardParabolic _)
  · rw [← quotientEquiv_r Q split d]
    exact mem_map_of_mem _ d.long_placement

omit [Finite F] [CharP F 2] in
def flagVertex (F : Type*) [Field F] (shortIndex i : Fin 2) : Subgroup (Model F) :=
  if i = shortIndex then parabolic₁ else parabolic₂

omit [Finite F] [CharP F 2] in
theorem borel_le_flagVertex (F : Type*) [Field F] (shortIndex i : Fin 2) :
    borel (K := F) ≤ flagVertex F shortIndex i := by
  unfold flagVertex
  split
  · exact borel_le_parabolic₁
  · exact borel_le_parabolic₂

omit [Finite F] [CharP F 2] in
def flagAmalgam (F : Type*) [Field F] (shortIndex : Fin 2) :
    RankTwoAmalgam (flagVertex F shortIndex 0) (borel (K := F)) (flagVertex F shortIndex 1) :=
  RankTwoAmalgam.ofSubgroups _ _ _ (borel_le_flagVertex F shortIndex 0)
    (borel_le_flagVertex F shortIndex 1)

theorem quotientEquiv_vertex (i : Fin 2) :
    (Q.tits.standardParabolic {Q.simple i}).map
      (quotientEquiv Q split d).toMonoidHom = flagVertex F shortIndex i := by
  by_cases h : i = shortIndex
  · subst i
    simpa [flagVertex] using quotientEquiv_short Q split d
  · have hi : i = 1 - shortIndex := by
      fin_cases i <;> fin_cases shortIndex <;> simp_all
    rw [flagVertex,if_neg h,hi]
    exact quotientEquiv_long Q split d

omit [Finite F] [CharP F 2] in
def restrictEquiv {Z : Type*} [Group Z] (e : Y ≃* Z)
    (A : Subgroup Y) (C : Subgroup Z) (h : A.map e.toMonoidHom = C) : A ≃* C :=
  (A.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr h)

omit [Finite F] [CharP F 2] in
private theorem standard_left_apply (b : Q.tits.B) :
    (Q.standardAmalgam.left b : X ⧸ Q.D) = b := by
  obtain ⟨x, rfl⟩ := Q.markedIso.middle.surjective b
  rw [← Q.markedIso.left_commutes]
  rw [Q.markedIso_left_apply, Q.markedIso_middle_apply]
  rfl

omit [Finite F] [CharP F 2] in
private theorem standard_right_apply (b : Q.tits.B) :
    (Q.standardAmalgam.right b : X ⧸ Q.D) = b := by
  obtain ⟨x, rfl⟩ := Q.markedIso.middle.surjective b
  rw [← Q.markedIso.right_commutes]
  rw [Q.markedIso_right_apply, Q.markedIso_middle_apply]
  rfl

/-- Restrict one constructed ambient equivalence to both endpoints and the
whole Borel. Both squares commute on actual representatives. -/
def markedIso : RankTwoAmalgam.Iso Q.standardAmalgam (flagAmalgam F shortIndex) where
  left := restrictEquiv (quotientEquiv Q split d) _ _ (quotientEquiv_vertex Q split d 0)
  middle := restrictEquiv (quotientEquiv Q split d) _ _ (quotientEquiv_borel Q split d)
  right := restrictEquiv (quotientEquiv Q split d) _ _ (quotientEquiv_vertex Q split d 1)
  left_commutes b := by
    apply Subtype.ext
    exact congrArg (quotientEquiv Q split d) (standard_left_apply Q b)
  right_commutes b := by
    apply Subtype.ext
    exact congrArg (quotientEquiv Q split d) (standard_right_apply Q b)

@[simp] theorem markedIso_left_apply (a : Q.tits.standardParabolic {Q.simple 0}) :
    ((markedIso Q split d).left a : Model F) = quotientEquiv Q split d a := rfl

@[simp] theorem markedIso_middle_apply (b : Q.tits.B) :
    ((markedIso Q split d).middle b : Model F) = quotientEquiv Q split d b := rfl

@[simp] theorem markedIso_right_apply (a : Q.tits.standardParabolic {Q.simple 1}) :
    ((markedIso Q split d).right a : Model F) = quotientEquiv Q split d a := rfl

/-- Compose with the existing marked quotient, without changing its quotient map. -/
def quotientMarkedIso : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
    (flagAmalgam F shortIndex) := Q.markedIso.trans (markedIso Q split d)

@[simp] theorem quotientMarkedIso_left_apply (a : P 0) :
    ((quotientMarkedIso Q split d).left a : Model F) = quotientEquiv Q split d (Q.q a) := by
  change quotientEquiv Q split d (Q.markedIso.left a : X ⧸ Q.D) = _
  rw [Q.markedIso_left_apply]

@[simp] theorem quotientMarkedIso_middle_apply (b : (P 0 ⊓ P 1 : Subgroup X)) :
    ((quotientMarkedIso Q split d).middle b : Model F) = quotientEquiv Q split d (Q.q b) := by
  change quotientEquiv Q split d (Q.markedIso.middle b : X ⧸ Q.D) = _
  rw [Q.markedIso_middle_apply]

@[simp] theorem quotientMarkedIso_right_apply (a : P 1) :
    ((quotientMarkedIso Q split d).right a : Model F) = quotientEquiv Q split d (Q.q a) := by
  change quotientEquiv Q split d (Q.markedIso.right a : X ⧸ Q.D) = _
  rw [Q.markedIso_right_apply]

end Atlas.G2.RootPresentationRecognition
