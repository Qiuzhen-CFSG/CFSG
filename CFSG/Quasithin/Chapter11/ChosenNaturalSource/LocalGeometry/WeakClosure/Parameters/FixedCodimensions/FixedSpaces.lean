module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Cover
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedIndex
public import Theory.Representation.ScalarCoinvariants
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Central
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.FixedSpaces
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.Dimensions

/-!
# Natural fixed spaces on the original chosen module

Fixed-point lifting in the symplectic orthogonal cover identifies every fixed
space with the full preimage of its natural fixed space. This includes nonsplit
central attachments and preserves the source A_k families. The SL₃ row uses
the vanishing of the original central part; the G₂ row uses the existing norm
lifting theorem. Together these give a uniform centralizer test in the actual
component, without choosing a complement to C_V(L).

The literal induced automizer therefore has binary fixed codimension equal to
the coefficient-field degree times natural codimension. The last application
transfers pointwise model fixation to the original source flag preimages.
Full-normalizer calculations and the hyperplane geometry remain separate.

Source: Aschbacher--Smith, I.2.3(1), B.4.6(7), and 11.2.2(1--4),
printed pp.413, 88--90, 767--768.
-/

open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.NaturalFixedSpaces
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

/-- Every representative of a fixed natural vector is fixed on the original cover. -/
theorem sp4_marked_fixed (a : Matrix.symplecticGroup (Fin 2) S.field.Carrier) (v : D.space)
    (hv : symplecticNatural 2 a (Preliminary.markedProjection D m v) =
      Preliminary.markedProjection D m v) : Preliminary.markedAction D m a v = v := by
  let := S.source.quasisimple
  let : Group.IsPerfect (Matrix.symplecticGroup (Fin 2) S.field.Carrier) :=
    Group.IsPerfect.ofSurjective (f := m.groupEquiv.toMonoidHom) m.groupEquiv.surjective
  let p : Representation.IntertwiningMap ((Preliminary.markedAction D m).comp
      (commutator (Matrix.symplecticGroup (Fin 2) S.field.Carrier)).subtype)
        (SymplecticFourOrthogonalCover.binaryNatural (K := S.field.Carrier)) :=
    { toLinearMap := (Preliminary.markedProjection D m).toLinearMap
      isIntertwining' g := (Preliminary.markedProjection D m).isIntertwining' g.val }
  have hcover := Preliminary.markedProjection_isCover D m
  have hp : IsCover p := by
    refine ⟨hcover.1, ?_, ?_⟩
    · intro w hw g
      exact hcover.2.1 hw g.val
    · apply top_unique
      rw [← hcover.2.2]
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g, w⟩, rfl⟩
      exact Coinvariants.sub_mem_ker
        (ρ := (Preliminary.markedAction D m).comp
          (commutator (Matrix.symplecticGroup (Fin 2) S.field.Carrier)).subtype)
        ⟨g, Group.IsPerfect.mem_commutator⟩ w
  exact SymplecticFourOrthogonalCover.cover_fixed_of_projection_fixed p hp
    ⟨a, Group.IsPerfect.mem_commutator⟩ v hv

/-- Exact fixed-space preimages, retaining the entire central kernel. -/
theorem sp4_marked_fixedSpace (A : Subgroup (Matrix.symplecticGroup (Fin 2) S.field.Carrier)) :
    BinaryOffender.fixedSpace (Preliminary.markedAction D m) A =
      (BinaryOffender.fixedSpace (restrictScalars (k := ZMod 2)
        (symplecticNatural (k := S.field.Carrier) 2)) A).comap
        (Preliminary.markedProjection D m).toLinearMap := by
  ext v
  constructor
  · intro hv a
    have h := LinearMap.congr_fun ((Preliminary.markedProjection D m).isIntertwining' a) v
    change Preliminary.markedProjection D m
        (Preliminary.markedAction D m a v) =
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)) a
        (Preliminary.markedProjection D m v) at h
    have ha : Preliminary.markedAction D m a v = v := hv a
    rw [ha] at h
    exact h.symm
  · intro hv a
    exact sp4_marked_fixed D S m a v (hv a)

/-- The central attachment does not change any fixed quotient dimension. -/
theorem sp4_marked_fixedCodim
    (A : Subgroup (Matrix.symplecticGroup (Fin 2) S.field.Carrier)) :
    BinaryOffender.fixedCodim (Preliminary.markedAction D m) A =
      BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
        (symplecticNatural (k := S.field.Carrier) 2)) A := by
  let q := (BinaryOffender.fixedSpace (restrictScalars (k := ZMod 2)
      (symplecticNatural (k := S.field.Carrier) 2)) A).mkQ.comp
        (Preliminary.markedProjection D m).toLinearMap
  have hq : Function.Surjective q :=
    (Submodule.mkQ_surjective _).comp (Preliminary.markedProjection_isCover D m).1
  have hk : q.ker = BinaryOffender.fixedSpace (Preliminary.markedAction D m) A := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    exact (sp4_marked_fixedSpace D S m A).symm
  exact ((Submodule.quotEquivOfEq _ _ hk.symm).trans
    (q.quotKerEquivOfSurjective hq)).finrank_eq

/-- The source A_k family is preserved on nonsplit symplectic covers. -/
theorem sp4_marked_fixedSpaceFamily (k : ℕ) :
    ChapterE.fixedSpaceFamily (Preliminary.markedAction D m) k =
      ChapterE.fixedSpaceFamily (restrictScalars (k := ZMod 2)
        (symplecticNatural (k := S.field.Carrier) 2)) k := by
  have he (A B : Subgroup (Matrix.symplecticGroup (Fin 2) S.field.Carrier)) :
      BinaryOffender.fixedSpace (Preliminary.markedAction D m) A =
        BinaryOffender.fixedSpace (Preliminary.markedAction D m) B ↔
      BinaryOffender.fixedSpace (restrictScalars (k := ZMod 2)
        (symplecticNatural (k := S.field.Carrier) 2)) A =
        BinaryOffender.fixedSpace (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := S.field.Carrier) 2)) B := by
    rw [sp4_marked_fixedSpace D S m A, sp4_marked_fixedSpace D S m B]
    constructor
    · intro h
      have hh := congrArg (Submodule.map (Preliminary.markedProjection D m).toLinearMap) h
      simpa only [Submodule.map_comap_eq_of_surjective
        (Preliminary.markedProjection_isCover D m).1] using hh
    · exact congrArg (Submodule.comap (Preliminary.markedProjection D m).toLinearMap)
  ext A
  simp only [ChapterE.fixedSpaceFamily, Set.mem_ofPred_eq, he]


omit m in
/-- The source SL₃ quotient has no central attachment. -/
theorem sl3_centralizes_vector_iff
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) (l : L) (v : V) :
    (l : G) * (v : G) = (v : G) * (l : G) ↔
      (Coordinates.sl3 m).modelAction ((Coordinates.sl3 m).quotientMap l)
        ((Coordinates.sl3 m).projection v).toAdd = ((Coordinates.sl3 m).projection v).toAdd := by
  have hinj : Function.Injective (Coordinates.sl3 m).projection := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro w hw
    have hc := ((Coordinates.sl3 m).projection_eq_one_iff w).mp hw
    have hz : (w : G) ∈ (⊥ : Subgroup G) := by
      rw [← Preliminary.sl3_centralizer_eq_bot D S m]
      exact ⟨w.property, hc⟩
    exact Subtype.ext hz
  constructor
  · intro hc
    rw [← (Coordinates.sl3 m).projection_component_conjugation]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr hc
  · intro hv
    rw [← (Coordinates.sl3 m).projection_component_conjugation] at hv
    have he := hinj (congrArg Multiplicative.ofAdd hv)
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)

/-- The centralizer test also holds on nonsplit symplectic covers. -/
theorem sp4_centralizes_vector_iff (l : L) (v : V) :
    (l : G) * (v : G) = (v : G) * (l : G) ↔
      (Coordinates.sp4 m).modelAction ((Coordinates.sp4 m).quotientMap l)
        ((Coordinates.sp4 m).projection v).toAdd = ((Coordinates.sp4 m).projection v).toAdd := by
  constructor
  · intro hc
    rw [← (Coordinates.sp4 m).projection_component_conjugation]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr hc
  · intro hv
    let w : D.space := (D.spaceEquiv.symm v).toAdd
    have hw : (w.val.toMul.val : G) = (v : G) :=
      (D.spaceEquiv_apply w).symm.trans
        (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
    have he := sp4_marked_fixed D S m ((Coordinates.sp4 m).quotientMap l) w hv
    change Preliminary.markedAction D m (m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) w = w at he
    rw [Preliminary.markedAction_mk] at he
    have hh := congrArg (fun z : D.space => (z.val.toMul.val : G)) he
    change (l : G) * (w.val.toMul.val : G) * (l : G)⁻¹ = (w.val.toMul.val : G) at hh
    rw [hw] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh

omit m in
/-- A component element centralizes an actual vector exactly when its model fixes
the image under the literal coordinate projection. -/
theorem centralizes_vector_iff (c : Coordinates D S.field) (l : L) (v : V) :
    (l : G) * (v : G) = (v : G) * (l : G) ↔
      c.modelAction (c.quotientMap l) (c.projection v).toAdd = (c.projection v).toAdd := by
  cases c with
  | sl3 m => exact sl3_centralizes_vector_iff D S m l v
  | sp4 m => exact sp4_centralizes_vector_iff D S m l v
  | g2 m => exact G2.centralizes_vector_iff D S m l v

omit m in
/-- The literal image of an ambient actor in the chosen model group. -/
def modelActor (c : Coordinates D S.field) (A : Subgroup G) : Subgroup c.ModelGroup :=
  (A.subgroupOf L).map c.quotientMap

omit m in
/-- The ambient relative centralizer is the full preimage of the natural fixed space. -/
theorem relative_centralizer_eq_preimage (c : Coordinates D S.field)
    (A : Subgroup G) (hA : A ≤ L) :
    V ⊓ centralizer (A : Set G) =
      c.preimage (Representation.invariants (c.modelAction.comp (modelActor D S c A).subtype)) := by
  ext v
  constructor
  · rintro ⟨hvV, hvC⟩
    apply (c.mem_preimage _ ⟨v, hvV⟩).mpr
    rintro ⟨b, l, hl, rfl⟩
    exact (centralizes_vector_iff D S c l ⟨v, hvV⟩).mp (hvC l hl)
  · intro hv
    have hvV := D.centralQuotientPreimage_le _ hv
    refine ⟨hvV, ?_⟩
    intro a ha
    apply (centralizes_vector_iff D S c ⟨a, hA ha⟩ ⟨v, hvV⟩).mpr
    exact (c.mem_preimage _ ⟨v, hvV⟩).mp hv
      ⟨c.quotientMap ⟨a, hA ha⟩, ⟨⟨a, hA ha⟩, ha, rfl⟩⟩

omit m in
/-- Exact fixed codimension for the actual induced automizer of a component actor. -/
theorem component_fixedCodim (c : Coordinates D S.field) (A : Subgroup G) (hA : A ≤ L) :
    letI := D.elementary
    Representation.BinaryOffender.fixedCodim (ChapterE.automizerRepresentation V)
      (ChapterE.inducedAutomizer V A) =
      S.field.degree * Module.finrank S.field.Carrier
        (c.Space ⧸ Representation.invariants (c.modelAction.comp (modelActor D S c A).subtype)) := by
  let := D.elementary
  rw [ChapterE.fixedCodim_inducedAutomizer V A (hA.trans D.normalizes),
    relative_centralizer_eq_preimage D S c A hA, NaturalDimensions.pullback_corank D S c]


omit m in
/-- The original module and its marked natural quotient have identical fixed
codimensions for each component actor. -/
theorem component_fixedCodim_binary (c : Coordinates D S.field)
    (A : Subgroup G) (hA : A ≤ L) :
    letI := D.elementary
    Representation.BinaryOffender.fixedCodim (ChapterE.automizerRepresentation V)
      (ChapterE.inducedAutomizer V A) =
      Representation.BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2) c.modelAction)
        (modelActor D S c A) := by
  rw [component_fixedCodim D S c A hA,
    Representation.BinaryOffender.fixedCodim_restrictScalars,
    coefficient_finrank_of_card 2 _ S.field.card_eq]

omit m in
/-- Component fixed codimensions are multiples of the actual field degree. -/
theorem component_fixedCodim_multiple (c : Coordinates D S.field)
    (A : Subgroup G) (hA : A ≤ L) :
    letI := D.elementary
    S.field.degree ∣ Representation.BinaryOffender.fixedCodim
      (ChapterE.automizerRepresentation V) (ChapterE.inducedAutomizer V A) := by
  rw [component_fixedCodim D S c A hA]
  exact dvd_mul_right _ _

omit m in
/-- Whole subspace preimages are centralized exactly by their pointwise model fixers. -/
theorem centralizes_preimage_iff (c : Coordinates D S.field)
    (U : Submodule S.field.Carrier c.Space) (A : Subgroup G) (hA : A ≤ L) :
    c.preimage U ≤ centralizer (A : Set G) ↔
      ∀ a : A, ∀ u ∈ U, c.modelAction (c.quotientMap ⟨a, hA a.property⟩) u = u := by
  constructor
  · intro hc a u hu
    obtain ⟨v, hv⟩ := c.projection_surjective (Multiplicative.ofAdd u)
    have hUv : (v : G) ∈ c.preimage U := by
      apply (c.mem_preimage U v).mpr
      change (c.projection v).toAdd ∈ U
      rw [hv]
      exact hu
    have hh := (centralizes_vector_iff D S c ⟨a, hA a.property⟩ v).mp
      ((hc hUv) a a.property)
    rw [hv] at hh
    exact hh
  · intro hf v hv a ha
    let v' : V := ⟨v, D.centralQuotientPreimage_le _ hv⟩
    apply (centralizes_vector_iff D S c ⟨a, hA ha⟩ v').mpr
    exact hf ⟨a, ha⟩ _ ((c.mem_preimage U v').mp hv)

omit m in
/-- Application to the original source flag, with the same quotient map and actor. -/
theorem flag_centralizes_of_model_fixed {c : Coordinates D S.field}
    (f : InvariantFlag c) (i : Fin 3) (A : Subgroup G) (hA : A ≤ L)
    (hf : ∀ a : A, ∀ u ∈ f.space i,
      c.modelAction (c.quotientMap ⟨a, hA a.property⟩) u = u) :
    f.Vi i ≤ centralizer (A : Set G) :=
  (centralizes_preimage_iff D S c (f.space i) A hA).mpr hf

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.NaturalFixedSpaces
