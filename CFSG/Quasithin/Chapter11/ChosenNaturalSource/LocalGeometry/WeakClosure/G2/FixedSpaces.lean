module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Cover
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.Representation.G2NaturalExtensions.FixedSpaces
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module

/-!
# Fixed spaces on the original chosen G₂ module

The chosen module is a central cover under its actual quotient marking.
Perfectness of that marked component supplies derived generation, so the
proved octonion norm argument lifts every fixed natural vector to every
original representative. This yields an exact centralizer test for preimages
of field subspaces, and preserves the source A_k families on the marked
whole module. The final application concerns the original flag preimages.

No splitting of C_V(L) or field structure on that kernel is assumed.
These results supply the fixed-space transfer needed by the B.4.6 model
geometry in 11.2.2; they do not assert the root-plane or R₁-localization
constructions. Source: Aschbacher--Smith, B.4.6(7), printed p.88, and
11.2.2(5--6), printed pp.767--768.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

private theorem marked_fixed (a : Atlas.G2.Model S.field.Carrier) (v : D.space)
    (hv : Atlas.G2.Natural.action S.field.Carrier a (Preliminary.markedProjection D m v) =
      Preliminary.markedProjection D m v) : Preliminary.markedAction D m a v = v := by
  let := S.source.quasisimple
  let : Group.IsPerfect (Atlas.G2.Model S.field.Carrier) :=
    Group.IsPerfect.ofSurjective (f := m.groupEquiv.toMonoidHom) m.groupEquiv.surjective
  have hcover := Preliminary.markedProjection_isCover D m
  have hgen : Coinvariants.ker ((Preliminary.markedAction D m).comp
      (commutator (Atlas.G2.Model S.field.Carrier)).subtype) = ⊤ := by
    apply top_unique
    rw [← hcover.2.2]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, v⟩, rfl⟩
    exact Coinvariants.sub_mem_ker
      (ρ := (Preliminary.markedAction D m).comp
        (commutator (Atlas.G2.Model S.field.Carrier)).subtype)
      ⟨a, Group.IsPerfect.mem_commutator⟩ v
  exact Atlas.G2.Natural.Extensions.fixed_of_natural_fixed
    (Preliminary.markedAction D m) (Preliminary.markedProjection D m).toLinearMap
    hcover.1 hcover.2.1 hgen
    (fun a v => LinearMap.congr_fun ((Preliminary.markedProjection D m).isIntertwining' a) v)
    a v hv

/-- Fixing the marked natural quotient fixes the actual original vector. -/
theorem centralizes_vector_iff (l : L) (v : V) :
    (l : G) * (v : G) = (v : G) * (l : G) ↔
      (Coordinates.g2 m).modelAction ((Coordinates.g2 m).quotientMap l)
        ((Coordinates.g2 m).projection v).toAdd = ((Coordinates.g2 m).projection v).toAdd := by
  constructor
  · intro hc
    rw [← (Coordinates.g2 m).projection_component_conjugation]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr hc
  · intro hv
    let w : D.space := (D.spaceEquiv.symm v).toAdd
    have hw : (w.val.toMul.val : G) = (v : G) :=
      (D.spaceEquiv_apply w).symm.trans
        (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
    have he := marked_fixed D S m ((Coordinates.g2 m).quotientMap l) w hv
    change Preliminary.markedAction D m (m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) w = w at he
    rw [Preliminary.markedAction_mk] at he
    have hh := congrArg (fun z : D.space => (z.val.toMul.val : G)) he
    change (l : G) * (w.val.toMul.val : G) * (l : G)⁻¹ = (w.val.toMul.val : G) at hh
    rw [hw] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh

/-- The entire preimage of a field subspace is centralized exactly when the
literal image actor fixes that subspace pointwise. -/
theorem centralizes_preimage_iff (U : Submodule S.field.Carrier (Coordinates.g2 m).Space)
    (A : Subgroup G) (hA : A ≤ L) :
    (Coordinates.g2 m).preimage U ≤ centralizer (A : Set G) ↔
      ∀ a : A, ∀ u ∈ U, (Coordinates.g2 m).modelAction
        ((Coordinates.g2 m).quotientMap ⟨a, hA a.property⟩) u = u := by
  constructor
  · intro hc a u hu
    obtain ⟨v, hv⟩ := (Coordinates.g2 m).projection_surjective (Multiplicative.ofAdd u)
    have hUv : (v : G) ∈ (Coordinates.g2 m).preimage U := by
      apply ((Coordinates.g2 m).mem_preimage U v).mpr
      change ((Coordinates.g2 m).projection v).toAdd ∈ U
      rw [hv]
      exact hu
    have hh := (centralizes_vector_iff D S m ⟨a, hA a.property⟩ v).mp
      ((hc hUv) a a.property)
    rw [hv] at hh
    exact hh
  · intro hf v hv a ha
    let v' : V := ⟨v, D.centralQuotientPreimage_le _ hv⟩
    apply (centralizes_vector_iff D S m ⟨a, hA ha⟩ v').mpr
    exact hf ⟨a, ha⟩ _ (((Coordinates.g2 m).mem_preimage U v').mp hv)

/-- B.4.6(7) for every subgroup of the marked component, on the original
chosen module and the original projection through its central fixed space. -/
theorem marked_fixedSpace (A : Subgroup (Atlas.G2.Model S.field.Carrier)) :
    BinaryOffender.fixedSpace (Preliminary.markedAction D m) A =
      (BinaryOffender.fixedSpace (restrictScalars (k := ZMod 2)
        (g2Natural S.field.Carrier)) A).comap
        (Preliminary.markedProjection D m).toLinearMap := by
  ext v
  constructor
  · intro hv a
    have h := LinearMap.congr_fun ((Preliminary.markedProjection D m).isIntertwining' a) v
    change Preliminary.markedProjection D m
        (Preliminary.markedAction D m a v) =
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)) a
        (Preliminary.markedProjection D m v) at h
    have ha : Preliminary.markedAction D m a v = v := hv a
    rw [ha] at h
    exact h.symm
  · intro hv a
    exact marked_fixed D S m a v (hv a)

/-- The source A_k condition is unchanged on the actual central extension.
The group, elementary-abelian condition and relative indices are identical. -/
theorem marked_fixedSpaceFamily (k : ℕ) :
    ChapterE.fixedSpaceFamily (Preliminary.markedAction D m) k =
      ChapterE.fixedSpaceFamily (restrictScalars (k := ZMod 2)
        (g2Natural S.field.Carrier)) k := by
  have he (A B : Subgroup (Atlas.G2.Model S.field.Carrier)) :
      BinaryOffender.fixedSpace (Preliminary.markedAction D m) A =
        BinaryOffender.fixedSpace (Preliminary.markedAction D m) B ↔
      BinaryOffender.fixedSpace (restrictScalars (k := ZMod 2)
        (g2Natural S.field.Carrier)) A =
        BinaryOffender.fixedSpace (restrictScalars (k := ZMod 2)
          (g2Natural S.field.Carrier)) B := by
    rw [marked_fixedSpace D S m A, marked_fixedSpace D S m B]
    constructor
    · intro h
      have hh := congrArg (Submodule.map (Preliminary.markedProjection D m).toLinearMap) h
      simpa only [Submodule.map_comap_eq_of_surjective
        (Preliminary.markedProjection_isCover D m).1] using hh
    · exact congrArg (Submodule.comap (Preliminary.markedProjection D m).toLinearMap)
  ext A
  simp only [ChapterE.fixedSpaceFamily, Set.mem_ofPred_eq, he]

/-- The actual source flag inherits every pointwise fixed-space calculation
for an actor contained in the component; the central part is retained. -/
theorem flag_centralizes_of_model_fixed (f : InvariantFlag (Coordinates.g2 m))
    (i : Fin 3) (A : Subgroup G) (hA : A ≤ L)
    (hf : ∀ a : A, ∀ u ∈ f.space i, (Coordinates.g2 m).modelAction
      ((Coordinates.g2 m).quotientMap ⟨a, hA a.property⟩) u = u) :
    f.Vi i ≤ centralizer (A : Set G) :=
  (centralizes_preimage_iff D S m (f.space i) A hA).mpr hf

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2
