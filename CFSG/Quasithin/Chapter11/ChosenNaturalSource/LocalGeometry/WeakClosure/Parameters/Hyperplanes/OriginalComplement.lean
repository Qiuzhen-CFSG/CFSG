module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalComplements
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Cover
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.Exceptional
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootGeometry.Minimal
/-!
# The orthogonal complement of the original escaping hyperplane

The full chosen module is reindexed by the original symplectic quotient
marking. Its marked projection is a central cover, even when the central
kernel does not split. The universal orthogonal quotient and binary
hyperplane factorization therefore produce a four-dimensional field
complement whose image is exactly the original subgroup U.

The final application starts from the escaping-hyperplane reduction, so
its hypotheses supply the order-two kernel and complement condition.
It retains the actual quotient map, identifies the component stabilizer
with N_L(U), and proves nondegeneracy of the restricted polar form.
The orthogonal orbit/maximality, cubic actor, and Sylow-fixed intersection
calculations remain in the natural-parameter task. Final discharge of the
earlier-source inputs belongs to qt-d-1222-natural-weak-closure-source.

Source: Aschbacher--Smith, I.2.3 and 11.2.2, printed pp.413 and 767.
-/

open Representation Submodule
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
@[expose] public noncomputable section

open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure
open Representation.OneCohomology
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalComplement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Linearize the original multiplicative chosen-space equivalence. -/
def spaceLinear : let := D.elementary
    D.space ≃ₗ[ZMod 2] Additive V := by
  let := D.elementary
  let e : D.space ≃+ Additive V :=
    { toFun v := Additive.ofMul (D.spaceEquiv (Multiplicative.ofAdd v))
      invFun v := (D.spaceEquiv.symm v.toMul).toAdd
      left_inv v := congrArg Multiplicative.toAdd
        (D.spaceEquiv.symm_apply_apply (Multiplicative.ofAdd v))
      right_inv v := congrArg Additive.ofMul (D.spaceEquiv.apply_symm_apply v.toMul)
      map_add' v w := congrArg Additive.ofMul (D.spaceEquiv.map_mul
        (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  exact e.toLinearEquiv (ZMod.map_smul e)

/-- The literal subgroup represented in the original chosen space. -/
def subspace (U : Subgroup G) : Submodule (ZMod 2) D.space := by
  let := D.elementary
  exact (Parameters.MinimalFixed.subspace (V := V) U).comap (spaceLinear D).toLinearMap

omit [Finite G] in
/-- Membership uses the original embedding into G. -/
theorem subspace_mem (U : Subgroup G) (v : D.space) :
    v ∈ subspace D U ↔ (D.spaceEquiv (Multiplicative.ofAdd v) : G) ∈ U := Iff.rfl

/-- The source subgroup corank is measured on the entire chosen space. -/
theorem subspace_finrank_add_corank (U : Subgroup G) :
    Module.finrank (ZMod 2) (subspace D U) +
      CFSG.Quasithin.ChapterE.subgroupCorank V U = Module.finrank (ZMod 2) D.space := by
  let := D.elementary
  change Module.finrank (ZMod 2) ((Parameters.MinimalFixed.subspace (V := V) U).comap
    (spaceLinear D).toLinearMap) + _ = _
  rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq, (spaceLinear D).finrank_eq]
  exact Parameters.MinimalFixed.subspace_finrank_add_corank U

/-- A disjoint hyperplane complements the original central kernel of order two. -/
theorem subspace_central_compl {U : Subgroup G}
    (hU : CFSG.Quasithin.ChapterE.subgroupCorank V U = 1)
    (hC : Nat.card ↥(V ⊓ centralizer (L : Set G)) = 2)
    (hint : U ⊓ (V ⊓ centralizer (L : Set G)) = ⊥) :
    IsCompl (subspace D U) (Preliminary.centralSpace D) := by
  let := D.elementary
  have hd := subspace_finrank_add_corank D U
  rw [hU] at hd
  have hc : Module.finrank (ZMod 2) (Preliminary.centralSpace D) = 1 := by
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Preliminary.centralSpace D)
    rw [Nat.card_zmod, Nat.card_congr (Preliminary.centralSpaceEquiv D), hC] at hcard
    exact Nat.pow_right_injective (by decide : 1 < 2) (by simpa using hcard.symm)
  have hi : subspace D U ⊓ Preliminary.centralSpace D = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    have hz : (D.spaceEquiv (Multiplicative.ofAdd v) : G) ∈ (⊥ : Subgroup G) := by
      rw [←hint]
      exact ⟨hv.1, (D.spaceEquiv (Multiplicative.ofAdd v)).property,
        (Preliminary.mem_centralSpace_iff D v).mp hv.2⟩
    change (D.spaceEquiv (Multiplicative.ofAdd v) : G) = 1 at hz
    change v = 0
    simpa using hz
  refine ⟨disjoint_iff.mpr hi, codisjoint_iff.mpr ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  have he := Submodule.finrank_sup_add_finrank_inf_eq (subspace D U) (Preliminary.centralSpace D)
  rw [hi, finrank_bot, hc] at he
  omega

open SymplecticFourOrthogonalCover hiding L
variable (m : ActionEquiv D.centralQuotientAction
  (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

/-- Reindex the entire chosen module by the genuine derived symplectic group. -/
def coverAction : Representation (ZMod 2)
    (SymplecticFourOrthogonalCover.L (K := S.field.Carrier)) D.space :=
  (Preliminary.markedAction D m).comp (commutator _).subtype

/-- The original central-quotient projection with that same reindexing. -/
def coverProjection : (coverAction D S m).IntertwiningMap
    (binaryNatural (K := S.field.Carrier)) where
  toLinearMap := (Preliminary.markedProjection D m).toLinearMap
  isIntertwining' g := (Preliminary.markedProjection D m).isIntertwining' g.val

/-- Perfectness loses no commutator generation when restricting to the derived group. -/
theorem coverProjection_isCover : IsCover (coverProjection D S m) := by
  let := S.source.quasisimple
  let : Group.IsPerfect (Matrix.symplecticGroup (Fin 2) S.field.Carrier) :=
    Group.IsPerfect.ofSurjective (f := m.groupEquiv.toMonoidHom) m.groupEquiv.surjective
  have hp := Preliminary.markedProjection_isCover D m
  refine ⟨hp.1,?_,?_⟩
  · intro v hv g
    exact hp.2.1 hv g.val
  · apply top_unique
    rw [←hp.2.2]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,w⟩,rfl⟩
    exact Coinvariants.sub_mem_ker
      (ρ := coverAction D S m) ⟨g,Group.IsPerfect.mem_commutator⟩ w

/-- The universal quotient lies over the original natural projection and central kernel. -/
theorem exists_original_cover :
    ∃ f : (binaryAction (K := S.field.Carrier)).IntertwiningMap
      (coverAction D S m),
      Function.Surjective f ∧
      (∀ x, Preliminary.markedProjection D m (f x) = binaryProjection x) ∧
      f.toLinearMap.ker ≤ (radical (K := S.field.Carrier)).restrictScalars (ZMod 2) ∧
      ((radical (K := S.field.Carrier)).restrictScalars (ZMod 2)).map f.toLinearMap =
        Preliminary.centralSpace D := by
  obtain ⟨f,hf,hp⟩ := exists_cover_quotient
    (coverProjection D S m) (coverProjection_isCover D S m)
  obtain ⟨hk,hr⟩ := OrthogonalComplements.cover_map_radical
    (coverProjection D S m) f hf hp
  exact ⟨f,hf,hp,hk,hr.trans (Preliminary.markedProjection_ker D m)⟩

/-- Construct a field complement mapping injectively onto this same binary hyperplane. -/
theorem exists_original_field_complement {U : Subgroup G}
    (hUV : U ≤ V) (hU : CFSG.Quasithin.ChapterE.subgroupCorank V U = 1)
    (hC : Nat.card ↥(V ⊓ centralizer (L : Set G)) = 2)
    (hint : U ⊓ (V ⊓ centralizer (L : Set G)) = ⊥) :
    ∃ f : (binaryAction (K := S.field.Carrier)).IntertwiningMap
      (coverAction D S m),
      Function.Surjective f ∧
      (∀ x, Preliminary.markedProjection D m (f x) = binaryProjection x) ∧
      ∃ Q : Submodule S.field.Carrier (Space (K := S.field.Carrier)),
        Module.finrank S.field.Carrier Q = 4 ∧ IsCompl Q radical ∧
        (Q.restrictScalars (ZMod 2)).map f.toLinearMap = subspace D U ∧
        Disjoint (Q.restrictScalars (ZMod 2)) f.toLinearMap.ker ∧
        (∀ P : Submodule S.field.Carrier (Space (K := S.field.Carrier)),
          (P.restrictScalars (ZMod 2)).map f.toLinearMap ≤ subspace D U → P ≤ Q) ∧
        (∀ u : G, u ∈ U ↔ ∃ x ∈ Q, (D.spaceEquiv (Multiplicative.ofAdd (f x)) : G) = u) := by
  have hd := subspace_finrank_add_corank D U
  rw [hU] at hd
  have hc : IsCompl (subspace D U) (coverProjection D S m).toLinearMap.ker := by
    change IsCompl (subspace D U) (Preliminary.markedProjection D m).toLinearMap.ker
    rw [Preliminary.markedProjection_ker]
    exact subspace_central_compl D hU hC hint
  obtain ⟨f,hf,hp,Q,hQ,hQR,hQU,hkerQ,hgreat⟩ := OrthogonalComplements.exists_field_complement
    (coverProjection D S m) (coverProjection_isCover D S m) (subspace D U) hd hc
  refine ⟨f,hf,hp,Q,hQ,hQR,hQU,hkerQ,hgreat,?_⟩
  intro u
  constructor
  · intro hu
    let v : V := ⟨u,hUV hu⟩
    let w : D.space := (D.spaceEquiv.symm v).toAdd
    have hw : w ∈ subspace D U := by
      change (D.spaceEquiv (D.spaceEquiv.symm v) : G) ∈ U
      simpa using hu
    rw [←hQU] at hw
    obtain ⟨x,hx,hxw⟩ := hw
    refine ⟨x,hx,?_⟩
    change f x = w at hxw
    rw [hxw]
    exact congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v)
  · rintro ⟨x,hx,rfl⟩
    apply (subspace_mem D U (f x)).mp
    rw [←hQU]
    exact ⟨x,hx,rfl⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalComplement

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalComplement
open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure
open SymplecticFourOrthogonalCover hiding L
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

/-- The marked action is the literal original conjugation action. -/
theorem markedAction_ambient (l : L) (v : D.space) :
    (D.spaceEquiv (Multiplicative.ofAdd
      (Preliminary.markedAction D m ((Coordinates.sp4 m).quotientMap l) v)) : G) =
      (l : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (l : G)⁻¹ := by
  change (D.spaceEquiv (Multiplicative.ofAdd
    (Preliminary.markedAction D m (m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) v)) : G) = _
  rw [Preliminary.markedAction_mk, D.spaceEquiv_apply, D.spaceEquiv_apply]
  rfl

/-- Stabilizing the chosen-coordinate subspace is exactly normalizing U in G. -/
theorem subspace_stabilizer_iff {U : Subgroup G} (hUV : U ≤ V) (l : L) :
    (subspace D U).map (Preliminary.markedAction D m ((Coordinates.sp4 m).quotientMap l)) =
      subspace D U ↔ (l : G) ∈ normalizer (U : Set G) := by
  let := D.elementary
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmem (x : D.space) : x ∈ (subspace D U).map
      (Preliminary.markedAction D m ((Coordinates.sp4 m).quotientMap l)) ↔
      (D.spaceEquiv (Multiplicative.ofAdd x) : G) ∈ U.map (MulAut.conj (l : G)).toMonoidHom := by
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨D.spaceEquiv (Multiplicative.ofAdd w),hw, (markedAction_ambient D S m l w).symm⟩
    · rintro ⟨u,hu,he⟩
      let w : D.space := (D.spaceEquiv.symm ⟨u,hUV hu⟩).toAdd
      have hw : (D.spaceEquiv (Multiplicative.ofAdd w) : G) = u :=
        congrArg Subtype.val (D.spaceEquiv.apply_symm_apply ⟨u,hUV hu⟩)
      refine ⟨w,(subspace_mem D U w).mpr (hw.symm ▸ hu),?_⟩
      apply (spaceLinear D).injective
      apply Subtype.ext
      change (D.spaceEquiv (Multiplicative.ofAdd
        (Preliminary.markedAction D m ((Coordinates.sp4 m).quotientMap l) w)) : G) = _
      rw [markedAction_ambient,hw]
      exact he
  constructor
  · intro he
    apply le_antisymm
    · rintro y hy
      have hyV : y ∈ V := by
        obtain ⟨u,hu,rfl⟩ := hy
        exact (Subgroup.mem_normalizer_iff.mp (D.normalizes l.property) u).mp (hUV hu)
      let w : D.space := (D.spaceEquiv.symm ⟨y,hyV⟩).toAdd
      have hw : (D.spaceEquiv (Multiplicative.ofAdd w) : G) = y :=
        congrArg Subtype.val (D.spaceEquiv.apply_symm_apply ⟨y,hyV⟩)
      have hm := (hmem w).mpr (hw.symm ▸ hy)
      rw [he] at hm
      exact hw ▸ (subspace_mem D U w).mp hm
    · intro y hy
      let w : D.space := (D.spaceEquiv.symm ⟨y,hUV hy⟩).toAdd
      have hw : (D.spaceEquiv (Multiplicative.ofAdd w) : G) = y :=
        congrArg Subtype.val (D.spaceEquiv.apply_symm_apply ⟨y,hUV hy⟩)
      have hm : w ∈ subspace D U := (subspace_mem D U w).mpr (hw.symm ▸ hy)
      rw [←he] at hm
      exact hw ▸ (hmem w).mp hm
  · intro he
    change U.map (MulAut.conj (l : G)).toMonoidHom = U at he
    ext x
    rw [hmem,he,subspace_mem]

/-- The field-complement stabilizer pulls back to the literal component normalizer. -/
theorem original_field_stabilizer_iff
    (f : (binaryAction (K := S.field.Carrier)).IntertwiningMap
      (coverAction D S m))
    {U : Subgroup G} (hUV : U ≤ V)
    (Q : Submodule S.field.Carrier (Space (K := S.field.Carrier)))
    (him : (Q.restrictScalars (ZMod 2)).map f.toLinearMap = subspace D U)
    (hgreat : ∀ P : Submodule S.field.Carrier (Space (K := S.field.Carrier)),
      (P.restrictScalars (ZMod 2)).map f.toLinearMap ≤ subspace D U → P ≤ Q)
    (l : L) :
    Q.map (fullAction ((Coordinates.sp4 m).quotientMap l)) = Q ↔
      (l : G) ∈ normalizer (U : Set G) := by
  let := S.source.quasisimple
  let : Group.IsPerfect (Matrix.symplecticGroup (Fin 2) S.field.Carrier) :=
    Group.IsPerfect.ofSurjective (f := m.groupEquiv.toMonoidHom) m.groupEquiv.surjective
  let a := (Coordinates.sp4 m).quotientMap l
  let a' : SymplecticFourOrthogonalCover.L (K := S.field.Carrier) :=
    ⟨a,Group.IsPerfect.mem_commutator⟩
  exact (OrthogonalComplements.stabilizer_iff f Q (subspace D U) him hgreat a').trans
    (subspace_stabilizer_iff D S m hUV l)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalComplement

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalComplement
open Subgroup Representation
open Representation.SymplecticFourOrthogonalCover hiding L
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The actual escaping hyperplane is the image of an orthogonal complement,
with the same projection and the literal component normalizer. -/
theorem escaping_hyperplane_field_complement (c : Coordinates D S.field)
    (hE : HypothesisE61 CFSG.KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) :
    ∃ m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)),
      S.field.degree = 2 ∧
      ∃ f : (binaryAction (K := S.field.Carrier)).IntertwiningMap (coverAction D S m),
        Function.Surjective f ∧
        (∀ x, Preliminary.markedProjection D m (f x) = binaryProjection x) ∧
        ∃ Q : Submodule S.field.Carrier (Space (K := S.field.Carrier)),
          Module.finrank S.field.Carrier Q = 4 ∧ IsCompl Q radical ∧
          (Q.restrictScalars (ZMod 2)).map f.toLinearMap = subspace D U ∧
          Disjoint (Q.restrictScalars (ZMod 2)) f.toLinearMap.ker ∧
          (∀ P : Submodule S.field.Carrier (Space (K := S.field.Carrier)),
            (P.restrictScalars (ZMod 2)).map f.toLinearMap ≤ subspace D U → P ≤ Q) ∧
          (∀ u : G, u ∈ U ↔ ∃ x ∈ Q,
            (D.spaceEquiv (Multiplicative.ofAdd (f x)) : G) = u) ∧
          (LinearMap.BilinForm.restrict (ClassicalOrthogonal.formB 2 S.field.Carrier).polarBilin Q).Nondegenerate ∧
          (∀ l : L, Q.map (fullAction ((Coordinates.sp4 m).quotientMap l)) = Q ↔
            (l : G) ∈ normalizer (U : Set G)) := by
  obtain ⟨⟨m⟩,hn,hC,hi,_⟩ := escaping_hyperplane_sp4_four D S c hE hunique hUV hU hescape
  obtain ⟨f,hf,hp,Q,hQ,hQR,him,hker,hgreat,hambient⟩ :=
    exists_original_field_complement D S m hUV hU hC hi
  exact ⟨m,hn,f,hf,hp,Q,hQ,hQR,him,hker,hgreat,hambient,
    OrthogonalComplements.complement_polar_nondegenerate Q hQR,
    original_field_stabilizer_iff D S m f hUV Q him hgreat⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalComplement
