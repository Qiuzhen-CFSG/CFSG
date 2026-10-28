module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalMaximality
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.SemilinearComplements
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.Representation.CentralCoverOriginalAction
public import Theory.Representation.SymplecticFourBinaryNormalizer

/-!
# The normalizer supplement for the original nonsplit hyperplane

The actual Sylow action on the natural quotient is semilinear. Its explicit
orthogonal lift agrees with the Sylow action through the original cover map:
equivariant maps with the same central projection agree on a module generated
by commutators. Thus the field-complement correction acts on the whole cover,
and its image is the same original binary hyperplane U.

For each t in T this gives l in L with lt in N_G(U), proving
N_LT(U) join L = LT. The existing maximality, cubic-action and fixed-intersection
results now apply E.6.14 with every orthogonal premise discharged. Source
11.2.2(1--4) is assembled in Parameters.Source; the earlier-source premises
retain final discharge by qt-d-1222-natural-weak-closure-source.

Source: Aschbacher--Smith, 11.2.2, printed pp.767--768, and I.2.3, p.413.
-/

open Matrix.PSp4Three
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalMaximality
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalSupplement
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter11.ChosenNaturalSource
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
open OriginalComplement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

def sylowOperator (t : T) : D.space ≃ₗ[ZMod 2] D.space := by
  let a : D.space ≃+ D.space := ((D.spaceEquiv.trans
    (V.normalizerMonoidHom (inclusion S.sylow_normalizes t))).trans D.spaceEquiv.symm).toAdditive
  exact a.toLinearEquiv (ZMod.map_smul a)

theorem sylowOperator_ambient (t : T) (v : D.space) :
    (D.spaceEquiv (Multiplicative.ofAdd (sylowOperator D S t v)) : G) =
      (t : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (t : G)⁻¹ := by
  change (D.spaceEquiv (D.spaceEquiv.symm
    (V.normalizerMonoidHom (inclusion S.sylow_normalizes t)
      (D.spaceEquiv (Multiplicative.ofAdd v)))) : G) = _
  rw [D.spaceEquiv.apply_symm_apply]
  rfl

def sylowModelAut (t : T) : MulAut (Matrix.symplecticGroup (Fin 2) S.field.Carrier) :=
  (MulAut.congr m.groupEquiv)
    (quotientAut (pCore 2 L) (L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t)))

theorem sylowModelAut_mk (t : T) (l : L) :
    sylowModelAut D S m t ((Coordinates.sp4 m).quotientMap l) =
      (Coordinates.sp4 m).quotientMap
        (L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t) l) := by
  change m.groupEquiv (quotientAut (pCore 2 L) (L.normalizerMonoidHom _)
    (m.groupEquiv.symm (m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)))) = _
  rw [m.groupEquiv.symm_apply_apply, quotientAut_apply_mk]
  rfl

theorem sylowOperator_intertwines (t : T)
    (g : Matrix.symplecticGroup (Fin 2) S.field.Carrier) (v : D.space) :
    sylowOperator D S t (Preliminary.markedAction D m g v) =
      Preliminary.markedAction D m (sylowModelAut D S m t g) (sylowOperator D S t v) := by
  obtain ⟨l,rfl⟩ := (Coordinates.sp4 m).quotientMap_surjective g
  rw [sylowModelAut_mk]
  let := D.elementary
  apply (spaceLinear D).injective
  apply Subtype.ext
  change (D.spaceEquiv (Multiplicative.ofAdd _ ) : G) =
    (D.spaceEquiv (Multiplicative.ofAdd _) : G)
  rw [sylowOperator_ambient, markedAction_ambient, markedAction_ambient,
    sylowOperator_ambient]
  change (t : G) * ((l : G) * _ * (l : G)⁻¹) * (t : G)⁻¹ =
    ((t : G) * (l : G) * (t : G)⁻¹) * ((t : G) * _ * (t : G)⁻¹) *
      ((t : G) * (l : G) * (t : G)⁻¹)⁻¹
  group

theorem sylowOperator_projection (t : T) (v : D.space) :
    Preliminary.markedProjection D m (sylowOperator D S t v) =
      (Coordinates.sp4 m).sylowAction S t (Preliminary.markedProjection D m v) := by
  have h := (Coordinates.sp4 m).conjugationAction_projection
    D.sylow_normalizes_component S.sylow_normalizes t
    (D.spaceEquiv (Multiplicative.ofAdd v))
  change (Coordinates.sp4 m).sylowAction S t
    (m.linearEquiv (Submodule.Quotient.mk
      (D.spaceEquiv.symm (D.spaceEquiv (Multiplicative.ofAdd v))).toAdd)) = _ at h
  rw [D.spaceEquiv.symm_apply_apply] at h
  exact h.symm

theorem sylowNatural_intertwines (t : T)
    (g : Matrix.symplecticGroup (Fin 2) S.field.Carrier)
    (v : Representation.SymplecticFourOrthogonalCover.Natural (K := S.field.Carrier)) :
    (Coordinates.sp4 m).sylowAction S t (symplecticNatural 2 g v) =
      symplecticNatural 2 (sylowModelAut D S m t g)
        ((Coordinates.sp4 m).sylowAction S t v) := by
  obtain ⟨w,rfl⟩ := (Preliminary.markedProjection_isCover D m).1 v
  exact (congrArg ((Coordinates.sp4 m).sylowAction S t)
      (Representation.IntertwiningMap.isIntertwining _ _
        (Preliminary.markedProjection D m) g w).symm).trans
    ((sylowOperator_projection D S m t _).symm.trans
      ((congrArg (Preliminary.markedProjection D m)
        (sylowOperator_intertwines D S m t g w)).trans
        ((Representation.IntertwiningMap.isIntertwining _ _
          (Preliminary.markedProjection D m) _ _).trans
          (congrArg (symplecticNatural 2 (sylowModelAut D S m t g))
            (sylowOperator_projection D S m t w)))))


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalSupplement

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalSupplement
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter11.ChosenNaturalSource
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
open OriginalComplement
open Representation.SymplecticFourOrthogonalCover hiding L
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

/-- Decompose the original Sylow operator on the same natural quotient. -/
theorem sylowNatural_decomposition (t : T) :
    ∃ (a : S.field.Carrierˣ) (g : Matrix.PSp4Three.Sp 2 S.field.Carrier)
      (σ : S.field.Carrier ≃+* S.field.Carrier),
      ∀ v, (Coordinates.sp4 m).sylowAction S t v =
        a.val • (g • (fun i => σ (v i))) := by
  let e : Matrix.PSp4Three.Vector 2 S.field.Carrier ≃ₗ[ZMod 2]
      Matrix.PSp4Three.Vector 2 S.field.Carrier :=
    linearAction ((Coordinates.sp4 m).sylowAction S) t
  let α := sylowModelAut D S m t
  let : Finite (naturalDerivedImage (F := S.field.Carrier)) :=
    Finite.of_surjective (linearAction (naturalDerivedAction (F := S.field.Carrier))).rangeRestrict
      (linearAction (naturalDerivedAction (F := S.field.Carrier))).rangeRestrict_surjective
  have hn : e ∈ naturalNormalizer := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨_,⟨l,rfl⟩,rfl⟩
      refine ⟨MulAut.characteristic (commutator _) α l, ?_⟩
      apply LinearEquiv.ext
      intro v
      change symplecticNatural 2 (α l.val) v = e (symplecticNatural 2 l.val (e.symm v))
      rw [show e (symplecticNatural 2 l.val (e.symm v)) =
        symplecticNatural 2 (α l.val) (e (e.symm v)) from
          sylowNatural_intertwines D S m t l.val (e.symm v), e.apply_symm_apply]
    · exact (Subgroup.card_map_of_injective (MulAut.conj e).injective).ge
  obtain ⟨a,g,σ,he⟩ := naturalNormalizer_semilinear e hn
  exact ⟨a,g,σ,he⟩

/-- The explicit semilinear lift descends through the original cover map.
The equality holds on the whole chosen module, not just its natural quotient. -/
theorem original_cover_equivariant (t : T)
    (f : (binaryAction (K := S.field.Carrier)).IntertwiningMap (coverAction D S m))
    (hp : ∀ x, Preliminary.markedProjection D m (f x) = binaryProjection x)
    (a : S.field.Carrierˣ) (g : Matrix.PSp4Three.Sp 2 S.field.Carrier)
    (σ : S.field.Carrier ≃+* S.field.Carrier)
    (he : ∀ v, (Coordinates.sp4 m).sylowAction S t v =
      a.val • (g • (fun i => σ (v i)))) :
    ∀ x, f (SemilinearComplements.semilinearCover a g σ x) = sylowOperator D S t (f x) := by
  let α := MulAut.characteristic (commutator _) (sylowModelAut D S m t)
  let A := SemilinearComplements.semilinearCover a g σ
  have hA (l : SymplecticFourOrthogonalCover.L (K := S.field.Carrier)) (x) :
      A (binaryAction l x) = binaryAction (α l) (A x) := by
    apply SemilinearComplements.semilinearCover_intertwines
    intro v
    exact (he (symplecticNatural 2 l.val v)).symm.trans
      ((sylowNatural_intertwines D S m t l.val v).trans
        (congrArg (symplecticNatural 2 (sylowModelAut D S m t l.val)) (he v)))
  have hmap : f.toLinearMap.comp A = (sylowOperator D S t).toLinearMap.comp f.toLinearMap := by
    apply OneCohomology.CentralCoverOriginalAction.lift_unique
      (binaryAction (K := S.field.Carrier)) ((coverAction D S m).comp α.toMonoidHom)
      binaryProjection_isCover.2.2 (Preliminary.markedProjection D m).toLinearMap
      (fun _ hw l => (coverProjection_isCover D S m).2.1 hw (α l))
    · intro l x
      change f (A (binaryAction l x)) = coverAction D S m (α l) (f (A x))
      rw [hA, Representation.IntertwiningMap.isIntertwining _ _ f]
    · intro l x
      change sylowOperator D S t (f (binaryAction l x)) =
        coverAction D S m (α l) (sylowOperator D S t (f x))
      rw [Representation.IntertwiningMap.isIntertwining _ _ f]
      exact sylowOperator_intertwines D S m t l.val (f x)
    · intro x
      change Preliminary.markedProjection D m (f (A x)) =
        Preliminary.markedProjection D m (sylowOperator D S t (f x))
      rw [hp,sylowOperator_projection,hp]
      exact (he x.1).symm
  exact fun x => LinearMap.congr_fun hmap x

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalSupplement

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalSupplement
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter11.ChosenNaturalSource
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
open OriginalComplement
open Representation.SymplecticFourOrthogonalCover hiding L
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Every actual Sylow actor has a component correction normalizing the original U. -/
theorem original_normalizer_representatives
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hn : S.field.degree = 2)
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hC : Nat.card ↥(V ⊓ centralizer (L : Set G)) = 2)
    (hint : U ⊓ (V ⊓ centralizer (L : Set G)) = ⊥) :
    ∀ t : T, ∃ l : L, (l : G) * (t : G) ∈ normalizer (U : Set G) := by
  let := S.source.quasisimple
  let : Group.IsPerfect (Matrix.symplecticGroup (Fin 2) S.field.Carrier) :=
    Group.IsPerfect.ofSurjective (f := m.groupEquiv.toMonoidHom) m.groupEquiv.surjective
  obtain ⟨f,_,hp,Q,_,hQR,him,_,_,hambient⟩ :=
    exists_original_field_complement D S m hUV hU hC hint
  intro t
  obtain ⟨a,g,σ,he⟩ := sylowNatural_decomposition D S m t
  obtain ⟨k,hk⟩ := SemilinearComplements.semilinearCover_correction
    (by rw [S.field.card_eq,hn]; norm_num) Q hQR a g σ
  obtain ⟨l,hl⟩ := (Coordinates.sp4 m).quotientMap_surjective k
  refine ⟨l,mem_normalizer_fintype (fun u hu => ?_)⟩
  obtain ⟨x,hx,rfl⟩ := (hambient u).mp hu
  have hy : f (fullAction k (SemilinearComplements.semilinearCover a g σ x)) ∈ subspace D U := by
    rw [←him]
    exact ⟨_,hk x hx,rfl⟩
  have haction : f (fullAction k (SemilinearComplements.semilinearCover a g σ x)) =
      Preliminary.markedAction D m k (f (SemilinearComplements.semilinearCover a g σ x)) :=
    Representation.IntertwiningMap.isIntertwining _ _ f
      (⟨k,Group.IsPerfect.mem_commutator⟩ : SymplecticFourOrthogonalCover.L (K := S.field.Carrier)) _
  rw [haction,original_cover_equivariant D S m t f hp a g σ he,←hl] at hy
  have hyG := (subspace_mem D U _).mp hy
  rw [markedAction_ambient, sylowOperator_ambient] at hyG
  simpa only [SetLike.mem_coe, mul_inv_rev, mul_assoc] using hyG

/-- The orbit representatives give the literal normalizer supplement in LT. -/
theorem original_stabilizer_supplement
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hn : S.field.degree = 2)
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hC : Nat.card ↥(V ⊓ centralizer (L : Set G)) = 2)
    (hint : U ⊓ (V ⊓ centralizer (L : Set G)) = ⊥) :
    localNormalizer (L ⊔ (T : Subgroup G)) U ⊔ L = L ⊔ (T : Subgroup G) := by
  apply le_antisymm (sup_le inf_le_left le_sup_left)
  apply sup_le le_sup_right
  intro t ht
  obtain ⟨l,hl⟩ := original_normalizer_representatives D S m hn hUV hU hC hint ⟨t,ht⟩
  have hlt : (l : G) * t ∈ localNormalizer (L ⊔ (T : Subgroup G)) U :=
    ⟨(L ⊔ (T : Subgroup G)).mul_mem ((show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) l.property)
      ((show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right) ht),hl⟩
  have hh := (localNormalizer (L ⊔ (T : Subgroup G)) U ⊔ L).mul_mem
    ((show L ≤ localNormalizer (L ⊔ (T : Subgroup G)) U ⊔ L from le_sup_right)
      (L.inv_mem l.property))
    ((show localNormalizer (L ⊔ (T : Subgroup G)) U ≤
      localNormalizer (L ⊔ (T : Subgroup G)) U ⊔ L from le_sup_left) hlt)
  simpa only [inv_mul_cancel_left] using hh

theorem escaping_hyperplane_supplement (c : Coordinates D S.field)
    (hE : HypothesisE61 CFSG.KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) :
    localNormalizer (L ⊔ (T : Subgroup G)) U ⊔ L = L ⊔ (T : Subgroup G) := by
  obtain ⟨⟨m⟩,hn,hC,hi,_⟩ := escaping_hyperplane_sp4_four D S c hE hunique hUV hU hescape
  exact original_stabilizer_supplement D S m hn hUV hU hC hi

/-- The source hyperplane centralizer bound with every owned orthogonal premise discharged. -/
theorem hyperplane_centralizer_le (c : Coordinates D S.field)
    (hE : HypothesisE61 CFSG.KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  exact hescape (OriginalMaximality.centralizer_le_of_stabilizer_supplement
    D S c hE hunique hUV hU (escaping_hyperplane_supplement D S c hE hunique hUV hU hescape))
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalSupplement
