module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.Quotient.ModelCocycles
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.Quotient.DualModel

/-!
# The literal Q/C_T(L) inside the dual symplectic five-space

The previously constructed displacement embedding is transported through the
actual perfect full-to-derived symplectic equivalence and the universal dual
model. The original quotient map, component action, and denominator are retained.

Source: Aschbacher–Smith C.1.13(b), I.2.3(1), 11.1.5, pp.125,413,766.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
namespace SymplecticModel
open Representation.SymplecticFourOrthogonalCover
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

private def fullDerived : Matrix.symplecticGroup (Fin 2) S.field.Carrier ≃*
    Representation.SymplecticFourOrthogonalCover.L (K := S.field.Carrier) := by
  let := S.source.quasisimple
  let : Group.IsPerfect (Matrix.symplecticGroup (Fin 2) S.field.Carrier) :=
    Group.IsPerfect.ofSurjective (f := m.groupEquiv.toMonoidHom) m.groupEquiv.surjective
  exact (MulEquiv.ofBijective (commutator (Matrix.symplecticGroup (Fin 2) S.field.Carrier)).subtype
    ⟨Subtype.val_injective,fun g => ⟨⟨g,Group.IsPerfect.mem_commutator⟩,rfl⟩⟩).symm

private theorem fullDerived_val (g : Matrix.symplecticGroup (Fin 2) S.field.Carrier) :
    (fullDerived D S m g).val = g :=
  (fullDerived D S m).symm_apply_apply g

private def reindex :
    cocycles (restrictScalars (k := ZMod 2) (Coordinates.sp4 m).modelAction) ≃ₗ[ZMod 2]
      cocycles (binaryNatural (K := S.field.Carrier)) :=
  cocyclesCongr _ _ (fullDerived D S m) (LinearEquiv.refl _ _)
    (fun g v => by
      change Matrix.symplecticGroup (Fin 2) S.field.Carrier at g
      change Natural (K := S.field.Carrier) at v
      change g.val *ᵥ v = (fullDerived D S m g).val.val *ᵥ v
      rw [fullDerived_val])

/-- The original component actor on the derived symplectic model. -/
def actor : L →* Representation.SymplecticFourOrthogonalCover.L (K := S.field.Carrier) :=
  (fullDerived D S m).toMonoidHom.comp (Coordinates.sp4 m).quotientMap

theorem actor_surjective : Function.Surjective (actor D S m) :=
  (fullDerived D S m).surjective.comp (Coordinates.sp4 m).quotientMap_surjective

/-- Forgetting the derived subgroup recovers the supplied component quotient. -/
theorem actor_val (l : L) : (actor D S m l).val = (Coordinates.sp4 m).quotientMap l :=
  fullDerived_val D S m _

/-- The actual actor has exactly the original intrinsic two-core as kernel. -/
theorem actor_ker : (actor D S m).ker = pCore 2 L := by
  ext l
  change actor D S m l = 1 ↔ l ∈ pCore 2 L
  rw [← Subtype.val_injective.eq_iff,actor_val]
  change m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ _
  rw [← m.groupEquiv.map_one,m.groupEquiv.injective.eq_iff]
  exact QuotientGroup.eq_one_iff l

/-- The actual corrected quotient map followed by the universal dual-model equivalence. -/
def embedding (hb : ChapterC.IsShort L) :
    letI := componentCentralizer_normal_core D
    (((L ⊔ (T : Subgroup G)).pCoreIn 2) ⧸
      (((T : Subgroup G) ⊓ centralizer (L : Set G)).subgroupOf
        ((L ⊔ (T : Subgroup G)).pCoreIn 2))) →*
      Multiplicative (Module.Dual (ZMod 2) (Space (K := S.field.Carrier))) := by
  letI := componentCentralizer_normal_core D
  exact ((reindex D S m).trans DualModel.equiv).toAddEquiv.toMultiplicative.toMonoidHom.comp
    (coreModelQuotientCocycle D (Coordinates.sp4 m) hb)

theorem embedding_injective (hb : ChapterC.IsShort L) : Function.Injective (embedding D S m hb) :=
  ((reindex D S m).trans DualModel.equiv).injective.comp
    (coreModelQuotientCocycle_injective D (Coordinates.sp4 m) hb)

/-- The natural layer is exactly VC_T(L)/C_T(L), on every original q. -/
theorem embedding_natural_layer (hb : ChapterC.IsShort L)
    (q : (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    (q : G) ∈ cohomologyDenominator T L V ↔
      ∀ a : S.field.Carrier, (embedding D S m hb (QuotientGroup.mk q)).toAdd (0,a) = 0 := by
  rw [←coreModelCocycle_principal_iff D (Coordinates.sp4 m) hb q]
  change _ ↔ ∀ a : S.field.Carrier,
    DualModel.equiv (reindex D S m (coreModelCocycle D (Coordinates.sp4 m) hb q)) (0,a) = 0
  rw [DualModel.equiv_annihilates_radical_iff]
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨v,(cocyclesCongr_principal _ _ _ _ _ v).symm.trans (congrArg (reindex D S m) hv)⟩
  · rintro ⟨v,hv⟩
    exact ⟨v,(reindex D S m).injective ((cocyclesCongr_principal _ _ _ _ _ v).trans hv)⟩

private theorem reindex_apply
    (f : cocycles (restrictScalars (k := ZMod 2) (Coordinates.sp4 m).modelAction))
    (g : Matrix.symplecticGroup (Fin 2) S.field.Carrier) :
    (reindex D S m f).val (fullDerived D S m g) = f.val g := by
  change f.val ((fullDerived D S m).symm (fullDerived D S m g)) = f.val g
  rw [MulEquiv.symm_apply_apply]

private theorem reindex_equivariant
    (g : Matrix.symplecticGroup (Fin 2) S.field.Carrier)
    (f : cocycles (restrictScalars (k := ZMod 2) (Coordinates.sp4 m).modelAction)) :
    reindex D S m (universalAction
      (restrictScalars (k := ZMod 2) (Coordinates.sp4 m).modelAction) g f) =
        universalAction (binaryNatural (K := S.field.Carrier)) (fullDerived D S m g)
          (reindex D S m f) := by
  change cocycles (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)) at f
  apply Subtype.ext
  funext a
  obtain ⟨b,rfl⟩ := (fullDerived D S m).surjective a
  rw [reindex_apply]
  change f.val b + (b.val *ᵥ f.val g - f.val g) =
    (reindex D S m f).val (fullDerived D S m b) +
      ((fullDerived D S m b).val.val *ᵥ (reindex D S m f).val (fullDerived D S m g) -
        (reindex D S m f).val (fullDerived D S m g))
  rw [reindex_apply,reindex_apply,fullDerived_val]

/-- Equivariance retains the literal Q-conjugation and quotient map. -/
theorem embedding_equivariant (hb : ChapterC.IsShort L) (l : L)
    (q : (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    (embedding D S m hb (QuotientGroup.mk (componentConjugateCore l q))).toAdd =
      (binaryAction (K := S.field.Carrier)).dual (actor D S m l)
        (embedding D S m hb (QuotientGroup.mk q)).toAdd := by
  change DualModel.equiv (reindex D S m
      (coreModelCocycle D (Coordinates.sp4 m) hb (componentConjugateCore l q))) = _
  rw [coreModelCocycle_equivariant,reindex_equivariant,DualModel.equiv_intertwines]
  rfl

/-- Placement of one actual conjugate long root yields the required fixed-space bound.
The embedding, its natural layer, and the dual geometry are all constructed. -/
theorem core_fixed_le_denominator_of_root_placement (hb : ChapterC.IsShort L)
    {R : Subgroup G}
    (g : Representation.SymplecticFourOrthogonalCover.L (K := S.field.Carrier))
    (hroot : Roots.conjugateGroup g ≤ (R.subgroupOf L).map (actor D S m)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (R : Set G) ≤
      cohomologyDenominator T L V := by
  rintro q ⟨hq,hfix⟩
  let q' : (L ⊔ (T : Subgroup G)).pCoreIn 2 := ⟨q,hq⟩
  apply (embedding_natural_layer D S m hb q').mpr
  apply dual_conjugate_root_fixed_annihilates_radical
    (show 2 < Nat.card S.field.Carrier by
      rw [S.field.card_eq]
      exact lt_of_le_of_lt (by decide : 2 ≤ 2^1)
        (Nat.pow_lt_pow_right (by decide : 1 < 2) S.nonbinary)) g
  intro r hr
  obtain ⟨l,hl,rfl⟩ := hroot hr
  rw [←embedding_equivariant]
  have he : componentConjugateCore l q' = q' := by
    apply Subtype.ext
    change (l : G)*q*(l : G)⁻¹=q
    rw [hfix l hl,mul_inv_cancel_right]
  rw [he]


end SymplecticModel
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
