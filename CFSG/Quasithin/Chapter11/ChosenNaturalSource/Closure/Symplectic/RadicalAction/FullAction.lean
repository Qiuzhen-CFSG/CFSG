module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.PointModel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Actions

/-!
# The faithful symplectic action on the full original module

The action of L on V has kernel O₂(L): the chosen module kills that core,
and the faithful central quotient detects every other element. Factoring
this action through the supplied marking therefore embeds the actual
symplectic group in Aut(V), including the entire central attachment C_V(L).
Its images are exactly the original normalizer-action images.

The point-radical lattice transports through this injection, proving both
strict chief factors and indecomposability on the full original action.
The local and Cartan identifications remain preceding geometric inputs.
The literal root preimage inside L is provided for the independent central
cover calculation and for the closure consumer.
Source: Aschbacher--Smith 11.5.7, assertion (!), printed pp.782--783.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.FullAction
open Subgroup
open scoped IsMulCommutative
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D} (m : MarkedFlag E)

def componentHom : L →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion D.normalizes)

theorem componentHom_ker (E : Geometry D) : (componentHom (D := D)).ker = pCore 2 L := by
  have he : (componentHom (D := D)).ker = (centralizer (V : Set G)).subgroupOf L := by
    ext l
    change V.normalizerMonoidHom (inclusion D.normalizes l) = 1 ↔ _
    rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
    rfl
  rw [he, ← D.chosenAction_ker]
  apply le_antisymm _ D.chosenAction_core
  intro l hl
  apply (QuotientGroup.eq_one_iff l).mp
  apply E.input.faithful
  change D.centralQuotientAction (QuotientGroup.mk' (pCore 2 L) l) = D.centralQuotientAction 1
  rw [map_one, D.centralQuotientAction_mk]
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ v =>
    change Submodule.Quotient.mk (D.chosenAction l v) = Submodule.Quotient.mk v
    rw [show D.chosenAction l = 1 from hl]
    rfl

def modelHom : Sp E.input.field.Carrier →* MulAut V :=
  (QuotientGroup.lift (pCore 2 L) (componentHom (D := D))
    (componentHom_ker E).ge).comp m.action.groupEquiv.symm.toMonoidHom

theorem modelHom_quotientMap (l : L) :
    modelHom m (PointModel.quotientMap m l) = componentHom (D := D) l := by
  change QuotientGroup.lift (pCore 2 L) (componentHom (D := D)) (componentHom_ker E).ge
    (m.action.groupEquiv.symm (m.action.groupEquiv (QuotientGroup.mk' _ l))) = _
  rw [m.action.groupEquiv.symm_apply_apply]
  rfl

theorem modelHom_injective : Function.Injective (modelHom m) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  obtain ⟨l, rfl⟩ := m.action.groupEquiv.surjective.comp
    (QuotientGroup.mk'_surjective (pCore 2 L)) g
  change modelHom m (PointModel.quotientMap m l) = 1 at hg
  rw [modelHom_quotientMap] at hg
  have hl : l ∈ pCore 2 L := (componentHom_ker E).le hg
  change m.action.groupEquiv (QuotientGroup.mk' _ l) = 1
  have hq : QuotientGroup.mk' (pCore 2 L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
  rw [hq, map_one]

theorem image_eq (A : Subgroup G) (hA : A ≤ L) :
    (PointModel.image m A).map (modelHom m) = actionImage (V := V) A := by
  change ((A.subgroupOf L).map _).map _ = _
  rw [map_map]
  have he : (modelHom m).comp (PointModel.quotientMap m) = componentHom (D := D) := by
    apply MonoidHom.ext
    exact modelHom_quotientMap m
  rw [he, componentHom, ← map_map]
  congr 1
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact hl
  · intro hx
    exact ⟨⟨x, hA hx⟩, hx, Subtype.ext rfl⟩

include m in
/-- The bars preserve the actual local two-core, using its two-group kernel. -/
theorem core_image (A : Subgroup G) (hA : A ≤ L) :
    actionImage (V := V) (A.pCoreIn 2) = (actionImage (V := V) A).pCoreIn 2 := by
  rw [← image_eq m _ ((pCoreIn_le 2 A).trans hA), PointModel.image_core m A hA,
    map_pCoreIn_of_injective 2 _ _ (modelHom_injective m), image_eq m A hA]

theorem center_image :
    ((center (PointModel.image m E.L₁)).map (PointModel.image m E.L₁).subtype).map
        (modelHom m) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype := by
  rw [PointRadicalAction.map_embedded_center _ _ (modelHom_injective m),
    image_eq m E.L₁ E.L₁_le]

theorem chief_series (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom) :
    ⊥ < (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype ∧
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype <
        actionImage (V := V) (E.L₁.pCoreIn 2) := by
  have h := PointModel.chief_series m g hlocal
  have hi {A B : Subgroup (Sp E.input.field.Carrier)} (h : A < B) :
      A.map (modelHom m) < B.map (modelHom m) :=
    (map_lt_map_iff_of_injective (modelHom_injective m)).mpr h
  constructor
  · simpa only [Subgroup.map_bot, center_image] using hi h.1
  · simpa only [center_image, image_eq m _ ((pCoreIn_le 2 E.L₁).trans E.L₁_le)] using hi h.2

theorem invariant_lattice (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom)
    (hX : E.X ≤ L) (A : Subgroup (MulAut V))
    (hA : A ≤ actionImage (V := V) (E.L₁.pCoreIn 2))
    (hn : actionImage (V := V) (E.L₁ ⊔ E.X) ≤ normalizer (A : Set (MulAut V))) :
    A = ⊥ ∨ A = (center (actionImage (V := V) E.L₁)).map
      (actionImage (V := V) E.L₁).subtype ∨
      A = actionImage (V := V) (E.L₁.pCoreIn 2) := by
  have hle : A.comap (modelHom m) ≤ PointModel.image m (E.L₁.pCoreIn 2) := by
    rw [← image_eq m _ ((pCoreIn_le 2 E.L₁).trans E.L₁_le)] at hA
    exact (comap_mono hA).trans_eq (comap_map_eq_self_of_injective (modelHom_injective m) _)
  have hn' : PointModel.image m (E.L₁ ⊔ E.X) ≤ normalizer
      (A.comap (modelHom m) : Set (Sp E.input.field.Carrier)) := by
    apply le_trans _ (A.le_normalizer_comap (modelHom m))
    apply map_le_iff_le_comap.mp
    rw [image_eq m _ (sup_le E.L₁_le hX)]
    exact hn
  have hrange : A ≤ (modelHom m).range := by
    rw [← image_eq m _ ((pCoreIn_le 2 E.L₁).trans E.L₁_le)] at hA
    exact hA.trans (map_le_range _ _)
  rcases PointModel.image_invariant_lattice m g hlocal hcartan
    (A.comap (modelHom m)) hle hn' with h | h | h
  · left
    have hh := congrArg (map (modelHom m)) h
    simpa only [map_comap_eq_self hrange, Subgroup.map_bot] using hh
  · right; left
    have hh := congrArg (map (modelHom m)) h
    simpa only [map_comap_eq_self hrange, center_image] using hh
  · right; right
    have hh := congrArg (map (modelHom m)) h
    simpa only [map_comap_eq_self hrange,
      image_eq m _ ((pCoreIn_le 2 E.L₁).trans E.L₁_le)] using hh

/-- The two proper terms of the chief series are invariant under the same
original local--Cartan image used by the lattice theorem. -/
theorem normalizes_center_and_core (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom) (hX : E.X ≤ L) :
    actionImage (V := V) (E.L₁ ⊔ E.X) ≤ normalizer
      ((center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype :
        Set (MulAut V)) ∧
    actionImage (V := V) (E.L₁ ⊔ E.X) ≤ normalizer
      (actionImage (V := V) (E.L₁.pCoreIn 2) : Set (MulAut V)) := by
  obtain ⟨hz,hq⟩ := PointModel.normalizes_center_and_core m g hlocal hcartan
  have hz' := (map_mono (f := modelHom m) hz).trans (le_normalizer_map _)
  have hq' := (map_mono (f := modelHom m) hq).trans (le_normalizer_map _)
  rw [image_eq m _ (sup_le E.L₁_le hX), center_image] at hz'
  rw [image_eq m _ (sup_le E.L₁_le hX),
    image_eq m _ ((pCoreIn_le 2 E.L₁).trans E.L₁_le)] at hq'
  exact ⟨hz',hq'⟩

/-- The local center acts as the literal marked long root on the full V. -/
theorem center_eq_marked_root (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom) :
    (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype =
      ((RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom).map (modelHom m) := by
  rw [← center_image, PointModel.center_identification m g hlocal]

/-- The literal original preimage of the local root image inside L. -/
def rootPreimage : Subgroup G :=
  (((center (actionImage (V := V) E.L₁)).map
    (actionImage (V := V) E.L₁).subtype).comap (componentHom (D := D))).map L.subtype

theorem rootPreimage_le : rootPreimage (E := E) ≤ L := map_subtype_le _

include m in
theorem rootPreimage_image :
    actionImage (V := V) (rootPreimage (E := E)) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype := by
  rw [← image_eq m _ rootPreimage_le]
  change ((((rootPreimage (E := E)).subgroupOf L).map (PointModel.quotientMap m)).map
    (modelHom m)) = _
  rw [map_map]
  have he : (modelHom m).comp (PointModel.quotientMap m) = componentHom (D := D) := by
    apply MonoidHom.ext
    exact modelHom_quotientMap m
  rw [he]
  simp only [rootPreimage, subgroupOf, comap_map_eq_self_of_injective L.subtype_injective]
  apply map_comap_eq_self
  apply (map_subtype_le _).trans
  rw [← image_eq m E.L₁ E.L₁_le]
  change ((E.L₁.subgroupOf L).map (PointModel.quotientMap m)).map (modelHom m) ≤ _
  rw [map_map, he]
  exact map_le_range _ _

theorem core_elementaryAbelian (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom) :
    IsElementaryAbelian 2 (actionImage (V := V) (E.L₁.pCoreIn 2)) := by
  rw [← image_eq m _ ((pCoreIn_le 2 E.L₁).trans E.L₁_le)]
  let := PointModel.core_elementaryAbelian m g hlocal
  exact IsElementaryAbelian.map (modelHom m)

theorem indecomposable (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom)
    (hX : E.X ≤ L) (A B : Subgroup (MulAut V))
    (hA : actionImage (V := V) (E.L₁ ⊔ E.X) ≤ normalizer (A : Set (MulAut V)))
    (hB : actionImage (V := V) (E.L₁ ⊔ E.X) ≤ normalizer (B : Set (MulAut V)))
    (hjoin : A ⊔ B = actionImage (V := V) (E.L₁.pCoreIn 2)) (hmeet : A ⊓ B = ⊥) :
    A = ⊥ ∨ B = ⊥ := by
  by_cases ha : A = ⊥
  · exact Or.inl ha
  by_cases hb : B = ⊥
  · exact Or.inr hb
  have hchain := chief_series m g hlocal
  have hc (C : Subgroup (MulAut V))
      (hC : C ≤ actionImage (V := V) (E.L₁.pCoreIn 2))
      (hn : actionImage (V := V) (E.L₁ ⊔ E.X) ≤ normalizer (C : Set (MulAut V)))
      (hne : C ≠ ⊥) :
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype ≤ C := by
    rcases invariant_lattice m g hlocal hcartan hX C hC hn with h | h | h
    · exact (hne h).elim
    · exact h.ge
    · exact hchain.2.le.trans h.ge
  have hz := le_inf (hc A (le_sup_left.trans hjoin.le) hA ha)
    (hc B (le_sup_right.trans hjoin.le) hB hb)
  rw [hmeet] at hz
  exact (hchain.1.not_ge hz).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.FullAction
