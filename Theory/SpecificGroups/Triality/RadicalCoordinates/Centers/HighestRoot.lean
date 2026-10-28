module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.FixedPoints

/-!
# The highest-root subgroup in the genuine triality carrier

The canonical curve at position 11 is the highest positive D₄ root. Height
additivity and the proved non-sum commutation relations show that it commutes
with the positive subgroup. Graph-field fixedness restricts its parameter to
the actual fixed field, and the elementary central-kernel theorem makes its
descended parametrization faithful. Thus this subgroup has order q and lies
in the embedded centers of both the arms root radical and the unipotent group.
The reverse center inclusions are not asserted in this module.

Source: GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith F.1.11–12 (`refs/quasithin.pdf`, printed pp.262–264).
-/

@[expose] public section

noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.PositiveCoordinates
namespace Triality.Standard.RadicalCoordinates.Centers
open Parabolics

def highestCoordinates (P : Parameters) (t : ExtensionField P) : Coordinates P :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, t]

theorem orderedProduct_highestCoordinates (P : Parameters) (t : ExtensionField P) :
    orderedProduct P (highestCoordinates P t) = curve P 11 t := by
  simp [orderedProduct, highestCoordinates, List.ofFn_succ]

theorem highestCurve_injective (P : Parameters) : Function.Injective (curve P 11) := by
  intro s t h
  have he : highestCoordinates P s = highestCoordinates P t :=
    orderedProduct_injective P (by simpa only [orderedProduct_highestCoordinates] using h)
  exact congrFun he 11

def splitHighestHom (P : Parameters) : Multiplicative (ExtensionField P) →* SplitGroup P where
  toFun t := curve P 11 t.toAdd
  map_one' := curve_zero P 11
  map_mul' s t := curve_add P 11 s.toAdd t.toAdd

def splitHighestRoot (P : Parameters) : Subgroup (SplitGroup P) := (splitHighestHom P).range

def highestRoot (P : Parameters) : Subgroup (Carrier P) :=
  descendSubgroup P (splitHighestRoot P)

theorem mem_splitHighestRoot (P : Parameters) (g : SplitGroup P) :
    g ∈ splitHighestRoot P ↔ ∃ t : ExtensionField P, curve P 11 t = g := Iff.rfl

theorem splitHighestRoot_le_rootSubgroup (P : Parameters) (a : Node) :
    splitHighestRoot P ≤ rootSubgroup P a := by
  rintro g ⟨t, rfl⟩
  exact curve_mem_rootSubgroup P a 11 (by cases a <;> decide) t.toAdd

theorem highestRoot_le_descendedRootSubgroup (P : Parameters) (a : Node) :
    highestRoot P ≤ descendSubgroup P (rootSubgroup P a) :=
  descendSubgroup_mono P (splitHighestRoot_le_rootSubgroup P a)

theorem highestRoot_le_unipotent (P : Parameters) (hp : P.prime = 2) :
    highestRoot P ≤ unipotent P :=
  descendSubgroup_mono P ((splitHighestRoot_le_rootSubgroup P .arms).trans
    (rootSubgroup_le_positiveSubgroup P hp .arms))

theorem highestCurve_commute (P : Parameters) (i : Fin 12) (s t : ExtensionField P) :
    Commute (curve P 11 s) (curve P i t) := by
  by_cases hi : (11 : Fin 12) = i
  · subst i
    change _ * _ = _ * _
    rw [← curve_add, ← curve_add, add_comm s t]
  · apply nonsumCommute_parameters P 11 i hi
    rintro ⟨k, hk⟩
    have h := collectionHeight_add hk
    have hpos := collectionHeight_pos i
    have hlt := collectionHeight_lt_six k
    change collectionHeight k = 5 + collectionHeight i at h
    omega

theorem positiveSubgroup_le_centralizer_highestCurve (P : Parameters) (t : ExtensionField P) :
    positiveSubgroup P ≤ Subgroup.centralizer {curve P 11 t} := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, s, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  have hx' : x = curve P 11 t := Set.mem_singleton_iff.mp hx
  subst x
  simpa only [curve_simple] using (highestCurve_commute P (simplePosition i) t s).eq

theorem graphField_highestCurve (P : Parameters) (hp : P.prime = 2) (t : ExtensionField P) :
    graphFieldAutomorphism P (curve P 11 t) = curve P 11 (fieldFrobenius P t) := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  exact graphField_curve_binary n hn 11 t

def elementaryHighestHom (P : Parameters) (hp : P.prime = 2) :
    Multiplicative (fixedField P) →* ElementaryGroup P where
  toFun t :=
    ⟨⟨curve P 11 t.toAdd.val, by
        rw [mem_fixedSubgroup, graphField_highestCurve P hp]
        exact congrArg (curve P 11) (show fieldFrobenius P t.toAdd.val = t.toAdd.val from
          t.toAdd.property)⟩,
      fixedRootSubgroup_le_elementary P hp .arms
        (curve_mem_rootSubgroup P .arms 11 (by decide) t.toAdd.val)⟩
  map_one' := Subtype.ext (Subtype.ext (curve_zero P 11))
  map_mul' s t := Subtype.ext (Subtype.ext (curve_add P 11 s.toAdd.val t.toAdd.val))

@[simp] theorem elementaryHighestHom_val (P : Parameters) (hp : P.prime = 2)
    (t : Multiplicative (fixedField P)) :
    elementaryInclusion P (elementaryHighestHom P hp t) = curve P 11 t.toAdd.val := rfl

def highestHom (P : Parameters) (hp : P.prime = 2) :
    Multiplicative (fixedField P) →* Carrier P :=
  (toCarrier P).comp (elementaryHighestHom P hp)

theorem highestHom_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (highestHom P hp) := by
  intro s t h
  have he := ElementaryCentralKernel.toCarrier_injective P hp h
  have hf := congrArg (elementaryInclusion P) he
  exact congrArg Multiplicative.ofAdd (Subtype.ext (highestCurve_injective P hf))

theorem highestHom_range (P : Parameters) (hp : P.prime = 2) :
    (highestHom P hp).range = highestRoot P := by
  apply le_antisymm
  · rintro g ⟨t, rfl⟩
    exact ⟨elementaryHighestHom P hp t, ⟨Multiplicative.ofAdd t.toAdd.val, rfl⟩, rfl⟩
  · intro g hg
    change ∃ e : ElementaryGroup P, elementaryInclusion P e ∈ splitHighestRoot P ∧
      toCarrier P e = g at hg
    obtain ⟨e, he, rfl⟩ := hg
    change ∃ t : ExtensionField P, curve P 11 t = elementaryInclusion P e at he
    obtain ⟨t, ht⟩ := he
    have htfix : fieldFrobenius P t = t := by
      apply highestCurve_injective P
      rw [← graphField_highestCurve P hp, ht]
      exact e.val.property
    refine ⟨Multiplicative.ofAdd ⟨t, htfix⟩, ?_⟩
    apply congrArg (toCarrier P)
    exact Subtype.ext (Subtype.ext ht)

def highestRootEquiv (P : Parameters) (hp : P.prime = 2) :
    Multiplicative (fixedField P) ≃* highestRoot P :=
  (MonoidHom.ofInjective (highestHom_injective P hp)).trans
    (MulEquiv.subgroupCongr (highestHom_range P hp))

theorem card_highestRoot (P : Parameters) (hp : P.prime = 2) :
    Nat.card (highestRoot P) = P.q := by
  rw [← Nat.card_congr (highestRootEquiv P hp).toEquiv]
  exact card_fixedField P

private theorem embedded_center_of_commute {G : Type*} [Group G]
    (Z H : Subgroup G) (hlo : Z ≤ H)
    (hcomm : ∀ z ∈ Z, ∀ x ∈ H, x * z = z * x) :
    Z ≤ (Subgroup.center H).map H.subtype := by
  intro z hz
  refine ⟨⟨z, hlo hz⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
  intro x
  exact Subtype.ext (hcomm z hz x.val x.property)

private theorem commute_map_comap {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : A →* C) (hf : Function.Injective f)
    (Z H : Subgroup B) (hcomm : ∀ z ∈ Z, ∀ x ∈ H, x * z = z * x) :
    ∀ z ∈ (Z.comap f).map g, ∀ x ∈ (H.comap f).map g, x * z = z * x := by
  rintro _ ⟨z, hz, rfl⟩ _ ⟨x, hx, rfl⟩
  rw [← map_mul, ← map_mul]
  apply congrArg g
  apply hf
  simpa only [map_mul] using hcomm (f z) hz (f x) hx

theorem highestRoot_le_embeddedCenter (P : Parameters)
    (H : Subgroup (Carrier P)) (hlo : highestRoot P ≤ H) (hhi : H ≤ unipotent P) :
    highestRoot P ≤ (Subgroup.center H).map H.subtype := by
  apply embedded_center_of_commute _ _ hlo
  have hc : ∀ z ∈ splitHighestRoot P, ∀ x ∈ positiveSubgroup P, x * z = z * x := by
    rintro z ⟨t, rfl⟩ x hx
    exact ((Subgroup.mem_centralizer_iff.mp
      (positiveSubgroup_le_centralizer_highestCurve P t.toAdd hx))
        _ (Set.mem_singleton _)).symm
  intro z hz x hx
  exact commute_map_comap (elementaryInclusion P) (toCarrier P)
    (fun _ _ h => Subtype.ext (Subtype.ext h)) _ _ hc z hz x (hhi hx)

theorem highestRoot_le_center_unipotent (P : Parameters) (hp : P.prime = 2) :
    highestRoot P ≤ (Subgroup.center (unipotent P)).map (unipotent P).subtype :=
  highestRoot_le_embeddedCenter P _ (highestRoot_le_unipotent P hp) le_rfl

theorem highestRoot_le_center_arms (P : Parameters) (hp : P.prime = 2) :
    highestRoot P ≤ (Subgroup.center (descendSubgroup P (rootSubgroup P .arms))).map
      (descendSubgroup P (rootSubgroup P .arms)).subtype :=
  highestRoot_le_embeddedCenter P _ (highestRoot_le_descendedRootSubgroup P .arms)
    (descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .arms))

end Triality.Standard.RadicalCoordinates.Centers
