module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.ActorGeometry

/-!
# The actual action and centralizers used by the four-family calculation

Restriction to `S` has kernel exactly the embedded core `Q`. Equivariance
identifies the fixed vectors of every action image with the centralizer in
`U`. The remaining transport to `Q = UD` can therefore be stated as an
explicit cardinal identity, together with the single-actor fixed test.

`FixedProfile` is a conditional interface for these two group-action facts;
it asserts no maximum order or elementary-family enumeration.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.21 and
the proof of C.5.6, printed pp.82–83 and 157–158.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
open Subgroup Representation.BinaryOffender
universe u

/-- Fixed-space transport needed by the finite-group lifting argument.
The index is calculated from the actual sixteen-element permutation module. -/
structure FixedProfile {T : Type*} [Group T] (σ : T →* Perm) (V : Subgroup T) : Prop where
  card_fixed : ∀ B : Subgroup T,
    Nat.card (V ⊓ centralizer (B : Set T) : Subgroup T) * fixedIndex (B.map σ) = Nat.card V
  full_detect : ∀ (B : Subgroup T) (b : T), b ∈ B → B.map σ = ChapterB.Offenders.D 5 →
    σ b = doubleSwap →
    V ⊓ centralizer (B : Set T) = V ⊓ centralizer ({b} : Set T)

variable {G : Type u} [Group G] {R L : Subgroup G}

/-- The coordinate action restricted to the actual Baumann subgroup. -/
noncomputable def restrictedAction (c : ActionCoordinates R L) : S R →* Perm :=
  c.action.comp (inclusion (show S R ≤ R from inf_le_left))

/-- The actual core, as a subgroup of the group on which we enumerate. -/
noncomputable def coreIn (R L : Subgroup G) : Subgroup (S R) := (Q R L).subgroupOf (S R)

/-- The second specified member, in the same intrinsic group. -/
noncomputable def oppositeIn (R L : Subgroup G) (x : G) : Subgroup (S R) :=
  (opposite R L x).subgroupOf (S R)

theorem restrictedAction_image (c : ActionCoordinates R L) {B : Subgroup G}
    (hB : B ≤ S R) :
    (B.subgroupOf (S R)).map (restrictedAction c) = actionImage c.action B := by
  ext p
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b.val, (show S R ≤ R from inf_le_left) b.property⟩, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b.val, hB hb⟩, hb, rfl⟩

theorem restrictedAction_range (c : ActionCoordinates R L) :
    (restrictedAction c).range = ChapterB.Offenders.D 5 := by
  rw [← c.baumann_image, ← restrictedAction_image c (le_refl (S R)), subgroupOf_self]
  exact (restrictedAction c).range_eq_map

theorem restrictedAction_ker {H : Subgroup G} (c : ActionCoordinates R L)
    (hb : BaumannStructure H R L) : (restrictedAction c).ker = coreIn R L := by
  ext s
  change c.action ⟨s.val, (show S R ≤ R from inf_le_left) s.property⟩ = 1 ↔ s.val ∈ Q R L
  rw [c.kernel, hb.core_eq]
  exact ⟨fun hs => ⟨s.property, hs⟩, fun hs => hs.2⟩

theorem opposite_le_S {x : G} (hp : Factorization R L x) : opposite R L x ≤ S R := by
  exact sup_le (le_sup_left.trans hp.span.ge) inf_le_left

theorem oppositeIn_image {H : Subgroup G} {x : G} (c : ActionCoordinates R L)
    (hb : BaumannStructure H R L) (hp : Factorization R L x) :
    (oppositeIn R L x).map (restrictedAction c) = ChapterB.Offenders.D 5 := by
  rw [oppositeIn, restrictedAction_image c (opposite_le_S hp), c.opposite_image hb hp]

/-- The Frattini-zero calculation supplies both intrinsic elementary groups. -/
theorem intrinsic_elementary [Finite G] {K : GroupClass.{u}}
    {A H : Subgroup G} {x : G} (h : Configuration K A H R L)
    (hb : BaumannStructure H R L) (hp : Factorization R L x) (hf : F R L = ⊥) :
    IsElementaryAbelian 2 (coreIn R L) ∧ IsElementaryAbelian 2 (oppositeIn R L x) := by
  obtain ⟨hQ, hW⟩ := elementary_candidates_of_frattini_eq_bot h hb hp hf
  let : IsElementaryAbelian 2 (Q R L) := hQ
  let : IsElementaryAbelian 2 (opposite R L x) := hW
  exact ⟨IsElementaryAbelian.subgroupOf (hb.core_eq ▸ inf_le_left),
    IsElementaryAbelian.subgroupOf (opposite_le_S hp)⟩

/-- The factor `D` centralizes all of `S`, using elementary abelianness of `Q`
and the separately supplied centralization of the conjugate module. -/
theorem D_centralizes_S [Finite G] {K : GroupClass.{u}}
    {A H : Subgroup G} {x : G} (h : Configuration K A H R L)
    (hb : BaumannStructure H R L) (hp : Factorization R L x) (hf : F R L = ⊥) :
    D R L ≤ centralizer (S R : Set G) := by
  let : IsElementaryAbelian 2 (Q R L) :=
    (elementary_candidates_of_frattini_eq_bot h hb hp hf).1
  have hQQ : Q R L ≤ centralizer (Q R L : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hDQ : D R L ≤ centralizer (Q R L : Set G) :=
    (hp.core ▸ (le_sup_right : D R L ≤ U L ⊔ D R L)).trans hQQ
  apply le_centralizer_iff.mpr
  rw [hp.span]
  exact sup_le (le_centralizer_iff.mp hp.centralizes) (le_centralizer_iff.mp hDQ)

/-- No ambient centralizer is substituted for a relative one: this equality
compares a vector with its image in the given subgroup of `G`. -/
theorem moduleMap_mem_centralizer_iff (c : ActionCoordinates R L)
    {B : Subgroup G} (hB : B ≤ R) (v : Multiplicative Vector) :
    c.moduleMap v ∈ centralizer (B : Set G) ↔
      v.toAdd ∈ fixedSpace (BinaryPermutation.coreRepresentation (Fin 5)) (actionImage c.action B) := by
  rw [mem_centralizer_iff, mem_fixedSpace_iff]
  constructor
  · intro hv p hp
    obtain ⟨r, hr, rfl⟩ := hp
    apply (Multiplicative.ofAdd.injective)
    apply c.moduleMap_injective
    rw [← c.equivariant]
    exact mul_inv_eq_iff_eq_mul.mpr (hv r.val hr)
  · intro hv b hb
    let r : R := ⟨b, hB hb⟩
    have he := congrArg (fun z : Vector => c.moduleMap (Multiplicative.ofAdd z))
      (hv (c.action r) (mem_map_of_mem c.action hb))
    rw [← c.equivariant] at he
    exact mul_inv_eq_iff_eq_mul.mp he

/-- The exact cardinal transport for centralizers in `U`. -/
theorem module_centralizer_card (c : ActionCoordinates R L)
    {B : Subgroup G} (hB : B ≤ R) :
    Nat.card (U L ⊓ centralizer (B : Set G) : Subgroup G) =
      Nat.card (fixedSpace (BinaryPermutation.coreRepresentation (Fin 5)) (actionImage c.action B)) := by
  let f : fixedSpace (BinaryPermutation.coreRepresentation (Fin 5)) (actionImage c.action B) →
      (U L ⊓ centralizer (B : Set G) : Subgroup G) := fun v =>
    ⟨c.moduleMap (Multiplicative.ofAdd v.val),
      ⟨c.moduleMap_range ▸ (show c.moduleMap (Multiplicative.ofAdd v.val) ∈ c.moduleMap.range from ⟨_, rfl⟩),
        (moduleMap_mem_centralizer_iff c hB _).mpr v.property⟩⟩
  have hfi : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    exact Multiplicative.ofAdd.injective (c.moduleMap_injective (congrArg Subtype.val he))
  have hfs : Function.Surjective f := by
    rintro ⟨g, hgU, hgC⟩
    rw [← c.moduleMap_range] at hgU
    obtain ⟨v, rfl⟩ := hgU
    exact ⟨⟨v.toAdd, (moduleMap_mem_centralizer_iff c hB v).mp hgC⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hfi, hfs⟩)).symm

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
end
