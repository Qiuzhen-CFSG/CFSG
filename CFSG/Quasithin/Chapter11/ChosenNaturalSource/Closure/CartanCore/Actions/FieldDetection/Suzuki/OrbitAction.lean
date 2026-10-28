module

public import Theory.GroupTheory.PCoreQuotientPerfectProjection
public import Theory.SpecificGroups.Suzuki.CyclicOuter
public import Theory.GroupTheory.ConjugateSpanSylow
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki.FixedAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki.Diagonal

/-!
# The Suzuki orbit coordinates and the original field actor

The orbit of a relative C-component is perfect and normalizes that component.
The Suzuki outer group is cyclic, so the orbit action on the centerless
component quotient is inner. Its unique inner representative constructs an
equivariant projection retaining the literal I/O₂(I) quotient. Sylow conjugacy
aligns the image of T∩⟨Iᵀ⟩ with the standard root subgroup.

The one-or-two-component theorem makes the orbit normal in G₁. Its Sylow
intersection is R₁∩⟨Iᵀ⟩, hence X-invariant. The original quotient mover then
has a nontrivial field factor and an inner Borel factor. The previously proved
diagonal normalizer lifts finish BorelMovement in both orbit cases. No field
actor, orbit coordinates, or normalizer-lifting hypothesis remains.

The genuine preceding flag/Cartan geometry stays explicit, for discharge by
qt-d-1222-natural-closure and its earlier-input owners.
Source: Aschbacher--Smith 11.5.6(3), printed pp.780--781.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.SuzukiBorelFieldQuotient
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection.Suzuki
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
variable {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- Every conjugate C-component belongs to the layer normalizing I. -/
theorem component_orbit_normalizes_component
    (hT : (T : Subgroup G) ≤ E.G₁) {I : Subgroup G} (hI : Source.ComponentIn E.Y I) :
    orbit T I ≤ normalizer (I : Set G) := by
  let A := I.subgroupOf E.G₁
  have hA : A.IsCComponent := E.component_in_point_normalizer hI
  have hIH : I ≤ E.G₁ := hI.1.trans E.Y_le_G₁
  apply (closure_le _).mpr
  rintro x ⟨t, ht, i, hi, rfl⟩
  let tH : E.G₁ := ⟨t, hT ht⟩
  have hn := (le_cComponentLayer (hA.map_equiv (MulAut.conj tH))).trans
    (cComponentLayer_le_normalizer hA)
  have hh : tH * (⟨i, hIH hi⟩ : E.G₁) * tH⁻¹ ∈ normalizer (A : Set E.G₁) :=
    hn (mem_map_of_mem (MulAut.conj tH).toMonoidHom hi)
  rw [← subgroupOf_normalizer_eq hIH] at hh
  exact hh

/-- The source one-or-two-component bound makes the Sylow orbit normal in G₁. -/
theorem component_orbit_normalized
    (hp : E.point ≠ ⊥) (hT : (T : Subgroup G) ≤ E.G₁)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I) :
    E.G₁ ≤ normalizer (orbit T I : Set G) := by
  let A := I.subgroupOf E.G₁
  let S := T.subtype hT
  let J := conjugateSpanBy A (S : Subgroup E.G₁)
  have hn : J.Normal := conjugateSpanBy_sylow_normal A S
    (E.component_normal_or_index_two hp hI)
  have he : J.map E.G₁.subtype = orbit T I := by
    rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le (hI.1.trans E.Y_le_G₁)]
    change conjugateSpanBy I (((T : Subgroup G).subgroupOf E.G₁).map E.G₁.subtype) = _
    rw [map_subgroupOf_eq_of_le hT]
    rfl
  apply le_normalizer_iff.mpr
  intro x hx j hj
  rw [← he] at hj ⊢
  obtain ⟨a, ha, rfl⟩ := hj
  exact mem_map_of_mem E.G₁.subtype (hn.conj_mem a ha ⟨x,hx⟩)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.Suzuki
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
variable {L V : Subgroup G} {D : ChosenModule T L V} {E : Geometry D}
variable {I : Subgroup G} {m : ℕ}

/-- Construct the actual quotient projection and Sylow marking for either orbit. -/
theorem exists_equivariant_orbitCoordinates
    (hT : (T : Subgroup G) ≤ E.G₁) (hI : Source.ComponentIn E.Y I)
    (hm : 0 < m) (e : (I ⧸ pCore 2 I) ≃* SuzukiMatrixGroup m) :
    ∃ c : OrbitCoordinates T I m,
      ∀ (x : normalizer (orbit T I : Set G)) (hx : (x : G) ∈ normalizer (I : Set G))
        (j : orbit T I),
        c.quotient ((orbit T I).normalizerMonoidHom x j) =
          (MulAut.congr c.component (coreQuotientAction I ⟨x,hx⟩)) (c.quotient j) := by
  have hIH : I ≤ E.G₁ := hI.1.trans E.Y_le_G₁
  let : Group.IsPerfect (I.subgroupOf E.G₁) := (E.component_in_point_normalizer hI).perfect
  let : Group.IsPerfect I := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hIH).toMonoidHom) (subgroupOfEquivOfLe hIH).surjective
  let : Group.IsPerfect (orbit T I) := conjugateSpanBy_isPerfect I (T : Subgroup G)
  let : IsCyclic (MulAut.Outer (SuzukiMatrixGroup m)) := suzuki_outer_isCyclic m hm
  let : Group.IsSolvable (MulAut.Outer (I ⧸ pCore 2 I)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (MulAut.outerCongr e).toMonoidHom) (MulAut.outerCongr e).injective
  have hz : center (I ⧸ pCore 2 I) = ⊥ := by
    have hmodel : IsSimpleBenderGroup (SuzukiMatrixGroup m) :=
      .isSuzuki ⟨m,hm,⟨MulEquiv.refl _⟩⟩
    let := hmodel.isSimple
    let : IsSimpleGroup (I ⧸ pCore 2 I) := e.isSimpleGroup
    rcases (inferInstance : (center (I ⧸ pCore 2 I)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hh : IsMulCommutative (I ⧸ pCore 2 I) := center_eq_top_iff.mp h
      let := hh
      exact (hmodel.not_commutative (fun x y => by
        obtain ⟨a,rfl⟩ := e.surjective x
        obtain ⟨b,rfl⟩ := e.surjective y
        rw [← map_mul, ← map_mul]
        exact congrArg e (mul_comm a b))).elim
  have hIO : I ≤ orbit T I := le_conjugateSpanBy I (T : Subgroup G)
  obtain ⟨f,hf,hfe⟩ := exists_perfect_coreQuotient_projection hIO
    (E.component_orbit_normalizes_component hT hI) hz
  let q := e.toMonoidHom.comp f
  have hqsurj : Function.Surjective q := by
    intro z
    obtain ⟨a,rfl⟩ := e.surjective z
    obtain ⟨i,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 I) a
    exact ⟨inclusion hIO i, congrArg e (hf i)⟩
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T (orbit T I)
    (le_normalizer_conjugateSpanBy I (T : Subgroup G))
  obtain ⟨U,hU⟩ := suzukiRootSubgroup_isSylow m hm
  let Q := P.mapSurjective hqsurj
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) Q U
  let e' := e.trans (MulAut.conj g)
  let q' := (MulAut.conj g).toMonoidHom.comp q
  have hs : ((T : Subgroup G).subgroupOf (orbit T I)).map q' = SuzukiRootSubgroup m := by
    have hh := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul,hU] at hh
    change ((P : Subgroup (orbit T I)).map q).map (MulAut.conj g).toMonoidHom = _ at hh
    simpa only [q', ← map_map, hP] using hh
  let c : OrbitCoordinates T I m := {
    component := e'
    quotient := q'
    restriction := fun i => congrArg (fun z => MulAut.conj g (e z)) (hf i)
    sylow_image := hs }
  refine ⟨c, ?_⟩
  intro x hx j
  change e' (f ((orbit T I).normalizerMonoidHom x j)) =
    e' (coreQuotientAction I ⟨x,hx⟩ (e'.symm (e' (f j))))
  rw [e'.symm_apply_apply, hfe]
  rfl

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.Suzuki

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.Suzuki
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
variable {L V : Subgroup G} {D : ChosenModule T L V} {E : Geometry D}
variable {I : Subgroup G} {m : ℕ}

/-- An equivariant orbit marking turns the original coprime mover into a field actor. -/
theorem OrbitCoordinates.exists_fieldAction_of_equivariant (c : OrbitCoordinates T I m)
    (hm : 0 < m) (hc : Nat.Coprime (Nat.card E.X) (Nat.card I))
    (x : normalizer (orbit T I : Set G)) (hx : (x : G) ∈ E.X)
    (hxI : (x : G) ∈ normalizer (I : Set G))
    (hxs : (x : G) ∈ normalizer (((T : Subgroup G) ⊓ orbit T I : Subgroup G) : Set G))
    (hne : coreQuotientAction I ⟨x,hxI⟩ ≠ 1)
    (heq : ∀ j : orbit T I, c.quotient ((orbit T I).normalizerMonoidHom x j) =
      (MulAut.congr c.component (coreQuotientAction I ⟨x,hxI⟩)) (c.quotient j)) :
    Nonempty (FieldAction E c hm) := by
  have hxb : (x : G) ∈ normalizer (borel T I : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨x.property, (normalizer _).le_normalizer hxs⟩
  let α := MulAut.congr c.component (coreQuotientAction I ⟨x,hxI⟩)
  have hroot : (SuzukiRootSubgroup m).map α.toMonoidHom = SuzukiRootSubgroup m := by
    rw [← c.sylow_image]
    have he : α.toMonoidHom.comp c.quotient =
        c.quotient.comp ((orbit T I).normalizerMonoidHom x).toMonoidHom := by
      apply MonoidHom.ext
      intro j
      exact (heq j).symm
    rw [map_map, he, ← map_map]
    congr 1
    ext i
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact ((mem_normalizer_iff.mp hxs j).mp ⟨hj,j.property⟩).1
    · intro hi
      refine ⟨((orbit T I).normalizerMonoidHom x).symm i, ?_,
        ((orbit T I).normalizerMonoidHom x).apply_symm_apply i⟩
      exact ((mem_normalizer_iff.mp ((normalizer _).inv_mem hxs) i).mp
        ⟨hi,i.property⟩).1
  have hcop : Nat.Coprime (orderOf α) (Nat.card (SuzukiMatrixGroup m)) := by
    apply hc.of_dvd
    · exact ((orderOf_map_dvd (MulAut.congr c.component).toMonoidHom _).trans
        (orderOf_map_dvd (coreQuotientAction I) ⟨x,hxI⟩)).trans (by
          rw [← Subgroup.orderOf_coe (⟨x,hxI⟩ : normalizer (I : Set G))]
          exact E.X.orderOf_dvd_natCard hx)
    · exact card_dvd_of_surjective
        (c.component.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I)))
        (c.component.surjective.comp (QuotientGroup.mk'_surjective _))
  have hα : α ≠ 1 := by
    intro h
    apply hne
    exact (MulAut.congr c.component).injective (h.trans (map_one _).symm)
  obtain ⟨b,σ,hσ,ha⟩ := exists_borel_inner_field_of_coprime m hm α hα hcop hroot
  refine ⟨⟨⟨x,hxb⟩,hx,b,σ,hσ,?_⟩⟩
  intro y
  apply Subtype.ext
  rw [borelActor_apply, ← ha]
  exact heq ⟨y,y.property.1⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.Suzuki

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection.Suzuki
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
variable {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- Suzuki field detection with all coordinate, actor and normalizer-lift premises discharged. -/
theorem suzuki_borel_movement_of_quotient
    (hp : E.point ≠ ⊥) (hT : (T : Subgroup G) ≤ E.G₁)
    (hX : E.X ≤ E.G₁) (ho : Odd (Nat.card E.X))
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (eX : E.X ≃* (E.input.field.Carrierˣ × E.input.field.Carrierˣ))
    (hc : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1))
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    {m : ℕ} (hm : 0 < m) (e : (I ⧸ pCore 2 I) ≃* SuzukiMatrixGroup m)
    (hmoved : ¬ ⁅I, E.X⁆ ≤ E.Y.pCoreIn 2) : E.BorelMovement := by
  obtain ⟨c,he⟩ := exists_equivariant_orbitCoordinates hT hI hm e
  have hn := E.component_orbit_normalized hp hT hI
  have hJY : orbit T I ≤ E.Y := conjugateSpanBy_le hI.1 (hT.trans E.G₁_normalizes_Y)
  have hRT : E.R₁ ≤ (T : Subgroup G) := by
    simpa only [R₁, Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (E.L₁ ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hS : (T : Subgroup G) ⊓ orbit T I = E.R₁ ⊓ orbit T I := by
    apply le_antisymm
    · exact le_inf (fun _ h => E.sylow_inter_Y_le_R₁ hT ⟨h.1,hJY h.2⟩) inf_le_right
    · exact inf_le_inf_right _ hRT
  have hXS : E.X ≤ normalizer (((T : Subgroup G) ⊓ orbit T I : Subgroup G) : Set G) := by
    rw [hS]
    exact (le_inf hXR (hX.trans hn)).trans inf_normalizer_le_normalizer_inf
  obtain ⟨x,hx,hne⟩ := E.exists_component_quotient_mover hp hX ho hI hmoved
  let xJ : normalizer (orbit T I : Set G) := ⟨x,hn (hX hx)⟩
  obtain ⟨a⟩ := c.exists_fieldAction_of_equivariant hm
    (E.cartan_coprime_component_of_split_marking eX hc hI) xJ hx x.property
    (hXS hx) hne (he xJ x.property)
  exact E.suzuki_borel_movement_of_field_action hp hT hI hm c a

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
