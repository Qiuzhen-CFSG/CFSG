module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.ModelFlag
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Normalization

/-!
# The marked Sp4 flag in the original chosen module

Map the actual Sylow intersection T intersect L onto the symplectic group and
conjugate its Sylow to the standard one. The fixed-space filtration characterizes
the pulled-back flag intrinsically by commutators modulo its preceding step.
Because T normalizes L and V, it preserves that filtration even when its quotient
action is only binary linear. Model uniqueness gives uniqueness already under
T intersect L and discharges the Cartan normalization input.

Source: Aschbacher--Smith, 11.0.2 and opening section 11.1, pp.759--761.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField}
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))

/-- The actual image of T intersect L is a conjugate of the standard Sylow. -/
theorem exists_alignment : ∃ g : Sp F.Carrier,
    ((T : Subgroup G).subgroupOf L).map (Coordinates.sp4 m).quotientMap =
      unipotent.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow T L
    D.sylow_normalizes_component
  let Q := P.mapSurjective (Coordinates.sp4 m).quotientMap_surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Sp F.Carrier)
    (unipotentSylow F.card_eq F.degree_pos) Q
  refine ⟨g, ?_⟩
  have he := congrArg (fun R : Sylow 2 (Sp F.Carrier) => (R : Subgroup (Sp F.Carrier))) hg
  rw [Sylow.coe_subgroup_smul, coe_unipotentSylow] at he
  change unipotent.map (MulAut.conj g).toMonoidHom = (P : Subgroup L).map _ at he
  rw [hP] at he
  exact he.symm

/-- A symplectic matrix aligning the literal inner Sylow. -/
def alignment : Sp F.Carrier := (exists_alignment m).choose

theorem alignment_spec :
    ((T : Subgroup G).subgroupOf L).map (Coordinates.sp4 m).quotientMap =
      unipotent.map (MulAut.conj (alignment m)).toMonoidHom :=
  (exists_alignment m).choose_spec

/-- The four stages include the original central kernel as stage zero. -/
def space (i : Fin 4) : Submodule F.Carrier (Coordinates.sp4 m).Space :=
  ModelFlag.movedStage (alignment m) i

theorem space_dimension (i : Fin 4) : Module.finrank F.Carrier (space m i) = i.val :=
  ModelFlag.movedStage_dimension _ i

theorem space_nested : Monotone (space m) := ModelFlag.movedStage_nested _

theorem space_zero : space m 0 = ⊥ := ModelFlag.movedStage_zero _

/-- Membership in the next stage is determined by the original commutators. -/
theorem mem_preimage_succ_iff (i : Fin 3) (v : V) :
    (v : G) ∈ (Coordinates.sp4 m).preimage (space m i.succ) ↔
      ∀ l : L, (l : G) ∈ T →
        (l : G) * (v : G) * (l : G)⁻¹ * (v : G)⁻¹ ∈
          (Coordinates.sp4 m).preimage (space m i.castSucc) := by
  let c := Coordinates.sp4 m
  rw [c.mem_preimage]
  change (c.projection v).toAdd ∈ ModelFlag.movedStage (alignment m) i.succ ↔ _
  rw [ModelFlag.mem_movedStage_succ_iff, ← alignment_spec]
  have he (l : L) :
      (l : G) * (v : G) * (l : G)⁻¹ * (v : G)⁻¹ ∈ c.preimage (space m i.castSucc) ↔
        c.modelAction (c.quotientMap l) (c.projection v).toAdd - (c.projection v).toAdd ∈
          space m i.castSucc := by
    let w : V := V.normalizerMonoidHom (inclusion D.normalizes l) v * v⁻¹
    change (w : G) ∈ c.preimage _ ↔ _
    rw [c.mem_preimage]
    change (c.projection w).toAdd ∈ _ ↔ _
    simp only [w, map_mul, map_inv, toAdd_mul, toAdd_inv,
      c.projection_component_conjugation, sub_eq_add_neg]
  constructor
  · intro h l hl
    exact (he l).mpr (h _ ⟨l, hl, rfl⟩)
  · rintro h _ ⟨l, hl, rfl⟩
    exact (he l).mp (h l hl)

/-- Uniqueness in each positive dimension needs only the inner Sylow. -/
theorem space_inner_unique (i : Fin 3)
    (U : Submodule F.Carrier (Coordinates.sp4 m).Space)
    (hdim : Module.finrank F.Carrier U = i.val + 1)
    (hU : (T : Subgroup G) ⊓ L ≤ normalizer ((Coordinates.sp4 m).preimage U : Set G)) :
    U = space m i.succ := by
  apply ModelFlag.movedStage_unique (alignment m) i U _ hdim
  rw [← alignment_spec]
  rintro _ ⟨l, hl, rfl⟩
  rw [mem_stabilizer_iff]
  intro x hx
  exact ((Coordinates.sp4 m).mem_normalizer_preimage_iff U l).mp
    (hU ⟨hl, l.property⟩) x |>.mpr hx

/-- T preserves the intrinsic filtration, including every nonsplit central vector. -/
theorem sylow_normalizes_space (S : D.NonbinaryNaturalInput) (i : Fin 4) :
    (T : Subgroup G) ≤ normalizer ((Coordinates.sp4 m).preimage (space m i) : Set G) := by
  induction i using Fin.induction with
  | zero =>
    rw [space_zero, Coordinates.preimage_bot]
    exact (le_inf S.sylow_normalizes
      (D.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
        inf_normalizer_le_normalizer_inf
  | succ i ih =>
    apply le_normalizer_iff.mpr
    intro t ht v hv
    have hvV : v ∈ V := D.centralQuotientPreimage_le _ hv
    let v' : V := ⟨v,hvV⟩
    let w : V := V.normalizerMonoidHom ⟨t,S.sylow_normalizes ht⟩ v'
    change (w : G) ∈ (Coordinates.sp4 m).preimage (space m i.succ)
    apply (mem_preimage_succ_iff m i w).mpr
    intro l hl
    let a : L := L.normalizerMonoidHom
      ⟨t⁻¹,D.sylow_normalizes_component ((T : Subgroup G).inv_mem ht)⟩ l
    have hat : (a : G) ∈ T := by
      change t⁻¹ * (l : G) * (t⁻¹)⁻¹ ∈ T
      exact (T : Subgroup G).mul_mem
        ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem ht) hl)
        ((T : Subgroup G).inv_mem ((T : Subgroup G).inv_mem ht))
    have ha := (mem_preimage_succ_iff m i v').mp hv a hat
    have hh := (ih ht _).mp ha
    have he : (l : G) * (w : G) * (l : G)⁻¹ * (w : G)⁻¹ =
        t * ((a : G) * (v' : G) * (a : G)⁻¹ * (v' : G)⁻¹) * t⁻¹ := by
      change (l : G) * (t * v * t⁻¹) * (l : G)⁻¹ * (t * v * t⁻¹)⁻¹ =
        t * ((t⁻¹ * (l : G) * (t⁻¹)⁻¹) * v *
          (t⁻¹ * (l : G) * (t⁻¹)⁻¹)⁻¹ * v⁻¹) * t⁻¹
      group
    rw [he]
    exact hh

/-- The required actual flag, with no additional geometric premise. -/
def flag (S : D.NonbinaryNaturalInput) : InvariantFlag (Coordinates.sp4 m) where
  space i := space m i.succ
  dimension i := space_dimension m i.succ
  nested := fun _ _ hij => space_nested m (Fin.succ_le_succ_iff.mpr hij)
  invariant i := sylow_normalizes_space m S i.succ

/-- The uniqueness input consumed by the independent Cartan construction. -/
theorem flag_inner_unique (S : D.NonbinaryNaturalInput) : (flag m S).IsInnerUnique :=
  space_inner_unique m

/-- Each field dimension also has a unique T-invariant preimage. -/
theorem flag_unique (S : D.NonbinaryNaturalInput) : (flag m S).IsUnique := by
  intro i U hd hn
  exact flag_inner_unique m S i U hd (inf_le_left.trans hn)

/-- The original source Cartan exists and normalizes the constructed Sp4 flag. -/
theorem exists_normalizing_cartan (S : D.NonbinaryNaturalInput) :
    ∃ X : Subgroup G, IsCartan T L X ∧
      ∀ i, X ≤ normalizer ((flag m S).Vi i : Set G) :=
  (flag m S).exists_normalizing_cartan (flag_inner_unique m S)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4
