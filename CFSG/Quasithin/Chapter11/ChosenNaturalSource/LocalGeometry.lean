module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonbinaryNaturalCartan
public import CFSG.Quasithin.Chapter11.Section01To02.SourceDefs
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.Hall.TwoClosedNormal
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow

/-!
# Literal local geometry for a chosen nonbinary natural module

The three coordinate constructors retain the complete group isomorphism and
binary intertwiner of the supplied natural action. Field subspaces pull back
through that intertwiner and the original fixed-space quotient map. The bottom
preimage is proved to be the actual C_V(L); the pullback reflects inclusion.
Thus field dimensions and incidence describe genuine ambient subgroups.

The source flag is a nested family of one-, two- and three-dimensional field
subspaces invariant under the original Sylow subgroup. Its parabolic residuals
are N_L(V_i)^infinity, and its radicals are O_2(L_i T). The source Cartan condition
is precisely the Hall odd-order condition inside N_L(T intersect L O_2(LT)).
For any such flag, its normalizers belong to He, its residuals are perfect and
T-invariant, and its radicals contain the original seed. The Cartan coprimality
consumer uses these same preimages.

This module constructs coordinates from NonbinaryNaturalInput and proves the
transport and local consequences. Existence and uniqueness of the invariant
flag, existence and rank of the Cartan, and the component and weak-closure
conclusions are separate source obligations. None is an input field of S.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.0.2--11.1.1, printed pp.759--761, and 11.5.6(1), printed p.780.
-/

open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (F : BinaryField)

omit [Finite G] in
/-- The literal quotient kills exactly the original vectors fixed by L. -/
theorem quotient_eq_one_iff (v : V) :
    D.toCentralQuotient v = 1 ↔ (v : G) ∈ centralizer (L : Set G) := by
  let w : D.space := (D.spaceEquiv.symm v).toAdd
  have hw : (w.val.toMul.val : G) = v :=
    (D.spaceEquiv_apply w).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
  change Submodule.Quotient.mk w = (0 : D.chosenCentralQuotient) ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · intro h l hl
    have he := congrArg (fun z : Additive (ReducedModule (L ⊔ (T : Subgroup G))) =>
      (z.toMul.val : G)) (h ⟨⟨l, (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) hl⟩, hl⟩)
    change l * (w.val.toMul.val : G) * l⁻¹ = (w.val.toMul.val : G) at he
    rw [hw] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro h l
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (l.val : G) * (w.val.toMul.val : G) * (l.val : G)⁻¹ = (w.val.toMul.val : G)
    rw [hw]
    exact mul_inv_eq_iff_eq_mul.mpr (h _ l.property)

omit [Finite G] in
/-- The zero subspace lifts to C_V(L), including any nonsplit central part. -/
theorem centralQuotientPreimage_bot :
    D.centralQuotientPreimage ⊥ = V ⊓ centralizer (L : Set G) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.property, (quotient_eq_one_iff D v).mp hv⟩
  · rintro ⟨hxV, hxC⟩
    exact ⟨⟨x, hxV⟩, (quotient_eq_one_iff D ⟨x, hxV⟩).mpr hxC, rfl⟩

/-- Actual natural-action markings, retaining full SL3, rank-two Sp4 and G2. -/
inductive Coordinates where
  | sl3 (marking : ActionEquiv D.centralQuotientAction (linearNatural F 3))
  | sp4 (marking : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))
  | g2 (marking : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural F.Carrier)))

namespace Coordinates
variable {D F} (c : Coordinates D F)
/-- The field space of the marked model; G2 uses the octonion quotient. -/
def Space : Type := match c with
  | .sl3 _ => Fin 3 → F.Carrier
  | .sp4 _ => (Fin 2 ⊕ Fin 2) → F.Carrier
  | .g2 _ => Atlas.G2.Natural.Space F.Carrier

instance : AddCommGroup c.Space := match c with
  | .sl3 _ => inferInstanceAs (AddCommGroup (Fin 3 → F.Carrier))
  | .sp4 _ => inferInstanceAs (AddCommGroup ((Fin 2 ⊕ Fin 2) → F.Carrier))
  | .g2 _ => inferInstanceAs (AddCommGroup (Atlas.G2.Natural.Space F.Carrier))
instance : Module F.Carrier c.Space := match c with
  | .sl3 _ => inferInstanceAs (Module F.Carrier (Fin 3 → F.Carrier))
  | .sp4 _ => inferInstanceAs (Module F.Carrier ((Fin 2 ⊕ Fin 2) → F.Carrier))
  | .g2 _ => inferInstanceAs (Module F.Carrier (Atlas.G2.Natural.Space F.Carrier))
instance : Module (ZMod 2) c.Space := match c with
  | .sl3 _ => inferInstanceAs (Module (ZMod 2) (Fin 3 → F.Carrier))
  | .sp4 _ => inferInstanceAs (Module (ZMod 2) ((Fin 2 ⊕ Fin 2) → F.Carrier))
  | .g2 _ => inferInstanceAs (Module (ZMod 2) (Atlas.G2.Natural.Space F.Carrier))
instance : IsScalarTower (ZMod 2) F.Carrier c.Space := match c with
  | .sl3 _ => inferInstanceAs (IsScalarTower (ZMod 2) F.Carrier (Fin 3 → F.Carrier))
  | .sp4 _ => inferInstanceAs (IsScalarTower (ZMod 2) F.Carrier ((Fin 2 ⊕ Fin 2) → F.Carrier))
  | .g2 _ => inferInstanceAs (IsScalarTower (ZMod 2) F.Carrier (Atlas.G2.Natural.Space F.Carrier))

/-- The binary intertwiner attached to this same group marking. -/
def linearEquiv : D.chosenCentralQuotient ≃ₗ[ZMod 2] c.Space := by
  cases c with
  | sl3 m => exact m.linearEquiv
  | sp4 m => exact m.linearEquiv
  | g2 m => exact m.linearEquiv

/-- A field subspace transported to the literal chosen quotient. -/
def binarySubspace (U : Submodule F.Carrier c.Space) :
    Submodule (ZMod 2) D.chosenCentralQuotient :=
  (U.restrictScalars (ZMod 2)).comap c.linearEquiv.toLinearMap

/-- Its ambient inverse image under the original projection from V. -/
def preimage (U : Submodule F.Carrier c.Space) : Subgroup G :=
  D.centralQuotientPreimage (c.binarySubspace U)

/-- Membership uses the actual original quotient map. -/
theorem mem_preimage (U : Submodule F.Carrier c.Space) (v : V) :
    (v : G) ∈ c.preimage U ↔ c.linearEquiv (D.toCentralQuotient v).toAdd ∈ U := by
  change (v : G) ∈ (Subgroup.map V.subtype _) ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    have : w = v := Subtype.ext hwv
    subst w
    exact hw
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- Transport reflects field-subspace inclusion. -/
theorem binarySubspace_le_iff (U W : Submodule F.Carrier c.Space) :
    c.binarySubspace U ≤ c.binarySubspace W ↔ U ≤ W := by
  constructor
  · intro h u hu
    obtain ⟨v, rfl⟩ := c.linearEquiv.surjective u
    exact h hu
  · intro h u hu
    exact h hu

/-- Surjectivity of the original quotient makes ambient pullback reflect inclusion. -/
theorem preimage_le_iff (U W : Submodule F.Carrier c.Space) :
    c.preimage U ≤ c.preimage W ↔ U ≤ W := by
  constructor
  · intro h u hu
    obtain ⟨q, rfl⟩ := c.linearEquiv.surjective u
    obtain ⟨v, hv⟩ := D.toCentralQuotient_surjective (Multiplicative.ofAdd q)
    have hu' : (v : G) ∈ c.preimage U := (c.mem_preimage U v).mpr (by simpa [hv] using hu)
    have hw := (c.mem_preimage W v).mp (h hu')
    simpa [hv] using hw
  · intro h
    exact map_mono (comap_mono (show
      (c.binarySubspace U).toAddSubgroup.toSubgroup ≤
        (c.binarySubspace W).toAddSubgroup.toSubgroup from
      (c.binarySubspace_le_iff U W).mpr h))

/-- A positive-dimensional field subspace has nontrivial ambient preimage. -/
theorem preimage_ne_bot (U : Submodule F.Carrier c.Space) (hU : U ≠ ⊥) :
    c.preimage U ≠ ⊥ := by
  apply D.centralQuotientPreimage_ne_bot
  intro h
  apply hU
  apply bot_unique
  apply (c.binarySubspace_le_iff U ⊥).mp
  rw [h]
  exact bot_le

/-- Distinct field subspaces remain distinct ambient subgroups. -/
theorem preimage_injective : Function.Injective c.preimage := by
  intro U W h
  exact le_antisymm ((c.preimage_le_iff U W).mp h.le)
    ((c.preimage_le_iff W U).mp h.ge)

/-- The zero field subspace lifts to the original relative centralizer. -/
theorem preimage_bot : c.preimage ⊥ = V ⊓ centralizer (L : Set G) := by
  have hz : c.binarySubspace ⊥ = ⊥ := by
    ext q
    change c.linearEquiv q = 0 ↔ q = 0
    exact c.linearEquiv.map_eq_zero_iff
  change D.centralQuotientPreimage (c.binarySubspace ⊥) = _
  rw [hz, centralQuotientPreimage_bot]

/-- The whole field space lifts to the original V. -/
theorem preimage_top : c.preimage ⊤ = V := by
  apply le_antisymm (D.centralQuotientPreimage_le _)
  intro v hv
  exact (c.mem_preimage ⊤ ⟨v, hv⟩).mpr (by trivial)

end Coordinates

/-- The source input supplies coordinates without assuming any flag geometry. -/
theorem exists_coordinates (S : D.NonbinaryNaturalInput) :
    Nonempty (Coordinates D S.field) := by
  cases S.natural with
  | sl3 h => exact ⟨.sl3 h.some⟩
  | sp4 h => exact ⟨.sp4 h.some⟩
  | g2 h => exact ⟨.g2 h.some⟩

/-- Choose one of the actual action markings supplied by the source. -/
def coordinates (S : D.NonbinaryNaturalInput) : Coordinates D S.field :=
  (exists_coordinates D S).some

variable {D F}
/-- The source flag with genuine field dimensions and actual T-invariant preimages.
Existence and uniqueness must be proved from S; this is an output specification. -/
structure InvariantFlag (c : Coordinates D F) where
  space : Fin 3 → Submodule F.Carrier c.Space
  dimension : ∀ i, Module.finrank F.Carrier (space i) = i.val + 1
  nested : Monotone space
  invariant : ∀ i, (T : Subgroup G) ≤ normalizer (c.preimage (space i) : Set G)

/-- The source's uniqueness assertion for each field dimension. -/
def InvariantFlag.IsUnique {c : Coordinates D F} (f : InvariantFlag c) : Prop :=
  ∀ (i : Fin 3) (U : Submodule F.Carrier c.Space),
    Module.finrank F.Carrier U = i.val + 1 →
    (T : Subgroup G) ≤ normalizer (c.preimage U : Set G) → U = f.space i

/-- N_L(U)^infinity embedded in the common ambient group. -/
def localResidual (L U : Subgroup G) : Subgroup G :=
  (solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
    (L ⊓ normalizer (U : Set G)).subtype

/-- The literal O_2(L(U)T), with L(U) the normalizer residual. -/
def localRadical (T : Sylow 2 G) (L U : Subgroup G) : Subgroup G :=
  (localResidual L U ⊔ (T : Subgroup G)).pCoreIn 2

/-- The source T_L = T intersect L O_2(LT). -/
def sourceTL (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  (T : Subgroup G) ⊓ (L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)

/-- The actual N_L(T_L) in which the Cartan is selected. -/
def cartanNormalizer (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  L ⊓ normalizer (sourceTL T L : Set G)

/-- The source Hall condition, with the relative subgroup taken in N_L(T_L). -/
def IsCartan (T : Sylow 2 G) (L X : Subgroup G) : Prop :=
  X ≤ cartanNormalizer T L ∧
    IsHallSubgroup OddHall.oddPrimes (X.subgroupOf (cartanNormalizer T L))

omit [Finite G] in
/-- The ambient residual lies in the literal local normalizer. -/
theorem localResidual_le (U : Subgroup G) : localResidual L U ≤ L ⊓ normalizer (U : Set G) :=
  map_subtype_le _

/-- The finite terminal derived subgroup is perfect. -/
theorem localResidual_perfect (U : Subgroup G) : Group.IsPerfect (localResidual L U) := by
  let H := L ⊓ normalizer (U : Set G)
  let e := (solvableResidual H).equivMapOfInjective H.subtype H.subtype_injective
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

omit [Finite G] in
/-- T-invariance of U gives T-invariance of N_L(U)^infinity. -/
theorem sylow_normalizes_localResidual (D : ChosenModule T L V)
    (U : Subgroup G) (hU : (T : Subgroup G) ≤ normalizer (U : Set G)) :
    (T : Subgroup G) ≤ normalizer (localResidual L U : Set G) :=
  ((le_inf D.sylow_normalizes_component (hU.trans (normalizer _).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))

omit [Finite G] in
/-- The radical of L(U)T lies in the original T. -/
theorem localRadical_le_sylow (U : Subgroup G) : localRadical T L U ≤ T := by
  simpa only [localRadical, Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (localResidual L U ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

omit [Finite G] in
/-- The relative Hall condition gives odd order for the ambient subgroup. -/
theorem IsCartan.odd {X : Subgroup G} (hX : IsCartan T L X) : Odd (Nat.card X) := by
  have h := OddHall.odd_hall_odd hX.2
  rwa [Nat.card_congr (subgroupOfEquivOfLe hX.1).toEquiv] at h

namespace InvariantFlag
variable {c : Coordinates D F} (f : InvariantFlag c)
/-- Indices 0,1,2 represent the source V1,V2,V3. -/
def Vi (i : Fin 3) : Subgroup G := c.preimage (f.space i)
/-- Indices 0,1 represent the source L1,L2. -/
def Li (i : Fin 2) : Subgroup G := localResidual L (f.Vi i.castSucc)
/-- Indices 0,1 represent the source R1,R2. -/
def Ri (i : Fin 2) : Subgroup G := localRadical T L (f.Vi i.castSucc)

/-- The specified field dimensions are positive. -/
theorem space_ne_bot (i : Fin 3) : f.space i ≠ ⊥ := by
  intro h
  have hh := f.dimension i
  rw [h, finrank_bot] at hh
  omega

/-- Each source flag preimage is nontrivial. -/
theorem V_ne_bot (i : Fin 3) : f.Vi i ≠ ⊥ :=
  c.preimage_ne_bot _ (f.space_ne_bot i)

/-- Each normalizer is an actual two-local of the original group. -/
theorem normalizer_twoLocal (i : Fin 3) : IsTwoLocal (normalizer (f.Vi i : Set G)) :=
  ⟨f.Vi i, f.V_ne_bot i,
    @IsElementaryAbelian.isPGroup 2 _ _ (D.centralQuotientPreimage_elementary _), rfl⟩

/-- Condition E puts these actual flag normalizers in He. -/
theorem normalizer_mem_He (S : D.NonbinaryNaturalInput) (i : Fin 3) :
    normalizer (f.Vi i : Set G) ∈ Chapter1.He G :=
  Chapter1.twoLocal_mem_He_of_sylow_le T (S.source.simpleQTKE.evenCharacteristic T)
    (f.normalizer_twoLocal i) (f.invariant i)

/-- The chosen source residuals are T-invariant. -/
theorem sylow_normalizes_Li (i : Fin 2) :
    (T : Subgroup G) ≤ normalizer (f.Li i : Set G) :=
  sylow_normalizes_localResidual D _ (f.invariant i.castSucc)

/-- Field incidence gives the actual ambient chain V1 ≤ V2 ≤ V3. -/
theorem Vi_mono : Monotone f.Vi := by
  intro i j hij
  exact (c.preimage_le_iff _ _).mpr (f.nested hij)

/-- Each field preimage contains the original central part C_V(L). -/
theorem centralizer_le_Vi (i : Fin 3) : V ⊓ centralizer (L : Set G) ≤ f.Vi i := by
  rw [← c.preimage_bot]
  exact (c.preimage_le_iff _ _).mpr bot_le

/-- The radical of each residual join contains the whole original seed. -/
theorem seed_le_Ri (S : D.NonbinaryNaturalInput) (i : Fin 2) : V ≤ f.Ri i := by
  let := D.elementary
  apply le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
    (D.le_sylow.trans le_sup_right)
  exact sup_le ((localResidual_le _).trans inf_le_left |>.trans D.normalizes)
    S.sylow_normalizes

end InvariantFlag

/-- Apply 11.5.6(1)'s numerical argument in the actual flag normalizer.
The Cartan rank, normalization and disjointness inputs remain explicit. -/
theorem flag_cartan_coprime (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) (i : Fin 3)
    (X Y : Subgroup G)
    (hX : X ≤ normalizer (f.Vi i : Set G))
    (hY : Y ≤ normalizer (f.Vi i : Set G))
    (hr : ∀ p : ℕ, p.Prime → p ∣ 2 ^ S.field.degree - 1 → 2 ≤ primeRank p X)
    (hn : X ≤ normalizer (Y : Set G)) (hd : Disjoint X Y) :
    Nat.Coprime (Nat.card Y) (2 ^ S.field.degree - 1) := by
  apply D.centralQuotientPreimage_cartan_coprime_of_many S (c.binarySubspace (f.space i))
    _ X Y hX hY hr hn hd
  intro hz
  apply f.space_ne_bot i
  apply bot_unique
  exact (c.binarySubspace_le_iff _ ⊥).mp (by rw [hz]; exact bot_le)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
