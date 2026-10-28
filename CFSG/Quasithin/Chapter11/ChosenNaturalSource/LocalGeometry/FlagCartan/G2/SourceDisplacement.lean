module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.SourceFlag
public import Theory.GroupTheory.Commutator.SimpleSubnormal
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Displacement through the original chosen G₂ quotient

The perfect point residual acts trivially on the one-dimensional first
quotient. Its remaining displacements lie in C_V(L), so the three-subgroup
lemma proves that it centralizes the full first preimage. Once its image
contains the marked inner Sylow, the intrinsic model flag identifies this
preimage as C_{V3}(L1) and the second preimage by displacement modulo V1.
Consequently N_G(V3) intersect N_G(L1) preserves V1. Every map here uses
the original marking and the original central kernel.

The point-residual image containment remains the precise preceding model
input owned by the residual-incidence construction. It is not asserted here.
The actual consumer is G2.DisplacementNormalizer.

Source: Aschbacher--Smith, opening §11.1, printed pp.760--762, and the
geometric step of 11.1.4 on p.765; I.2.3 on p.413.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2

private theorem perfect_fixes_line {k H E : Type*} [Field k] [Group H] [Group.IsPerfect H]
    [AddCommGroup E] [Module k E] (ρ : Representation k H E)
    (U : Submodule k E) (hd : Module.finrank k U = 1)
    (hU : ∀ h : H, ∀ x ∈ U, ρ h x ∈ U) (h : H) (x : E) (hx : x ∈ U) : ρ h x = x := by
  let W : Subrepresentation ρ := ⟨U, hU⟩
  let r := W.toRepresentation
  let f := r.toHomUnits
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : IsMulCommutative f.range := ⟨⟨by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    apply Units.ext
    change r a * r b = r b * r a
    obtain ⟨s, hs, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd (r a)
    obtain ⟨t, ht, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd (r b)
    rw [hs, ht]
    simp [smul_smul, mul_comm]⟩⟩
  have he : f h = 1 := congrArg Subtype.val
    (Subsingleton.elim (⟨f h, h, rfl⟩ : f.range) 1)
  have hr : r h = 1 := congrArg Units.val he
  exact congrArg Subtype.val (DFunLike.congr_fun hr (⟨x,hx⟩ : U))

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

/-- Displacement under the original quotient, with the central kernel unchanged. -/
theorem projection_displacement (l : L) (v : V) :
    ((coordinates S m).projection
      (V.normalizerMonoidHom (inclusion D.normalizes l) v * v⁻¹)).toAdd =
      (coordinates S m).modelAction ((coordinates S m).quotientMap l)
        ((coordinates S m).projection v).toAdd - ((coordinates S m).projection v).toAdd := by
  rw [map_mul, map_inv]
  simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
  rw [(coordinates S m).projection_component_conjugation]

/-- The perfect point residual centralizes the entire first preimage, including C_V(L). -/
theorem first_le_point_centralizer :
    (flag S m).Vi 0 ≤ centralizer ((flag S m).Li 0 : Set G) := by
  let R := (flag S m).Li 0
  have hRL : R ≤ L := (localResidual_le _).trans inf_le_left
  have hRN : R ≤ normalizer ((flag S m).Vi 0 : Set G) :=
    (localResidual_le _).trans inf_le_right
  let : Group.IsPerfect R := localResidual_perfect _
  let ρ := (coordinates S m).modelAction.comp
    ((coordinates S m).quotientMap.comp (inclusion hRL))
  have hfix (r : R) (x : (coordinates S m).Space) (hx : x ∈ (flag S m).space 0) :
      ρ r x = x := by
    apply perfect_fixes_line ρ ((flag S m).space 0) ((flag S m).dimension 0) _ r x hx
    intro a y hy
    exact (((coordinates S m).mem_normalizer_preimage_iff _
      (inclusion hRL a)).mp (hRN a.property) y).mpr hy
  have hcomm : ⁅R, (flag S m).Vi 0⁆ ≤ centralizer (R : Set G) := by
    apply commutator_le.mpr
    intro r hr v hv
    have hvV := D.centralQuotientPreimage_le _ hv
    let l : L := ⟨r, hRL hr⟩
    let w : V := ⟨v, hvV⟩
    have hw := ((coordinates S m).mem_preimage _ w).mp hv
    have hd := projection_displacement S m l w
    have he := hfix ⟨r,hr⟩ _ hw
    change (coordinates S m).modelAction ((coordinates S m).quotientMap l)
      ((coordinates S m).projection w).toAdd = ((coordinates S m).projection w).toAdd at he
    rw [he, sub_self] at hd
    have hz := ((coordinates S m).projection_eq_one_iff
      (V.normalizerMonoidHom (inclusion D.normalizes l) w * w⁻¹)).mp
      (Multiplicative.toAdd.injective hd)
    exact centralizer_le hRL hz
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_eq_bot_of_iterated_eq_bot
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rwa [commutator_comm] at hcomm

/-- The point residual uses the original component map, followed only by the derived comparison. -/
def pointMap : (flag S m).Li 0 →* Atlas.G2.Natural.OrthogonalCover.SylowFlag.D S.field.Carrier :=
  (derivedMap S m).comp (inclusion ((localResidual_le _).trans inf_le_left))

/-- The unchanged component two-core contains the kernel on the point residual. -/
theorem pointMap_ker_isTwoGroup : IsPGroup 2 (pointMap S m).ker := by
  let hRL : (flag S m).Li 0 ≤ L := (localResidual_le _).trans inf_le_left
  let j : (pointMap S m).ker →* pCore 2 L :=
    ((inclusion hRL).comp (pointMap S m).ker.subtype).codRestrict _ (by
      intro x
      apply (QuotientGroup.eq_one_iff _).mp
      apply (coordinates S m).groupEquiv.injective
      rw [map_one]
      exact congrArg Subtype.val x.property)
  exact (pCore_isPGroup (p := 2) (G := L)).of_injective j (by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : pCore 2 L => (z.val : G)) h)))

/-- Containment of the marked Sylow in the residual image is the exact remaining
model input; the original two-group kernel supplies its literal Sylow lift. -/
theorem exists_pointSylow
    (himage : (modelSylow S m : Subgroup _) ≤ (pointMap S m).range) :
    ∃ P : Sylow 2 ((flag S m).Li 0),
      (P : Subgroup ((flag S m).Li 0)).map (pointMap S m) = modelSylow S m := by
  refine ⟨(modelSylow S m).comapOfKerIsPGroup (pointMap S m)
    (pointMap_ker_isTwoGroup S m) himage, ?_⟩
  exact Subgroup.map_comap_eq_self himage

/-- Literal displacement criterion for a point-residual Sylow with the marked inner image. -/
theorem mem_second_iff_displacement
    (P : Sylow 2 ((flag S m).Li 0))
    (hP : (P : Subgroup ((flag S m).Li 0)).map (pointMap S m) = modelSylow S m)
    (v : V) :
    (v : G) ∈ (flag S m).Vi 1 ↔
      ∀ p : P, (p.val.val : G) * v * (p.val.val : G)⁻¹ * (v : G)⁻¹ ∈ (flag S m).Vi 0 := by
  refine ((coordinates S m).mem_preimage ((modelFlag S m).space 1) v).trans ?_
  refine ((modelFlag S m).next 0 ((coordinates S m).projection v).toAdd).trans ?_
  constructor
  · intro h p
    let l : L := ⟨p.val.val, (localResidual_le _ p.val.property).1⟩
    have hm : pointMap S m p.val ∈ (modelSylow S m : Subgroup _) := by
      rw [← hP]
      exact mem_map_of_mem _ p.property
    have hd := h ⟨pointMap S m p.val, hm⟩
    apply ((coordinates S m).mem_preimage _
      (V.normalizerMonoidHom (inclusion D.normalizes l) v * v⁻¹)).mpr
    change ((coordinates S m).projection
      (V.normalizerMonoidHom (inclusion D.normalizes l) v * v⁻¹)).toAdd ∈ _
    rw [projection_displacement]
    exact hd
  · intro h ⟨q,hq⟩
    rw [← hP] at hq
    obtain ⟨p,hp,rfl⟩ := hq
    let l : L := ⟨p.val, (localResidual_le _ p.property).1⟩
    have hd := ((coordinates S m).mem_preimage _
      (V.normalizerMonoidHom (inclusion D.normalizes l) v * v⁻¹)).mp (h ⟨p,hp⟩)
    change ((coordinates S m).projection
      (V.normalizerMonoidHom (inclusion D.normalizes l) v * v⁻¹)).toAdd ∈ _ at hd
    rw [projection_displacement] at hd
    exact hd

/-- The first preimage is intrinsic to V3 and its actual point residual. -/
theorem first_eq_third_inf_point_centralizer
    (P : Sylow 2 ((flag S m).Li 0))
    (hP : (P : Subgroup ((flag S m).Li 0)).map (pointMap S m) = modelSylow S m) :
    (flag S m).Vi 0 = (flag S m).Vi 2 ⊓ centralizer ((flag S m).Li 0 : Set G) := by
  apply le_antisymm
  · exact le_inf ((flag S m).Vi_mono (by decide)) (first_le_point_centralizer S m)
  · rintro v ⟨hv,hc⟩
    let w : V := ⟨v, D.centralQuotientPreimage_le _ hv⟩
    apply ((coordinates S m).mem_preimage _ w).mpr
    apply ((modelFlag S m).first _).mpr
    rintro ⟨q,hq⟩
    rw [← hP] at hq
    obtain ⟨p,hp,rfl⟩ := hq
    let l : L := ⟨p.val, (localResidual_le _ p.property).1⟩
    have he : V.normalizerMonoidHom (inclusion D.normalizes l) w = w := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hc p.val p.property)
    have hh := (coordinates S m).projection_component_conjugation l w
    rw [he] at hh
    exact hh.symm

/-- Common normalizers preserve V1 because it is the intrinsic fixed subgroup of L1 in V3. -/
theorem normalizer_preserves_first
    (P : Sylow 2 ((flag S m).Li 0))
    (hP : (P : Subgroup ((flag S m).Li 0)).map (pointMap S m) = modelSylow S m) :
    normalizer ((flag S m).Vi 2 : Set G) ⊓ normalizer ((flag S m).Li 0 : Set G) ≤
      normalizer ((flag S m).Vi 0 : Set G) := by
  rw [first_eq_third_inf_point_centralizer S m P hP]
  exact (inf_le_inf_left _ (normalizer_le_normalizer_centralizer _)).trans
    inf_normalizer_le_normalizer_inf

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2
