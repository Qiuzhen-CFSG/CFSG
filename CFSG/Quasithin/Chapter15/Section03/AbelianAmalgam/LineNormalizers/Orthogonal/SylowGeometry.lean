module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal.FullAction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.OrthogonalNormalizer
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.LineGeometry
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal.SylowTransport

/-!
# The singular-line Sylow calculation (15.3.66(1)--(4))

The finite isometry calculation and its fixed-vector and displacement
extensions are transported through the compatible natural action. The ambient
Sylow selection supplies the finite Sylow selection, and the action kernel
preserves the relative index. `line_sylow_geometry_of_source` proves the actual
Ω-intersection, index, four-subgroup distinction, `Z ≤ E`, and commutator
identity from the source inputs, with `Z = C_V(T)` as in 15.3.2(2).

The earlier `SingularLineSylowData` API is preserved as a conditional legacy
interface. Its `hZV` field uses the transposed centralizer `C_T(V)` and its
conclusion fields are not proofs of the source theorem. The new theorem does
not use that record.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.66(1)--(4)
and the identity [V,C_T(E)] = E in the proof of 15.3.67, printed pp.1152--1153;
the fixed-space premise is 15.3.2(2), printed p.1121.
-/

@[expose] public section

open Subgroup
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.OrthogonalProducts

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal

variable {G : Type*} [Group G] [Finite G]

/--
Finite geometry data for the selected singular line.  Every field refers to
an actual subgroup/image in the compatible action.  In particular
`imageOmega` uses `OrthogonalFourBinary.omega`, the elementary orthogonal
subgroup of the fixed quadratic form; it is not an order-only surrogate.
-/
structure SingularLineSylowData
    (T : Sylow 2 G) (M V V₁ E : Subgroup G)
    (d : NaturalAction V M) where
  hTM : (T : Subgroup G) ≤ M
  hM : M = normalizer (V : Set G)
  hV₁V : V₁ ≤ V
  hV₁card : Nat.card V₁ = 4
  hV₁definite : ∀ v : V₁, v ≠ 1 →
    ¬ d.singular ⟨v, hV₁V v.property⟩
  hEV : E ≤ V
  hEcard : Nat.card E = 4
  hEsingular : ∀ e : E, d.singular ⟨e, hEV e.property⟩
  /-- Legacy transposed-centralizer premise; the source has `Z = C_V(T)`. -/
  hZV : centralInvolutions T = (T : Subgroup G) ⊓ centralizer (V : Set G)
  hZcard : Nat.card (centralInvolutions T) = 2
  /-- The selected Sylow subgroup in `M_E`, with its ambient image fixed. -/
  P : Sylow 2 (lineM M E)
  hP : (P : Subgroup (lineM M E)).map (lineM M E).subtype = lineT (T : Subgroup G) E
  /-- The finite coordinate comparison with the genuine Ω-subgroup. -/
  coordinateOmega :
    actionImage d (T : Subgroup G) ⊓
        lineStabilizer (coordinateLine d E) =
      actionImage d (T : Subgroup G) ⊓
        (OrthogonalFourBinary.omega : Subgroup OrthogonalFourBinary.IndexTwoNormalizer.IsometryGroup)
  /-- The finite index-two calculation in the actor. -/
  imageIndex : (actionImage d (lineT (T : Subgroup G) E)).relIndex
      (actionImage d (T : Subgroup G)) = 2
  /-- The image is the source's four-subgroup. -/
  imageKlein : IsKleinFour (actionImage d (lineT (T : Subgroup G) E))
  /-- It is distinct from the image of the definite-plane stabilizer. -/
  imageDistinct : actionImage d (lineT (T : Subgroup G) E) ≠
      actionImage d (planeStabilizer T V₁)
  /-- The central involution line is contained in the selected singular line. -/
  centralInLine : centralInvolutions T ≤ E
  /-- The immediately consumed commutator identity. -/
  commutatorCentralizer :
    ⁅V, (T : Subgroup G) ⊓ centralizer (E : Set G)⁆ = E

omit [Finite G] in
/-- The relative index survives passage through the compatible action kernel. -/
theorem lineT_actionImage_relIndex_of_E
    (T M V E : Subgroup G) (d : NaturalAction V M)
    (hTM : T ≤ M) (hEV : E ≤ V) :
    (actionImage d (lineT T E)).relIndex (actionImage d T) =
      (lineT T E).relIndex T := by
  let f : T →* OrthogonalFourBinary.IndexTwoNormalizer.IsometryGroup :=
    d.action.comp (inclusion hTM)
  let H : Subgroup T := (lineT T E).subgroupOf T
  have hker : f.ker ≤ H := by
    intro x hx
    have hm : (inclusion hTM x) ∈ d.action.ker := hx
    rw [action_ker d] at hm
    refine ⟨x.property, ?_⟩
    exact ((centralizer_le (show E ≤ V from hEV)).trans
      (_root_.centralizer_le_normalizer _)) hm
  have hh := relIndex_map_map f H (⊤ : Subgroup T)
  rw [sup_of_le_left hker, top_sup_eq] at hh
  dsimp [H] at hh
  have hrel : ((lineT T E).subgroupOf T).relIndex (⊤ : Subgroup T) =
      (lineT T E).relIndex T := by
    rw [← relIndex_subgroupOf (H := lineT T E) (K := T) (L := T) le_rfl]
    rw [Subgroup.subgroupOf_self]
  rw [hrel] at hh
  have hmapH : H.map f = ((lineT T E).subgroupOf M).map d.action := by
    change H.map (d.action.comp (inclusion hTM)) = _
    have hinc : H.map (inclusion hTM) = (lineT T E).subgroupOf M := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        change (y : G) ∈ lineT T E
        exact hy
      · intro hx
        change (x : G) ∈ lineT T E at hx
        rw [mem_map]
        refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
        exact hx
    calc
      H.map (d.action.comp (inclusion hTM)) =
          (H.map (inclusion hTM)).map d.action :=
        (Subgroup.map_map H d.action (inclusion hTM)).symm
      _ = _ := by rw [hinc]
  have hmapT : (⊤ : Subgroup T).map f = (T.subgroupOf M).map d.action := by
    change (⊤ : Subgroup T).map (d.action.comp (inclusion hTM)) = _
    have hinc : (⊤ : Subgroup T).map (inclusion hTM) = T.subgroupOf M := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        change (y : G) ∈ T
        exact y.property
      · intro hx
        change (x : G) ∈ T at hx
        rw [mem_map]
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        trivial
    calc
      (⊤ : Subgroup T).map (d.action.comp (inclusion hTM)) =
          ((⊤ : Subgroup T).map (inclusion hTM)).map d.action :=
        (Subgroup.map_map (⊤ : Subgroup T) d.action (inclusion hTM)).symm
      _ = _ := by rw [hinc]
  change (((lineT T E).subgroupOf M).map d.action).relIndex
      ((T.subgroupOf M).map d.action) = (lineT T E).relIndex T
  rw [← hmapH, ← hmapT]
  exact hh

omit [Finite G] in
theorem lineT_actionImage_eq_omega
    (T : Sylow 2 G) (M V V₁ E : Subgroup G)
    (d : NaturalAction V M) (h : SingularLineSylowData T M V V₁ E d) :
    actionImage d (lineT (T : Subgroup G) E) =
        actionImage d (T : Subgroup G) ⊓
          (OrthogonalFourBinary.omega :
            Subgroup OrthogonalFourBinary.IndexTwoNormalizer.IsometryGroup) := by
  rw [lineT, actionImage_lineNormalizer d (T : Subgroup G) E h.hEV,
    h.coordinateOmega]

omit [Finite G] in
/-- The relative index survives passage through the compatible action kernel. -/
theorem lineT_relIndex_of_sylow_data
    (T : Sylow 2 G) (M V V₁ E : Subgroup G)
    (d : NaturalAction V M) (h : SingularLineSylowData T M V V₁ E d)
    :
    (lineT (T : Subgroup G) E).relIndex (T : Subgroup G) = 2 := by
  rw [← lineT_actionImage_relIndex_of_E (T : Subgroup G) M V E d h.hTM h.hEV]
  exact h.imageIndex

omit [Finite G] in
/-- Conditional assembly of the legacy record; the source proof is
`line_sylow_geometry_of_source` below. -/
theorem line_sylow_geometry
    (T : Sylow 2 G) (M V V₁ E : Subgroup G)
    (d : NaturalAction V M) (h : SingularLineSylowData T M V V₁ E d)
    :
    actionImage d (lineT (T : Subgroup G) E) =
        actionImage d (T : Subgroup G) ⊓
            (OrthogonalFourBinary.omega :
              Subgroup OrthogonalFourBinary.IndexTwoNormalizer.IsometryGroup) ∧
      (lineT (T : Subgroup G) E).relIndex (T : Subgroup G) = 2 ∧
      IsKleinFour (actionImage d (lineT (T : Subgroup G) E)) ∧
      actionImage d (lineT (T : Subgroup G) E) ≠
        actionImage d (planeStabilizer T V₁) ∧
      centralInvolutions T ≤ E ∧
      ⁅V, (T : Subgroup G) ⊓ centralizer (E : Set G)⁆ = E := by
  exact ⟨lineT_actionImage_eq_omega T M V V₁ E d h,
    lineT_relIndex_of_sylow_data T M V V₁ E d h,
    h.imageKlein, h.imageDistinct, h.centralInLine, h.commutatorCentralizer⟩

variable {M V : Subgroup G}

/-- Source 15.3.66(1)--(3), transported from the selected finite Sylow intersection. -/
theorem line_sylow_image_geometry (d : NaturalAction V M)
    (T : Sylow 2 G) (V₁ E : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (hV₁V : V₁ ≤ V) (hV₁card : Nat.card V₁ = 4)
    (hV₁definite : ∀ v : V₁, v ≠ 1 → ¬ d.singular ⟨v,hV₁V v.property⟩)
    (hEV : E ≤ V) (hEcard : Nat.card E = 4)
    (hEsingular : ∀ e : E, d.singular ⟨e,hEV e.property⟩)
    (P : Sylow 2 (lineM M E))
    (hP : (P : Subgroup (lineM M E)).map (lineM M E).subtype =
      lineT (T : Subgroup G) E) :
    actionImage d (lineT (T : Subgroup G) E) =
        actionImage d (T : Subgroup G) ⊓ (OrthogonalFourBinary.omega :
          Subgroup OrthogonalFourBinary.IndexTwoNormalizer.IsometryGroup) ∧
      (lineT (T : Subgroup G) E).relIndex (T : Subgroup G) = 2 ∧
      IsKleinFour (actionImage d (lineT (T : Subgroup G) E)) ∧
      actionImage d (lineT (T : Subgroup G) E) ≠
        actionImage d (planeStabilizer T V₁) := by
  obtain ⟨S,hS⟩ := actionImage_sylow d T hTM
  obtain ⟨Q,hQ⟩ := coordinateLine_sylow d T E hEV P hP
  rw [← hS] at hQ
  have hdef : ∀ w ∈ coordinateLine d V₁, w ≠ 1 → form w.toAdd ≠ 0 := by
    intro w hw hne
    have hv := (mem_coordinateLine d V₁ w).mp hw
    have hn : (⟨d.coordinates.symm w,hv⟩ : V₁) ≠ 1 := by
      intro h
      apply hne
      have hvone : d.coordinates.symm w = 1 := Subtype.ext (congrArg (fun v : V₁ => (v : G)) h)
      have he := congrArg d.coordinates hvone
      simpa only [d.coordinates.apply_symm_apply, map_one] using he
    have hh := hV₁definite ⟨d.coordinates.symm w,hv⟩ hn
    change form (Multiplicative.toAdd (d.coordinates (d.coordinates.symm w))) ≠ 0 at hh
    simpa only [d.coordinates.apply_symm_apply] using hh
  obtain ⟨ho,hi,hk,hd⟩ := OrthogonalFourBinary.SylowGeometry.singular_line_sylow_geometry
    S (coordinateLine d E) (coordinateLine d V₁)
    ((coordinateLine_card d E hEV).trans hEcard) (coordinateLine_singular d E hEV hEsingular)
    ((coordinateLine_card d V₁ hV₁V).trans hV₁card) hdef Q hQ
  rw [hS] at ho hi hk hd
  have he : actionImage d (lineT (T : Subgroup G) E) =
      actionImage d (T : Subgroup G) ⊓ lineStabilizer (coordinateLine d E) :=
    actionImage_lineNormalizer d (T : Subgroup G) E hEV
  have ha : actionImage d (planeStabilizer T V₁) =
      actionImage d (T : Subgroup G) ⊓ lineStabilizer (coordinateLine d V₁) :=
    actionImage_lineNormalizer d (T : Subgroup G) V₁ hV₁V
  refine ⟨he.trans ho, ?_, he.symm ▸ hk, ?_⟩
  · rw [← lineT_actionImage_relIndex_of_E (T : Subgroup G) M V E d hTM hEV, he]
    exact hi
  · rwa [he,ha]


/-- Source 15.3.66(1)--(4) and the commutator used in 15.3.67. -/
theorem line_sylow_geometry_of_source (d : NaturalAction V M)
    (T : Sylow 2 G) (V₁ E : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (hV₁V : V₁ ≤ V) (hV₁card : Nat.card V₁ = 4)
    (hV₁definite : ∀ v : V₁, v ≠ 1 → ¬ d.singular ⟨v,hV₁V v.property⟩)
    (hEV : E ≤ V) (hEcard : Nat.card E = 4)
    (hEsingular : ∀ e : E, d.singular ⟨e,hEV e.property⟩)
    (hZV : centralInvolutions T = V ⊓ centralizer (T : Set G))
    (P : Sylow 2 (lineM M E))
    (hP : (P : Subgroup (lineM M E)).map (lineM M E).subtype =
      lineT (T : Subgroup G) E) :
    actionImage d (lineT (T : Subgroup G) E) =
        actionImage d (T : Subgroup G) ⊓ (OrthogonalFourBinary.omega :
          Subgroup OrthogonalFourBinary.IndexTwoNormalizer.IsometryGroup) ∧
      (lineT (T : Subgroup G) E).relIndex (T : Subgroup G) = 2 ∧
      IsKleinFour (actionImage d (lineT (T : Subgroup G) E)) ∧
      actionImage d (lineT (T : Subgroup G) E) ≠
        actionImage d (planeStabilizer T V₁) ∧
      centralInvolutions T ≤ E ∧
      ⁅V, (T : Subgroup G) ⊓ centralizer (E : Set G)⁆ = E := by
  obtain ⟨ho,hi,hk,hd⟩ := line_sylow_image_geometry d T V₁ E hTM
    hV₁V hV₁card hV₁definite hEV hEcard hEsingular P hP
  have hz : centralInvolutions T ≤ E := by
    rw [hZV]
    exact fixedSubgroup_le_singularLine d T E hTM hEV hEcard hEsingular P hP
  exact ⟨ho,hi,hk,hd,hz,
    singularLine_commutator_centralizer d T E hTM hEV hEcard hEsingular P hP⟩


end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal
