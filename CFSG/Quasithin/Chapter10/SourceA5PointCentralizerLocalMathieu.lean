module

public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerMarkedMathieu
public import CFSG.Quasithin.ChapterA.Section03.Basic
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.Mathieu.M22.Properties.LocalA5Placement

/-!
# The local M22 branch of the original A5 point centralizer

The original central image of L is a local C-component at a full Sylow of
I/Z(I). Its elementary two-core of order sixteen and A5 quotient determine
a marking of the native quintet actor. Transport through the same central
quotient, followed by marked involution rigidity, shows that the original U
centralizes I. The point-centralizer form keeps the original element v and
uses its normalizer containment to supply the action on I.

The local-component membership and E16:A5 structure remain the source inputs;
no independent marking or action-Sylow premise is required.

Source: Aschbacher--Smith A.3.12 and A.3.14, pp.47--49, and 10.2.9,
pp.750--751.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Sporadic.Mathieu MathieuCode Sporadic.Mathieu.M22ChapterH
namespace CFSG.Quasithin.Chapter10

private theorem local_component_map_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) {B S : Subgroup X}
    (hB : B ∈ ChapterA.Section03.localCComponents S) :
    B.map e.toMonoidHom ∈ ChapterA.Section03.localCComponents (S.map e.toMonoidHom) := by
  let H := B ⊔ S
  let J := B.map e.toMonoidHom ⊔ S.map e.toMonoidHom
  let eH : H ≃* J := (e.subgroupMap H).trans
    (MulEquiv.subgroupCongr (Subgroup.map_sup B S e.toMonoidHom))
  have hh := hB.map_equiv eH
  have hm : (B.subgroupOf H).map eH.toMonoidHom =
      (B.map e.toMonoidHom).subgroupOf J := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.val, hb, rfl⟩
    · rintro ⟨b, hb, hbx⟩
      exact ⟨⟨b, (show B ≤ H from le_sup_left) hb⟩, hb, Subtype.ext hbx⟩
  rw [hm] at hh
  exact hh

variable {G : Type*} [Group G] {L I U : Subgroup G}

/-- The actual central image admits a native marking from its local-component
membership and E16:A5 structure at a full quotient Sylow. -/
theorem source_a5_m22_local_image_exists_marking
    (eI : I ⧸ center I ≃* M22) (S : Sylow 2 (I ⧸ center I))
    (hB : (L.subgroupOf I).map (QuotientGroup.mk' (center I)) ∈
      ChapterA.Section03.localCComponents S)
    (hE : IsElementaryAbelian 2
      (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))))
    (h16 : Nat.card
      (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))) = 16)
    (eB : ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ⧸
      pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ≃*
      alternatingGroup (Fin 5)) :
    ∃ e : I ⧸ center I ≃* M22,
      Quintet.naturalActor.map M22Quintet.Q.subtype ≤
        (((L.subgroupOf I).map (QuotientGroup.mk' (center I))).map
          e.toMonoidHom).map m22ToPairStabilizer := by
  let B := ((L.subgroupOf I).map (QuotientGroup.mk' (center I))).map eI.toMonoidHom
  let : Finite (I ⧸ center I) := Finite.of_injective eI eI.injective
  let T := S.mapSurjective (f := eI.toMonoidHom) eI.surjective
  have hl : B ∈ ChapterA.Section03.localCComponents T := local_component_map_equiv eI hB
  let e := eI.subgroupMap ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))
  let ec : pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ≃*
      pCore 2 B :=
    (e.subgroupMap (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I))))).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  let : Group.IsPerfect B := by
    let := hl.perfect
    let h := subgroupOfEquivOfLe (show B ≤ B ⊔ (T : Subgroup M22) from le_sup_left)
    exact Group.IsPerfect.ofSurjective (f := h.toMonoidHom) h.surjective
  let : IsElementaryAbelian 2 (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))) := hE
  have he : IsElementaryAbelian 2 (pCore 2 B) :=
    IsElementaryAbelian.of_surjective ec.toMonoidHom ec.surjective
  have hc : Nat.card (pCore 2 B) = 16 := (Nat.card_congr ec.toEquiv).symm.trans h16
  let eq : ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ⧸
      pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ≃* B ⧸ pCore 2 B :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  obtain ⟨a, ha⟩ := Sporadic.Mathieu.M22LocalA5Placement.exists_marking
    T B hl.subnormal he hc (eq.symm.trans eB)
  refine ⟨eI.trans a, ?_⟩
  simpa only [B, MulEquiv.toMonoidHom_eq_coe, MulEquiv.coe_monoidHom_trans, map_map,
    MonoidHom.comp_assoc] using ha

/-- Local placement discharges the marking needed to centralize the original
perfect component, including the M22 central triple cover. -/
theorem source_a5_m22_local_component_centralized
    [Group.IsPerfect I] (eI : I ⧸ center I ≃* M22) (S : Sylow 2 (I ⧸ center I))
    (hB : (L.subgroupOf I).map (QuotientGroup.mk' (center I)) ∈
      ChapterA.Section03.localCComponents S)
    (hE : IsElementaryAbelian 2
      (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))))
    (h16 : Nat.card
      (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))) = 16)
    (eB : ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ⧸
      pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ≃*
      alternatingGroup (Fin 5))
    [IsElementaryAbelian 2 U]
    (hUN : U ≤ normalizer (I : Set G)) (hUL : U ≤ centralizer (L : Set G)) :
    U ≤ centralizer (I : Set G) := by
  obtain ⟨e, he⟩ := source_a5_m22_local_image_exists_marking eI S hB hE h16 eB
  exact source_a5_m22_marked_component_centralized e he hUN hUL

/-- The original point centralizer supplies normalization of I; the same U
then centralizes I without any additional embedding marking. -/
theorem source_a5_m22_local_point_component_centralized
    [Group.IsPerfect I] (eI : I ⧸ center I ≃* M22) (S : Sylow 2 (I ⧸ center I))
    (hB : (L.subgroupOf I).map (QuotientGroup.mk' (center I)) ∈
      ChapterA.Section03.localCComponents S)
    (hE : IsElementaryAbelian 2
      (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))))
    (h16 : Nat.card
      (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))) = 16)
    (eB : ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ⧸
      pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ≃*
      alternatingGroup (Fin 5))
    [IsElementaryAbelian 2 U]
    (v : G) (hUv : U ≤ centralizer ({v} : Set G))
    (hIN : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hUL : U ≤ centralizer (L : Set G)) : U ≤ centralizer (I : Set G) :=
  source_a5_m22_local_component_centralized eI S hB hE h16 eB (hUv.trans hIN) hUL

/-- The original local producer supplies a Sylow subgroup of the actual
component `I`. Mapping that literal Sylow through `I/Z(I)` supplies the
quotient-level local input required by the M22 placement theorem. -/
theorem source_a5_m22_local_component_centralized_of_original
    [Group.IsPerfect I] [Finite I]
    (eI : I ⧸ center I ≃* M22) (S : Sylow 2 I)
    (hB : L.subgroupOf I ∈ ChapterA.Section03.localCComponents S)
    (hE : IsElementaryAbelian 2
      (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))))
    (h16 : Nat.card
      (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))) = 16)
    (eB : ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ⧸
      pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ≃*
      alternatingGroup (Fin 5))
    [IsElementaryAbelian 2 U]
    (hUN : U ≤ normalizer (I : Set G)) (hUL : U ≤ centralizer (L : Set G)) :
    U ≤ centralizer (I : Set G) := by
  let q := QuotientGroup.mk' (center I)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm
      (fun x y => (IsMulCommutative.is_comm (M := center I)).comm x y)
  let Sbar := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective (center I))
  have hBbar : (L.subgroupOf I).map q ∈
      ChapterA.Section03.localCComponents (Sbar : Subgroup (I ⧸ center I)) := by
    exact Chapter1.Section02.localCComponents_map_of_solvable_ker hB q
  exact source_a5_m22_local_component_centralized eI Sbar hBbar hE h16 eB hUN hUL

/-- Point-centralizer version of the original-Sylow endpoint. -/
theorem source_a5_m22_local_point_component_centralized_of_original
    [Group.IsPerfect I] [Finite I]
    (eI : I ⧸ center I ≃* M22) (S : Sylow 2 I)
    (hB : L.subgroupOf I ∈ ChapterA.Section03.localCComponents S)
    (hE : IsElementaryAbelian 2
      (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))))
    (h16 : Nat.card
      (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))) = 16)
    (eB : ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ⧸
      pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ≃*
      alternatingGroup (Fin 5))
    [IsElementaryAbelian 2 U]
    (v : G) (hUv : U ≤ centralizer ({v} : Set G))
    (hIN : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hUL : U ≤ centralizer (L : Set G)) : U ≤ centralizer (I : Set G) :=
  source_a5_m22_local_component_centralized_of_original
    eI S hB hE h16 eB (hUv.trans hIN) hUL

end CFSG.Quasithin.Chapter10
