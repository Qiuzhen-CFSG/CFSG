module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.Basic
public import Mathlib.GroupTheory.Frattini
public import Theory.Representation.PSL3Two.SteinbergStructure.LocalActions

/-!
# Commutator generation and actual containment of the original S

The Steinberg point-parabolic displacement formulas make the image of [S,L]
all of S/V. Since V = Φ(S), Frattini nongeneration gives [S,L] = S.
The earlier S ≤ Q and 14.7.71(3) then give S = [Q,L]. As T normalizes L,
this commutator lies in L. Normality and the two-group property now give
S ≤ O₂(L), and the same commutator comparison gives [O₂(L),L] = S.

All coordinates use the original SourceMarking.qL. No containment in an
actor is inferred from normalization alone. The final equality S = O₂(L)
requires the separate source involution argument.

Source: Aschbacher–Smith, proof of 14.7.72, printed p.1076 (PDF p.1093),
combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

private theorem coordinates_commutator_onto (c : SteinbergCoordinates d) :
    ((⁅S F L,L⁆).subgroupOf (S F L)).map
      (N := Multiplicative BinaryLinearThree.Steinberg) c.coordinates = ⊤ := by
  let C := (⁅S F L,L⁆).subgroupOf (S F L)
  let X : Submodule (ZMod 2) BinaryLinearThree.Steinberg :=
    AddSubgroup.toZModSubmodule 2 (C.map c.coordinates).toAddSubgroup'
  have hdisp (g : BinaryLinearThree.Group) (v : BinaryLinearThree.Steinberg) :
      BinaryLinearThree.S g v - v ∈ X := by
    obtain ⟨l, rfl⟩ := d.qL_surjective g
    obtain ⟨a, ha⟩ := c.onto (Multiplicative.ofAdd v)
    let b : S F L := ⟨l * a * (l : G)⁻¹,
      (mem_normalizer_iff.mp (L_normalizes_S l.property) a).mp a.property⟩
    change Multiplicative.ofAdd (BinaryLinearThree.S (d.qL l) v - v) ∈ C.map c.coordinates
    refine ⟨b * a⁻¹, ?_, ?_⟩
    · change (l : G) * a * (l : G)⁻¹ * (a : G)⁻¹ ∈ ⁅S F L,L⁆
      rw [commutator_comm]
      exact commutator_mem_commutator l.property a.property
    · apply Multiplicative.toAdd.injective
      rw [map_mul, map_inv]
      simp only [toAdd_mul, toAdd_inv,
        toAdd_ofAdd, ← sub_eq_add_neg]
      rw [c.equivariant l a, ha]
      rfl
  have hX : X = ⊤ := by
    apply top_unique
    rw [← BinaryLinearThree.SteinbergStructure.LocalActions.point_commutator_eq_top]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, _, rfl⟩
    exact hdisp g v
  apply top_unique
  intro v _
  have hv : v.toAdd ∈ X := by rw [hX]; trivial
  exact hv

theorem S_commutator_L_eq (c : SteinbergCoordinates d)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V) :
    ⁅S F L,L⁆ = S F L := by
  have hCS : ⁅S F L,L⁆ ≤ S F L :=
    le_normalizer_iff_commutator_le_left.mp L_normalizes_S
  let C := (⁅S F L,L⁆).subgroupOf (S F L)
  have hPhi' : frattini (S F L) = V.subgroupOf (S F L) := by
    have he := congrArg (fun A : Subgroup G => A.subgroupOf (S F L)) hPhi
    simpa only [subgroupOf, comap_map_eq_self_of_injective (S F L).subtype_injective] using he
  have htop : C ⊔ frattini (S F L) = ⊤ := by
    rw [hPhi', ← c.kernel_eq]
    apply top_unique
    intro a _
    have ha : c.coordinates a ∈ C.map c.coordinates := by
      rw [coordinates_commutator_onto d c]
      trivial
    obtain ⟨b, hb, he⟩ := ha
    have hba : b⁻¹ * a ∈ c.coordinates.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he]
      exact inv_mul_cancel (c.coordinates a)
    have hh := (C ⊔ c.coordinates.ker).mul_mem (mem_sup_left hb) (mem_sup_right hba)
    simpa only [mul_inv_cancel_left] using hh
  have hC := frattini_nongenerating htop
  apply le_antisymm hCS
  intro a ha
  have hh : (⟨a,ha⟩ : S F L) ∈ C := by rw [hC]; trivial
  exact hh

theorem S_eq_commutator_Q_L (c : SteinbergCoordinates d)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V)
    (hSQ : S F L ≤ Q T L) (h71 : ⁅Q T L,L⁆ ≤ S F L) :
    S F L = ⁅Q T L,L⁆ := by
  apply le_antisymm ?_ h71
  rw [← S_commutator_L_eq d c hPhi]
  exact commutator_mono hSQ le_rfl

theorem S_le_L (c : SteinbergCoordinates d)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V)
    (hSQ : S F L ≤ Q T L) (h71 : ⁅Q T L,L⁆ ≤ S F L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) : S F L ≤ L := by
  rw [S_eq_commutator_Q_L d c hPhi hSQ h71, commutator_comm]
  apply le_normalizer_iff_commutator_le_left.mp
  exact (pCoreIn_le 2 (L ⊔ (T : Subgroup G))).trans (sup_le L.le_normalizer hTL)

theorem S_le_core (c : SteinbergCoordinates d)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V)
    (hSQ : S F L ≤ Q T L) (h71 : ⁅Q T L,L⁆ ≤ S F L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) : S F L ≤ L.pCoreIn 2 := by
  exact le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 _).to_le hSQ)
    (S_le_L d c hPhi hSQ h71 hTL) L_normalizes_S

theorem core_commutator_eq_S (c : SteinbergCoordinates d)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V)
    (hSQ : S F L ≤ Q T L) (h71 : ⁅Q T L,L⁆ ≤ S F L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) : ⁅L.pCoreIn 2,L⁆ = S F L := by
  have hcoreQ : L.pCoreIn 2 ≤ Q T L := by
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
      ((pCoreIn_le 2 L).trans le_sup_left)
    exact (sup_le L.le_normalizer hTL).trans
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  apply le_antisymm ((commutator_mono hcoreQ le_rfl).trans h71)
  rw [← S_commutator_L_eq d c hPhi]
  exact commutator_mono (S_le_core d c hPhi hSQ h71 hTL) le_rfl
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification
