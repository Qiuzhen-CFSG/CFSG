module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PureEndpointInvolutions
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreSeedCoverage
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreCommutator
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedConjugateTypes
public import Theory.GroupTheory.KleinFourLines
public import Theory.GroupTheory.InvolutionCentralizerControl
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PureEndpointInvolutions

/-!
# The point-core line of an actual endpoint involution

An involution outside the endpoint radical is conjugate, inside that same
endpoint, into the opposite radical outside the common plane. Its point
core meets the plane in a line: the lower bound comes from the opposite
radical's point hyperplane, while reciprocal incidence rules out the
whole plane. The line transports back to the original involution and is
fixed by every element normalizing the radical and centralizing that
involution. The internal import-all edge reuses the original Sylow
conjugation and involution decomposition proofs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

omit [Finite G] in
private theorem point_core_map (e : G ≃* G) (r : G) :
    ((involutionCentralizer r).pCoreIn 2).map e.toMonoidHom =
      (involutionCentralizer (e r)).pCoreIn 2 := by
  rw [map_pCoreIn_of_injective 2 _ _ e.injective]
  congr 1
  simpa only [Set.image_singleton] using map_centralizer_equiv ({r} : Set G) e

private theorem opposite_point_core_card (h : TypeAt z V)
    (W A B : Subgroup G) [IsElementaryAbelian 2 B]
    (hWV : W ≤ V) (hW4 : Nat.card W = 4) (hWB : W ≤ B)
    (hWA : W ≤ A) (hB16 : Nat.card B = 16)
    (hBP : B ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (hpureB : ∀ b ∈ B, b ≠ 1 → IsConj b z)
    (hpointsB : ∀ b ∈ B, b ≠ 1 →
      Nat.card (B ⊓ (involutionCentralizer b).pCoreIn 2 : Subgroup G) = 8)
    (b : G) (hb : b ∈ B) (hbW : b ∉ W)
    (hfixed : A ⊓ involutionCentralizer b = W) :
    Nat.card (A ⊓ (involutionCentralizer b).pCoreIn 2 : Subgroup G) = 2 := by
  classical
  let Q := (involutionCentralizer b).pCoreIn 2
  let F := B ⊓ Q
  have hb1 : b ≠ 1 := fun he => hbW (he ▸ W.one_mem)
  obtain ⟨Vb,hbT⟩ := h.exists_typeAt_of_isConj b (hpureB b hb hb1)
  have hVcore : V ≤ (normalizer (V : Set G)).pCoreIn 2 := by
    change V ≤ (pCore 2 (normalizer (V : Set G))).map (normalizer (V : Set G)).subtype
    rw [← h.normalizer_fitting]
    exact h.seed_le_normalizer_core
  have hn : ¬ W ≤ Q := by
    intro hWQ
    let : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by rw [hW4]; decide)
    obtain ⟨w,hw⟩ := exists_ne (1 : W)
    obtain ⟨v,hv,hvw⟩ := ENat.exists_ne_ne_of_three_le (α := W)
      (by rw [ENat.card_eq_coe_natCard,hW4]; norm_num) 1 w
    have hw1 : (w : G) ≠ 1 := fun he => hw (Subtype.ext he)
    have hv1 : (v : G) ≠ 1 := fun he => hv (Subtype.ext he)
    have hvw' : (v : G) ≠ (w : G) := fun he => hvw (Subtype.ext he)
    have hwT := h.at_seed_point w (hWV w.property) hw1
    have hvT := h.at_seed_point v (hWV v.property) hv1
    have hbQw := hbT.centralizer_core_involution_reciprocal w (hWQ w.property) hwT.involution
    have hbQv := hbT.centralizer_core_involution_reciprocal v (hWQ v.property) hvT.involution
    have hbV : b ∈ V :=
      h.distinct_point_cores_intersection v w (hWV v.property) (hWV w.property)
        hv1 hw1 hvw' ▸ (show b ∈ (involutionCentralizer (v : G)).pCoreIn 2 ⊓
          (involutionCentralizer (w : G)).pCoreIn 2 from ⟨hbQv,hbQw⟩)
    exact hbW (hBP ▸ (show b ∈ B ⊓ (normalizer (V : Set G)).pCoreIn 2 from
      ⟨hb,hVcore hbV⟩))
  have hi : W ⊓ F = W ⊓ Q := by
    ext x
    exact ⟨fun hx => ⟨hx.1,hx.2.2⟩, fun hx => ⟨hx.1,hWB hx.1,hx.2⟩⟩
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes W F (by
    intro x hx
    apply centralizer_le_normalizer
    intro w hw
    exact setLike_mul_comm (hWB hw) hx.1)
  have hF8 : Nat.card F = 8 := hpointsB b hb hb1
  have hsup : Nat.card (W ⊔ F : Subgroup G) ≤ 16 :=
    hB16 ▸ card_le_of_le (sup_le hWB inf_le_left)
  rw [hW4,hF8,hi] at hprod
  have hlo : 2 ≤ Nat.card (W ⊓ Q : Subgroup G) := by nlinarith
  have hd : Nat.card (W ⊓ Q : Subgroup G) ∣ 4 :=
    hW4 ▸ card_dvd_of_le (show W ⊓ Q ≤ W from inf_le_left)
  have hle : Nat.card (W ⊓ Q : Subgroup G) ≤ 4 := Nat.le_of_dvd (by decide) hd
  have hne : Nat.card (W ⊓ Q : Subgroup G) ≠ 4 := by
    intro he
    have heq : W ⊓ Q = W := eq_of_le_of_card_ge inf_le_left (by rw [he,hW4])
    exact hn (heq ▸ (show W ⊓ Q ≤ Q from inf_le_right))
  have htwo : Nat.card (W ⊓ Q : Subgroup G) = 2 := by
    have hc : Nat.card (W ⊓ Q : Subgroup G) = 2 ∨ Nat.card (W ⊓ Q : Subgroup G) = 3 := by omega
    rcases hc with he | he
    · exact he
    · rw [he] at hd
      norm_num at hd
  have heq : A ⊓ Q = W ⊓ Q := by
    apply le_antisymm
    · intro x hx
      exact ⟨hfixed ▸ (show x ∈ A ⊓ involutionCentralizer b from
        ⟨hx.1,pCoreIn_le 2 _ hx.2⟩),hx.2⟩
    · exact inf_le_inf hWA le_rfl
  rwa [heq]

/-- The original point core of an endpoint involution outside its radical
meets that radical in exactly a line. The unique nonidentity point is
reciprocally incident with the involution and is fixed by the full joint
normalizer-centralizer, with all subgroups kept in the original group. -/
theorem TypeAt.endpoint_involution_point_core (h : TypeAt z V)
    (W A B : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hWV : W ≤ V) (hW4 : Nat.card W = 4) (hWA : W ≤ A) (hWB : W ≤ B)
    (hB16 : Nat.card B = 16) (hAC : A ≤ centralizer (W : Set G))
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (hBP : B ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (p : G) (hp : p ∈ (normalizer (V : Set G)).pCoreIn 2) (hpW : p ^ 2 ∉ W)
    (hB : B = A.map (MulAut.conj p).toMonoidHom)
    (hBA : B ≤ normalizer (A : Set G))
    (d : NaturalEndpointData A) (hBd : B ≤ d.carrier)
    (h64 : Nat.card (A ⊔ B : Subgroup G) = 64)
    (hpureB : ∀ b ∈ B, b ≠ 1 → IsConj b z)
    (hpointsB : ∀ b ∈ B, b ≠ 1 →
      Nat.card (B ⊓ (involutionCentralizer b).pCoreIn 2 : Subgroup G) = 8)
    (r : G) (hr : r ∈ d.carrier) (hrA : r ∉ A) (hr2 : orderOf r = 2) :
    Nat.card (A ⊓ (involutionCentralizer r).pCoreIn 2 : Subgroup G) = 2 ∧
    ∃ w ∈ A, orderOf w = 2 ∧ w ∈ (involutionCentralizer r).pCoreIn 2 ∧
      r ∈ (involutionCentralizer w).pCoreIn 2 ∧
      A ⊓ (involutionCentralizer r).pCoreIn 2 = zpowers w ∧
      ∀ v ∈ normalizer (A : Set G), Commute v r → Commute v w := by
  have hfixed (b : G) (hb : b ∈ B) (hbW : b ∉ W) : A ⊓ involutionCentralizer b = W :=
    h.paired_plane_radical_centralizer W A hWV hW4 hWA hAC hAP p hp hpW
      b (hB ▸ hb) hbW
  obtain ⟨g,hg⟩ := endpoint_involution_conjugate_sylow (A ⊔ B) d.carrier
    (sup_le d.kernel_le hBd) h64 d.carrier_card r hr hr2
  let e := MulAut.conj (g : G)
  have hr'2 : orderOf (e r) = 2 := (e.orderOf_eq r).trans hr2
  have hr'A : e r ∉ A := fun he => hrA ((mem_normalizer_iff.mp (d.normalizes g.property) r).mpr he)
  have hr'B : e r ∈ B := (join_involution_mem W A B hWB hWA hBA hfixed (e r) hg
    (hr'2 ▸ pow_orderOf_eq_one (e r))).resolve_left hr'A
  have hr'W : e r ∉ W := fun he => hr'A (hWA he)
  have hcard' := opposite_point_core_card h W A B hWV hW4 hWB hWA hB16 hBP
    hpureB hpointsB (e r) hr'B hr'W (hfixed (e r) hr'B hr'W)
  have hmap : (A ⊓ (involutionCentralizer r).pCoreIn 2).map e.toMonoidHom =
      A ⊓ (involutionCentralizer (e r)).pCoreIn 2 := by
    have hAe : A.map e.toMonoidHom = A :=
      mem_normalizer_iff_map_conj_eq.mp (d.normalizes g.property)
    rw [map_inf _ _ _ e.injective, point_core_map, hAe]
  have hcard : Nat.card (A ⊓ (involutionCentralizer r).pCoreIn 2 : Subgroup G) = 2 := by
    calc
      _ = Nat.card ((A ⊓ (involutionCentralizer r).pCoreIn 2).map e.toMonoidHom) :=
        (card_map_of_injective e.injective).symm
      _ = 2 := by rw [hmap]; exact hcard'
  have hr'z := hpureB (e r) hr'B (fun he => hr'W (he ▸ W.one_mem))
  have hrz : IsConj r z := (isConj_iff.mpr ⟨(g : G),rfl⟩).trans hr'z
  obtain ⟨Vr,hrT⟩ := h.exists_typeAt_of_isConj r hrz
  obtain ⟨w,hw,hw1,hwgen⟩ := exists_generator_of_card_two
    (A ⊓ (involutionCentralizer r).pCoreIn 2) hcard
  have hw2 : orderOf w = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw.1) hw1
  refine ⟨hcard,w,hw.1,hw2,hw.2,
    hrT.centralizer_core_involution_reciprocal w hw.2 hw2,hwgen.symm,?_⟩
  intro v hvA hvr
  have hvR : v ∈ involutionCentralizer r := mem_centralizer_singleton_iff.mpr hvr.eq
  have hvQ : v ∈ normalizer ((involutionCentralizer r).pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image (involutionCentralizer r)
      (pCore 2 (involutionCentralizer r)) ((involutionCentralizer r).le_normalizer hvR)
  have hvL := inf_normalizer_le_normalizer_inf ⟨hvA,hvQ⟩
  exact (normalizer_le_centralizer_of_card_two
    (A ⊓ (involutionCentralizer r).pCoreIn 2) hcard hvL w hw).symm

end CFSG.Quasithin.HigmanSims
