module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.PlaneFusion
public import Theory.GroupTheory.NormalizerClassOrbitCard
public import Theory.GroupTheory.PairNormalizerIndex
/-!
# Orders of the full ambient plane normalizers

A root plane meets the original minus-extraspecial core in exactly E.
Consequently its normalizer's stabilizer of z lies in N_G(R). The latter
stabilizer has order 384 and interchanges the two planes, giving plane-point
stabilizer order 192. The proved fusion control and the one-class hypothesis
then give |N_G(A)| = 15·192 = 2880.

The literal common root/plane stabilizer has order 576, hence index five in
the full plane normalizer. These are the numerical and permutation-action
inputs in 46.14(5a); identifying the quotient and splitting its natural
extension are separate subsequent steps.

Source: Aschbacher, *Sporadic Groups* (1994), 46.14(5a), pp.257–258.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.HyperbolicRecognition
namespace CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
open Matrix.PSL3Four
variable {G : Type*} [Group G] [Finite G] {D : Seed G}
namespace ReturningPair
variable (P : ReturningPair D)

private theorem involution_class_card (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] :
    Nat.card {a : A // IsConj D.z (a : G)} = Nat.card A - 1 := by
  classical
  have hh (a : A) : IsConj D.z (a : G) ↔ a ≠ 1 := by
    constructor
    · intro h ha
      have hz : D.z = 1 := isConj_one_left.mp (by simpa [ha] using h)
      have ho := D.localType.involution
      rw [hz,orderOf_one] at ho
      omega
    · intro ha
      apply hclass.isConj _ D.localType.involution
      exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (a : G) a.property)
        (fun h => ha (Subtype.ext h))
  rw [Nat.card_congr (Equiv.subtypeEquivRight hh)]
  let : Fintype A := Fintype.ofFinite A
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,Fintype.card_unique]

/-- The exact intersection with the original minus-extraspecial core. -/
theorem plane_inf_core (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAR : A ≤ P.R) (hEA : P.E ≤ A) : A ⊓ ambientCore D.z = P.E := by
  apply le_antisymm
  · rintro x ⟨hxA,hxQ⟩
    apply (Geometry.Coordinates.leftCore_square_eq_one_iff P (P.R_inf_core ▸ ⟨hAR hxA,hxQ⟩)).mp
    exact elemPow_eq_one_of_isElementaryAbelian x hxA
  · exact le_inf hEA P.E_le_core

/-- A plane stabilizer fixing z must preserve its intersection E with the characteristic core. -/
theorem plane_point_stabilizer_le_root_normalizer (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAR : A ≤ P.R) (hEA : P.E ≤ A) :
    normalizer (A : Set G) ⊓ centralizer ({D.z} : Set G) ≤ normalizer (P.R : Set G) := by
  intro a ha
  have hQ : a ∈ normalizer (ambientCore D.z : Set G) :=
    D.localType.normalizer_core.symm ▸ ha.2
  have hE : a ∈ normalizer (P.E : Set G) := by
    rw [←P.plane_inf_core A hAR hEA]
    exact inf_normalizer_le_normalizer_inf ⟨ha.1,hQ⟩
  exact Geometry.Coordinates.normalizer_E_eq_normalizer_R P ▸ hE

/-- The root-normalizer stabilizer of z has order 384. -/
theorem root_point_stabilizer_card (hclass : OneInvolutionClass G) :
    Nat.card (normalizer (P.R : Set G) ⊓ centralizer ({D.z} : Set G) : Subgroup G) = 384 := by
  let : IsElementaryAbelian 2 P.E := P.E_elementary
  have ht : ∀ y ∈ P.E, IsConj D.z y →
      ∃ n ∈ normalizer (P.E : Set G), MulAut.conj n D.z = y := by
    intro y hy hzy
    have hy1 : y ≠ 1 := by
      intro hh
      have hz : D.z = 1 := isConj_one_left.mp (hh ▸ hzy)
      have ho := D.localType.involution
      rw [hz,orderOf_one] at ho
      omega
    have hz1 : D.z ≠ 1 := by
      intro hh
      have ho := D.localType.involution
      rw [hh,orderOf_one] at ho
      omega
    obtain ⟨a,ha⟩ := Geometry.Coordinates.centerTransitive P D.z P.z_mem_E hz1 y hy hy1
    exact ⟨a, (Geometry.Coordinates.normalizer_E_eq_normalizer_R P).symm ▸ a.property,ha⟩
  have hh := card_normalizer_of_class_transitive P.E D.z P.z_mem_E ht
  rw [involution_class_card (D := D) hclass P.E,P.E_card,
    Geometry.Coordinates.normalizer_E_eq_normalizer_R P,Geometry.Normalizer.normalizer_R_card P] at hh
  omega

private theorem plane_point_stabilizer_card_aux (hclass : OneInvolutionClass G)
    (A B : Subgroup G) [IsElementaryAbelian 2 A]
    (hAR : A ≤ P.R) (hEA : P.E ≤ A) (hne : A ≠ B)
    (hpair : ∀ a ∈ normalizer (P.R : Set G),
      A.conjBy a = A ∨ A.conjBy a = B)
    (hswap : ∃ c ∈ centralizer ({D.z} : Set G),
      c ∈ normalizer (P.R : Set G) ∧ A.conjBy c = B) :
    Nat.card (normalizer (A : Set G) ⊓ centralizer ({D.z} : Set G) : Subgroup G) = 192 := by
  let L := normalizer (P.R : Set G) ⊓ centralizer ({D.z} : Set G)
  obtain ⟨c,hcz,hcN,hc⟩ := hswap
  have hi : (normalizer (A : Set G)).relIndex L = 2 :=
    normalizer_relIndex_eq_two_of_pair L A B (fun n hn => hpair n hn.1)
      c ⟨hcN,hcz⟩ (fun he => hne (he.symm.trans hc))
  have heq : normalizer (A : Set G) ⊓ L =
      normalizer (A : Set G) ⊓ centralizer ({D.z} : Set G) := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
    · exact le_inf inf_le_left (le_inf (P.plane_point_stabilizer_le_root_normalizer A hAR hEA) inf_le_right)
  have hh := ((normalizer (A : Set G)).subgroupOf L).card_mul_index
  have hk : Nat.card ((normalizer (A : Set G)).subgroupOf L) =
      Nat.card (normalizer (A : Set G) ⊓ centralizer ({D.z} : Set G) : Subgroup G) := by
    rw [←inf_subgroupOf_right,Nat.card_congr (subgroupOfEquivOfLe
      (show normalizer (A : Set G) ⊓ L ≤ L from inf_le_right)).toEquiv,heq]
  rw [hk] at hh
  change Nat.card (normalizer (A : Set G) ⊓ centralizer ({D.z} : Set G) : Subgroup G) *
    (normalizer (A : Set G)).relIndex L = Nat.card L at hh
  rw [hi,show Nat.card L = 384 from P.root_point_stabilizer_card hclass] at hh
  omega

/-- The full normalizer of an actual root plane has order 2880. -/
theorem plane_normalizer_card (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    Nat.card (normalizer (A : Set G)) = 2880 := by
  obtain ⟨d,f,hf⟩ := Geometry.Normalizer.exists_identification P
  have hEA : P.E ≤ A := by
    rcases (P.elementary_sixteen_iff d A hAR).mp ⟨inferInstance,hA⟩ with rfl | rfl
    · rw [←P.planes_inf d]; exact inf_le_left
    · rw [←P.planes_inf d]; exact inf_le_right
  have hpair (U : Subgroup G) [IsElementaryAbelian 2 U] (hU : Nat.card U = 16)
      (hUR : U ≤ P.R) (a : G) (ha : a ∈ normalizer (P.R : Set G)) :
      U.conjBy a = P.A₁ d ∨ U.conjBy a = P.A₂ d := by
    let : IsElementaryAbelian 2 (U.conjBy a) := IsElementaryAbelian.map _
    have hc : Nat.card (U.conjBy a) = 16 := (card_map_of_injective (MulAut.conj a).injective).trans hU
    have hm : U.conjBy a ≤ P.R := by
      have hh := map_mono (f := (MulAut.conj a).toMonoidHom) hUR
      have he : P.R.map (MulAut.conj a).toMonoidHom = P.R := mem_normalizer_iff_map_conj_eq.mp ha
      rwa [he] at hh
    exact (P.elementary_sixteen_iff d _ hm).mp ⟨inferInstance,hc⟩
  have hpoint : Nat.card (normalizer (A : Set G) ⊓ centralizer ({D.z} : Set G) : Subgroup G) = 192 := by
    obtain ⟨c,hcz,hcN,hc1,hc2⟩ := P.exchange_marked_planes d f hf D.z P.z_mem_E
    rcases (P.elementary_sixteen_iff d A hAR).mp ⟨inferInstance,hA⟩ with rfl | rfl
    · exact P.plane_point_stabilizer_card_aux hclass _ _ (P.A₁_le_R d) hEA
        (P.planes_ne d) (hpair _ (P.A₁_card d) (P.A₁_le_R d)) ⟨c,hcz,hcN,hc1⟩
    · exact P.plane_point_stabilizer_card_aux hclass _ _ (P.A₂_le_R d) hEA
        (P.planes_ne d).symm (fun a ha => (hpair _ (P.A₂_card d) (P.A₂_le_R d) a ha).symm)
        ⟨c,hcz,hcN,hc2⟩
  have hh := card_normalizer_of_class_transitive A D.z (hEA P.z_mem_E)
    (fun y hy hzy => P.elementary_sixteen_normalizer_fusion hclass A hA D.z y (hEA P.z_mem_E) hy hzy)
  rw [involution_class_card (D := D) hclass A,hA,hpoint] at hh
  omega

/-- The root normalizer interchanges the two planes, so each plane stabilizer has index two. -/
theorem plane_stabilizer_index_in_root_normalizer
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    (normalizer (A : Set G)).relIndex (normalizer (P.R : Set G)) = 2 := by
  obtain ⟨d,f,hf⟩ := Geometry.Normalizer.exists_identification P
  have hpair (U : Subgroup G) [IsElementaryAbelian 2 U] (hU : Nat.card U = 16)
      (hUR : U ≤ P.R) (a : G) (ha : a ∈ normalizer (P.R : Set G)) :
      U.conjBy a = P.A₁ d ∨ U.conjBy a = P.A₂ d := by
    let : IsElementaryAbelian 2 (U.conjBy a) := IsElementaryAbelian.map _
    have hm : U.conjBy a ≤ P.R := by
      have hh := map_mono (f := (MulAut.conj a).toMonoidHom) hUR
      have he : P.R.map (MulAut.conj a).toMonoidHom = P.R := mem_normalizer_iff_map_conj_eq.mp ha
      rwa [he] at hh
    exact (P.elementary_sixteen_iff d _ hm).mp
      ⟨inferInstance,(card_map_of_injective (MulAut.conj a).injective).trans hU⟩
  obtain ⟨c,_,hcN,hc1,hc2⟩ := P.exchange_marked_planes d f hf 1 P.E.one_mem
  rcases (P.elementary_sixteen_iff d A hAR).mp ⟨inferInstance,hA⟩ with rfl | rfl
  · exact normalizer_relIndex_eq_two_of_pair _ _ _
      (hpair _ (P.A₁_card d) (P.A₁_le_R d)) c hcN
      (fun he => P.planes_ne d (he.symm.trans hc1))
  · exact normalizer_relIndex_eq_two_of_pair _ _ _
      (fun a ha => (hpair _ (P.A₂_card d) (P.A₂_le_R d) a ha).symm) c hcN
      (fun he => P.planes_ne d (hc2.symm.trans he))

/-- The literal common stabilizer has order 576. -/
theorem plane_root_stabilizer_card
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    Nat.card (normalizer (A : Set G) ⊓ normalizer (P.R : Set G) : Subgroup G) = 576 := by
  let N := normalizer (P.R : Set G)
  have hh := ((normalizer (A : Set G)).subgroupOf N).card_mul_index
  have hc : Nat.card ((normalizer (A : Set G)).subgroupOf N) =
      Nat.card (normalizer (A : Set G) ⊓ N : Subgroup G) := by
    rw [←inf_subgroupOf_right,Nat.card_congr (subgroupOfEquivOfLe
      (show normalizer (A : Set G) ⊓ N ≤ N from inf_le_right)).toEquiv]
  rw [hc] at hh
  change Nat.card (normalizer (A : Set G) ⊓ N : Subgroup G) *
    (normalizer (A : Set G)).relIndex N = Nat.card N at hh
  rw [P.plane_stabilizer_index_in_root_normalizer A hA hAR,
    Geometry.Normalizer.normalizer_R_card P] at hh
  dsimp only [N] at hh
  omega

/-- The action used in 46.14(5a) is on five cosets of the actual root stabilizer. -/
theorem root_stabilizer_index_in_plane_normalizer (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    (normalizer (P.R : Set G)).relIndex (normalizer (A : Set G)) = 5 := by
  let N := normalizer (A : Set G)
  have hh := ((normalizer (P.R : Set G)).subgroupOf N).card_mul_index
  have hc : Nat.card ((normalizer (P.R : Set G)).subgroupOf N) = 576 := by
    rw [←inf_subgroupOf_right,Nat.card_congr (subgroupOfEquivOfLe
      (show normalizer (P.R : Set G) ⊓ N ≤ N from inf_le_right)).toEquiv,inf_comm]
    exact P.plane_root_stabilizer_card A hA hAR
  rw [hc] at hh
  change 576 * (normalizer (P.R : Set G)).relIndex N = Nat.card N at hh
  rw [P.plane_normalizer_card hclass A hA hAR] at hh
  dsimp only [N] at hh
  omega
end ReturningPair
end CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
