module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Layer.SourceAdapters

/-!
# Evaluating a subgroup of the edge action

The fixed subgroup of an edge kernel has index two in Z_d. Every nontrivial
subaction has the same fixed subgroup. Its displacement is fixed by the edge
kernel, so evaluation outside that subgroup identifies the faithful action
index with the order of its commutator. The actual edge centralizer identifies
the kernel with Q_d. This handles the fixed central summand of Z_d directly.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.1)(iv), pp.895--896.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Layer
open PathCentrality PathCentrality.LocalCommutator
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem eq_of_index_two {G : Type*} [Group G] {N F U : Subgroup G}
    (hNF : N ≤ F) (hFU : F ≤ U) (hi : N.relIndex U = 2) (hne : F ≠ U) : F = N := by
  have hm := relIndex_mul_relIndex N F U hNF hFU
  rw [hi] at hm
  have hdiv : F.relIndex U ∣ 2 := ⟨N.relIndex F, by simpa only [Nat.mul_comm] using hm.symm⟩
  have hidx : F.relIndex U = 2 := ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
    (fun h => hne (le_antisymm hFU (relIndex_eq_one.mp h)))
  rw [hidx] at hm
  exact le_antisymm (relIndex_eq_one.mp (by omega)) hNF

/-- The faithful image of any nontrivial edge subaction has the same order
as its actual displacement, including the full Z-layer. -/
theorem edge_image_eq_displacement_card (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {d t : Vertex R}
    (hd : color R d = false) (hdt : Adjacent R d t)
    {P : Subgroup (FreeAmalgam R)} (hP : P ≤ Q R t)
    (hne : ⁅Z R d, P⁆ ≠ ⊥) :
    (Q R d).relIndex P = Nat.card (⁅Z R d, P⁆ : Subgroup (FreeAmalgam R)) := by
  have heq := Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance
    (moduleFacts common) d t hd hdt
  have hfix : Z R d ⊓ centralizer (P : Set (FreeAmalgam R)) = Z R t := by
    apply eq_of_index_two
      (show Z R t ≤ Z R d ⊓ centralizer (P : Set (FreeAmalgam R)) from
        heq ▸ le_inf inf_le_left (inf_le_right.trans (centralizer_le hP))) inf_le_left
      (earlier.edge_Z_index d t hd hdt)
    intro h
    apply hne
    exact commutator_eq_bot_iff_le_centralizer.mpr (h.ge.trans inf_le_right)
  have hi : (Z R d ⊓ centralizer (P : Set (FreeAmalgam R))).relIndex (Z R d) = 2 := by
    rw [hfix]
    exact earlier.edge_Z_index d t hd hdt
  have hlocal : Q R t ≤ stabilizer R d := fun _ hx => hx.2 d (adjacent_symm R hdt)
  have hn := hP.trans (hlocal.trans (Z_normalized R d))
  have hF : P ≤ normalizer (Z R d ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    (le_centralizer_iff.mp (show Z R d ⊓ centralizer (P : Set (FreeAmalgam R)) ≤
      centralizer (P : Set (FreeAmalgam R)) from inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  have hcomm := commutator_le_of_normalized_index_two _ _ P inf_le_left hi hn hF
  let := geometry.Z_elementary (by rw [earlier.distance]; decide) d hd
  have hindex := DistanceFour.Early.actor_index_eq_displacement_card_of_fixed_index_two
    (Z R d) P hn (hcomm.trans inf_le_right) hi
  have hker : (centralizer (Z R d : Set (FreeAmalgam R))).subgroupOf P = (Q R d).subgroupOf P := by
    ext x
    change (x : FreeAmalgam R) ∈ centralizer (Z R d : Set (FreeAmalgam R)) ↔ (x : FreeAmalgam R) ∈ Q R d
    constructor
    · intro hx
      rw [← common.centralizer d t hd hdt]
      exact ⟨hP x.property, hx⟩
    · intro hx
      exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hd)) hx
  change ((Q R d).subgroupOf P).index = _
  rw [← hker]
  exact hindex

/-- Order at least four for the nested displacement fills the literal
edge quotient. No small-image or representation premise remains. -/
theorem hatW_product_of_displacement_lower (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c d t : Vertex R}
    (ha : color R a = false) (hd : color R d = false) (hdt : Adjacent R d t)
    (hca : (cosetGraph R).dist c a ≤ 2) (hdc : (cosetGraph R).dist d c ≤ 2)
    (hat : (cosetGraph R).dist a t = 3)
    (hfour : 4 ≤ Nat.card (⁅hatW R a c d, Z R d⁆ : Subgroup (FreeAmalgam R))) :
    (hatW R a c d : Set (FreeAmalgam R)) * (Q R d : Set (FreeAmalgam R)) =
      (Q R t : Set (FreeAmalgam R)) := by
  have hn : ⁅Z R d, hatW R a c d⁆ ≠ ⊥ := by
    intro h
    rw [commutator_comm, h] at hfour
    simp only [Subgroup.card_bot] at hfour
    omega
  have hindex := edge_image_eq_displacement_card common earlier hd hdt
    (hatW_le_edge_kernel earlier ha hca hdc hat) hn
  apply hatW_product_of_large_image earlier ha hd hdt hca hdc hat
  rw [hindex, commutator_comm]
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Layer
