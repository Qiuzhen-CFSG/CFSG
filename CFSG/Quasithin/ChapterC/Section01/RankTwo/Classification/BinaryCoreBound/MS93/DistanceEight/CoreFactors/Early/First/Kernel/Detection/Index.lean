module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Kernel.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Layer.Displacement

/-!
# The small kernel image in MS93 (4.5.1)

The radius group lies in the edge kernel five steps along the path. Its
image modulo the next vertex kernel has order at most four. If that image
had order four, it would cover the edge quotient, so its displacement on
the next Z-layer would be the full edge displacement of order four.
Clause (i) bounds that displacement by a radius commutator of order two.
This proves the index bound needed for endpoint detection in clause (iii).

Source: Meierfrankenfeld--Stellmacher (1993), (4.4) and (4.5.1),
printed pp.895--896.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Kernel.Detection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem sup_eq_of_index_four {G : Type*} [Group G]
    {A K T : Subgroup G} (hA : A ≤ T) (hK : K ≤ T)
    (hn : T ≤ normalizer (K : Set G))
    (hi : K.relIndex T = 4) (hlarge : 2 < K.relIndex A) : A ⊔ K = T := by
  let A₀ := A.subgroupOf T
  let K₀ := K.subgroupOf T
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer hn
  have hfour : K₀.relIndex A₀ = 4 := by
    have hKi : K₀.index = 4 := hi
    have hdvd : K₀.relIndex A₀ ∣ 4 := hKi ▸ K₀.relIndex_dvd_index_of_normal A₀
    have hh := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 4 ≠ 0)⟩
    rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    have hgt : 2 < K₀.relIndex A₀ := by rwa [relIndex_subgroupOf hA]
    omega
  have hm := relIndex_mul_index (show K₀ ≤ A₀ ⊔ K₀ from le_sup_right)
  rw [relIndex_sup_right, hfour, show K₀.index = 4 from hi] at hm
  have he : A₀ ⊔ K₀ = ⊤ := index_eq_one.mp (by omega)
  have hh := congrArg (Subgroup.map T.subtype) he
  simpa only [A₀, K₀, Subgroup.map_sup, map_subgroupOf_eq_of_le hA,
    map_subgroupOf_eq_of_le hK, ← MonoidHom.range_eq_map, range_subtype] using hh

/-- The order-two radius commutator excludes the full edge image of order four. -/
theorem radius_kernel_index_le_two (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a d e t : Vertex R}
    (ha : color R a = false) (he : color R e = false) (het : Adjacent R e t)
    (hat : (cosetGraph R).dist a t = 5)
    (hed : (cosetGraph R).dist e d ≤ 2)
    (hcomm : Nat.card (⁅V R a, V R d⁆ : Subgroup (FreeAmalgam R)) = 2) :
    (Q R e).relIndex (V R a) ≤ 2 := by
  have hA : V R a ≤ Q R t := PathCentrality.V_le_Q_of_dist_add_two_lt R ha
    (by rw [hat, earlier.distance]; decide)
  have ht : color R t = true := by
    have hn := adjacent_color_ne R het
    cases h : color R t <;> simp_all
  have hK : Q R e ≤ Q R t := Q_le_adjacent_h R ht het
  have hlocal : Q R t ≤ stabilizer R e := fun _ hx => hx.2 e (adjacent_symm R het)
  by_contra! hlarge
  have hsup := sup_eq_of_index_four hA hK (hlocal.trans (Q_normalized R e))
    (earlier.edge_Q_index e t he het) hlarge
  have hreduce := commutator_eq_of_centralizing_sup (sup_comm _ _ |>.trans hsup)
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes e he))) (hA.trans (hlocal.trans (Z_normalized R e)))
  have hZV : Z R e ≤ V R d := le_iSup_of_le e (le_iSup_of_le hed le_rfl)
  have hbound : ⁅Z R e, Q R t⁆ ≤ ⁅V R a, V R d⁆ := by
    rw [← hreduce, commutator_comm]
    exact commutator_mono le_rfl hZV
  let : Finite (⁅V R a, V R d⁆ : Subgroup (FreeAmalgam R)) :=
    Nat.finite_of_card_ne_zero (by rw [hcomm]; decide)
  have hc := card_le_of_le hbound
  rw [Layer.edge_displacement_card common earlier he het, hcomm] at hc
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First.Kernel.Detection
