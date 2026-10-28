module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Structure
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Context
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.NormalizerControl.Geometry
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.NormalizerControl.SquareObstruction.LocalOrbits
public import Theory.GroupTheory.SaturatedInvolutionSquareFusion

/-!
# Seven-divisibility excludes an outside square in the second Held model

Let H be the actual involution centralizer, identified with the second model,
and let N normalize the embedded elementary subgroup F of order sixteen.
If seven divides |N|, the orbit of the original central involution has length
seven: its stabilizer is H of order 384, its orbit has at most fifteen points,
and its length is odd because H contains the original ambient Sylow subgroup.
The eight points outside V lie in one local orbit. The N-orbit containing
them is disjoint from the seven-point orbit and therefore has length eight.
Consequently the outside involution x has centralizer in N of order 336.

The p-group normalizer condition now makes F Sylow in the full ambient
centralizer of x. Any square root of x could be conjugated into F inside that
centralizer, contradicting exponent two. Simplicity is not used. The explicit
seven-divisibility premise must be discharged by the normalizer-control assembly;
this module does not assume exceptional action, splitting, or recognition.

Source problem: Huppert--Blackburn, *Finite Groups III*, XII.1.18(b),
printed p.314 / PDF p.322; D. Held, J. Algebra 8 (1968), 436–449.
This is an auxiliary argument toward splitting, not the source theorem itself.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl.SquareObstruction
open NonsplitModels Model

set_option maxRecDepth 100000

variable {G : Type*} [Group G]

private def relativeOrbit (N : Subgroup G) (x : G) : Set G :=
  {y | ∃ g ∈ N, g * x * g⁻¹ = y}

private theorem mem_relativeOrbit (N : Subgroup G) (x : G) : x ∈ relativeOrbit N x :=
  ⟨1, N.one_mem, by simp⟩

private theorem relativeOrbit_eq_of_mem {N : Subgroup G} {x y : G}
    (hy : y ∈ relativeOrbit N x) : relativeOrbit N y = relativeOrbit N x := by
  obtain ⟨a, ha, rfl⟩ := hy
  ext z
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b * a, N.mul_mem hb ha, by group⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b * a⁻¹, N.mul_mem hb (N.inv_mem ha), by group⟩

private theorem relativeOrbit_nonidentity {N : Subgroup G} {x y : G}
    (hx : x ≠ 1) (hy : y ∈ relativeOrbit N x) : y ≠ 1 := by
  obtain ⟨g, _, rfl⟩ := hy
  intro hh
  apply hx
  exact (MulAut.conj g).injective (hh.trans (map_one (MulAut.conj g)).symm)

private theorem relativeOrbit_subset {E : Subgroup G} {x : G} (hx : x ∈ E) :
    relativeOrbit (normalizer (E : Set G)) x ⊆ E := by
  rintro y ⟨g, hg, rfl⟩
  exact (mem_normalizer_iff.mp hg x).mp hx

private theorem relativeOrbit_ncard (N : Subgroup G) (x : G) :
    (relativeOrbit N x).ncard = (centralizer ({x} : Set G)).relIndex N := by
  let : MulAction N G := {
    smul := fun g y => (g : G) * y * (g : G)⁻¹
    one_smul := by intro y; change (1 : G) * y * (1 : G)⁻¹ = y; simp
    mul_smul := by
      intro a b y
      change ((a : G) * (b : G)) * y * ((a : G) * (b : G))⁻¹ =
        (a : G) * ((b : G) * y * (b : G)⁻¹) * (a : G)⁻¹
      simp [mul_assoc] }
  have ho : relativeOrbit N x = MulAction.orbit N x := by
    ext y
    constructor
    · rintro ⟨g, hg, he⟩
      exact ⟨⟨g, hg⟩, he⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, g.property, hg⟩
  have hs : MulAction.stabilizer N x = (centralizer ({x} : Set G)).subgroupOf N := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, mem_centralizer_singleton_iff]
    change (g : G) * x * (g : G)⁻¹ = x ↔ (g : G) * x = x * (g : G)
    exact mul_inv_eq_iff_eq_mul
  rw [ho, ← MulAction.index_stabilizer, hs]
  rfl

private theorem centralizer_le_normalizer (D : LocalData G)
    (e : D.centralizer ≃* Second) :
    D.centralizer ≤ normalizer (ambientFourGroup D e : Set G) := by
  have := fourGroup_normal
  have h := fourGroup.le_normalizer_map (embedding D e)
  simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
    embedding_range, ambientFourGroup] using h

private theorem relativeOrbit_card_mul (N : Subgroup G) (x : G) :
    Nat.card ↥(N ⊓ centralizer ({x} : Set G)) * (relativeOrbit N x).ncard = Nat.card N := by
  rw [relativeOrbit_ncard]
  have hc : Nat.card ((centralizer ({x} : Set G)).subgroupOf N) =
      Nat.card ↥(N ⊓ centralizer ({x} : Set G)) := by
    rw [← inf_subgroupOf_left]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hc]
  exact (centralizer ({x} : Set G)).subgroupOf N |>.card_mul_index

variable [Finite G] (D : LocalData G) (e : D.centralizer ≃* Second)

private theorem central_orbit_bound :
    (relativeOrbit (normalizer (ambientFourGroup D e : Set G)) D.z).ncard ≤ 15 := by
  have hzF : D.z ∈ ambientFourGroup D e := by
    rw [← embedding_centralPoint D e]
    exact mem_map_of_mem _ (threeGroup_le_fourGroup centralPoint_mem_threeGroup)
  have hs : relativeOrbit (normalizer (ambientFourGroup D e : Set G)) D.z ⊆
      (ambientFourGroup D e : Set G) \ {1} := by
    intro y hy
    exact ⟨relativeOrbit_subset hzF hy, relativeOrbit_nonidentity D.z_ne_one hy⟩
  have h := Set.ncard_le_ncard hs
  rw [Set.ncard_sdiff_singleton_of_mem (ambientFourGroup D e).one_mem] at h
  change _ ≤ Nat.card (ambientFourGroup D e) - 1 at h
  rw [ambientFourGroup_card] at h
  exact h

private theorem central_orbit_card
    (h7 : 7 ∣ Nat.card (normalizer (ambientFourGroup D e : Set G))) :
    (relativeOrbit (normalizer (ambientFourGroup D e : Set G)) D.z).ncard = 7 := by
  let N := normalizer (ambientFourGroup D e : Set G)
  have hHN : D.centralizer ≤ N := centralizer_le_normalizer D e
  have hc := relativeOrbit_card_mul N D.z
  have hH : Nat.card D.centralizer = 384 := (Nat.card_congr e.toEquiv).trans Model.card
  have hi : N ⊓ centralizer ({D.z} : Set G) = D.centralizer := inf_eq_right.mpr hHN
  rw [hi, hH] at hc
  have hd : 7 ∣ (relativeOrbit N D.z).ncard := by
    rw [← hc] at h7
    exact (Nat.Prime.dvd_mul (by decide : Nat.Prime 7)).mp h7 |>.resolve_left (by decide)
  have ho : ¬ 2 ∣ (relativeOrbit N D.z).ncard := by
    rw [relativeOrbit_ncard]
    intro h
    exact D.sylow.not_dvd_index (h.trans
      ((relIndex_dvd_index_of_le hHN).trans (index_dvd_of_le D.sylow_le_centralizer)))
  have hb := central_orbit_bound D e
  change (relativeOrbit N D.z).ncard ≤ 15 at hb
  change (relativeOrbit N D.z).ncard = 7
  omega

private theorem normalizer_card
    (h7 : 7 ∣ Nat.card (normalizer (ambientFourGroup D e : Set G))) :
    Nat.card (normalizer (ambientFourGroup D e : Set G)) = 2688 := by
  have hc := relativeOrbit_card_mul (normalizer (ambientFourGroup D e : Set G)) D.z
  rw [central_orbit_card D e h7,
    inf_eq_right.mpr (centralizer_le_normalizer D e)] at hc
  have hH : Nat.card D.centralizer = 384 := (Nat.card_congr e.toEquiv).trans Model.card
  rw [hH] at hc
  exact hc.symm

private def outsideSet : Set G :=
  embedding D e '' ((fourGroup : Set Second) \ (threeGroup : Set Second))

omit [Finite G] in
private theorem outsideSet_card : (outsideSet D e).ncard = 8 := by
  rw [outsideSet, Set.ncard_image_of_injective _ (embedding_injective D e),
    Set.ncard_sdiff' threeGroup_le_fourGroup]
  change Nat.card fourGroup - Nat.card threeGroup = 8
  rw [fourGroup_card, threeGroup_card]

omit [Finite G] in
private theorem outsideSet_subset_orbit : outsideSet D e ⊆
    relativeOrbit (normalizer (ambientFourGroup D e : Set G)) (embedding D e outsidePoint) := by
  rintro _ ⟨y, ⟨hyF, hyV⟩, rfl⟩
  obtain ⟨a, ha⟩ := isConj_iff.mp (outside_isConj y hyF hyV)
  refine ⟨embedding D e a, centralizer_le_normalizer D e (embedding_mem D e a), ?_⟩
  simpa only [map_mul, map_inv] using congrArg (embedding D e) ha

private theorem outside_not_in_central_orbit
    (h7 : 7 ∣ Nat.card (normalizer (ambientFourGroup D e : Set G))) :
    embedding D e outsidePoint ∉
      relativeOrbit (normalizer (ambientFourGroup D e : Set G)) D.z := by
  intro hx
  have hs := outsideSet_subset_orbit D e
  rw [relativeOrbit_eq_of_mem hx] at hs
  have hh := Set.ncard_le_ncard hs
  rw [outsideSet_card, central_orbit_card D e h7] at hh
  omega

private theorem outside_orbit_card
    (h7 : 7 ∣ Nat.card (normalizer (ambientFourGroup D e : Set G))) :
    (relativeOrbit (normalizer (ambientFourGroup D e : Set G))
      (embedding D e outsidePoint)).ncard = 8 := by
  let N := normalizer (ambientFourGroup D e : Set G)
  let Z := relativeOrbit N D.z
  let X := relativeOrbit N (embedding D e outsidePoint)
  have hX : 8 ≤ X.ncard := by
    have h := Set.ncard_le_ncard (outsideSet_subset_orbit D e)
    rw [outsideSet_card] at h
    exact h
  have hx1 : embedding D e outsidePoint ≠ 1 := by
    intro h
    have : outsidePoint = 1 := (embedding_injective D e) (h.trans (map_one _).symm)
    exact outsidePoint_not_mem_threeGroup (this ▸ threeGroup.one_mem)
  have hdis : Disjoint Z X := by
    apply Set.disjoint_left.mpr
    intro y hyZ hyX
    have he : X = Z := (relativeOrbit_eq_of_mem hyX).symm.trans (relativeOrbit_eq_of_mem hyZ)
    have hxX : embedding D e outsidePoint ∈ X := mem_relativeOrbit N _
    rw [he] at hxX
    exact outside_not_in_central_orbit D e h7 hxX
  have hs : Z ∪ X ⊆ (ambientFourGroup D e : Set G) \ {1} := by
    intro y hy
    rcases hy with hy | hy
    · exact ⟨relativeOrbit_subset (by
        rw [← embedding_centralPoint D e]
        exact mem_map_of_mem _ (threeGroup_le_fourGroup centralPoint_mem_threeGroup)) hy,
        relativeOrbit_nonidentity D.z_ne_one hy⟩
    · exact ⟨relativeOrbit_subset (mem_map_of_mem _ outsidePoint_mem_fourGroup) hy,
        relativeOrbit_nonidentity hx1 hy⟩
  have hh := Set.ncard_le_ncard hs
  rw [Set.ncard_union_eq hdis,
    Set.ncard_sdiff_singleton_of_mem (ambientFourGroup D e).one_mem] at hh
  change Z.ncard + X.ncard ≤ Nat.card (ambientFourGroup D e) - 1 at hh
  have hZ : Z.ncard = 7 := central_orbit_card D e h7
  rw [hZ, ambientFourGroup_card] at hh
  change X.ncard = 8
  omega

/-- The centralizer of the outside involution in the four-group normalizer
has order 336 whenever seven divides that normalizer's order. -/
public theorem outside_centralizer_card
    (h7 : 7 ∣ Nat.card (normalizer (ambientFourGroup D e : Set G))) :
    Nat.card ↥(normalizer (ambientFourGroup D e : Set G) ⊓
      centralizer ({embedding D e outsidePoint} : Set G)) = 336 := by
  have hc := relativeOrbit_card_mul (normalizer (ambientFourGroup D e : Set G))
    (embedding D e outsidePoint)
  rw [outside_orbit_card D e h7, normalizer_card D e h7] at hc
  omega

open scoped Pointwise in
/-- Seven-divisibility prevents the marked outside involution from being an
ambient square. Simplicity and exceptional normalizer action are not needed. -/
public theorem no_outside_square_of_seven_dvd
    (h7 : 7 ∣ Nat.card (normalizer (ambientFourGroup D e : Set G))) :
    ¬ ∃ r : G, r ^ 2 = embedding D e outsidePoint := by
  let F := ambientFourGroup D e
  let N := normalizer (F : Set G)
  let x := embedding D e outsidePoint
  let C := centralizer ({x} : Set G)
  have hFcard : Nat.card F = 16 := ambientFourGroup_card D e
  have hFp : IsPGroup 2 F := IsPGroup.of_card (n := 4) hFcard
  have hFx : x ∈ F := mem_map_of_mem _ outsidePoint_mem_fourGroup
  have hF2 : ∀ f : G, f ∈ F → f ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, fourGroup_square a ha, map_one]
  have hx1 : x ≠ 1 := by
    intro hh
    have hh1 : outsidePoint = 1 := (embedding_injective D e) (hh.trans (map_one _).symm)
    exact outsidePoint_not_mem_threeGroup (hh1 ▸ threeGroup.one_mem)
  have hFC : F ≤ C := by
    rintro _ ⟨a, ha, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact (map_mul (embedding D e) a outsidePoint).symm.trans
      ((congrArg (embedding D e) (fourGroup_comm a outsidePoint ha
        outsidePoint_mem_fourGroup)).trans (map_mul _ _ _))
  have hNC : Nat.card ↥(N ⊓ C) = 336 := outside_centralizer_card D e h7
  -- First saturate F among two-subgroups of N ∩ C, then in C.
  have hmax : ∀ T : Subgroup G, IsPGroup 2 T → F ≤ T → T ≤ C → T = F := by
    apply saturated_of_normalizer_control F N C _ inf_le_left
    intro T hTp hFT hTNC
    apply (eq_of_le_of_card_ge hFT _).symm
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hTp
    have hd : 2 ^ n ∣ 336 := by
      rw [← hn, ← hNC]
      exact card_dvd_of_le hTNC
    have hn4 : n ≤ 4 := by
      by_contra hn4
      have hh : 2 ^ 5 ∣ 336 := (pow_dvd_pow 2 (show 5 ≤ n by omega)).trans hd
      norm_num at hh
    rw [hn, hFcard]
    exact Nat.pow_le_pow_right (by decide) hn4
  -- Conjugation within C fixes x while moving a root into F.
  obtain ⟨P, hFP⟩ := (hFp.comap_subtype (K := C)).exists_le_sylow
  have hPF : (P : Subgroup C).map C.subtype = F := hmax _ (P.isPGroup'.map _)
    (by
      rw [← map_subgroupOf_eq_of_le hFC]
      exact map_mono hFP) (map_subtype_le _)
  rintro ⟨r, hr⟩
  change r ^ 2 = x at hr
  have hrC : r ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hr]
    exact (Commute.self_pow r 2).eq
  let rC : C := ⟨r, hrC⟩
  have hr4 : rC ^ 4 = 1 := by
    apply Subtype.ext
    change r ^ 4 = 1
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hr]
    exact hF2 x hFx
  have hp : IsPGroup 2 (zpowers rC) := IsPGroup.of_card_dvd_pow (n := 2) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hr4)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq C Q P
  have hrP : (MulAut.conj a) rC ∈ P := by
    rw [← ha]
    change (MulAut.conj a) • rC ∈ (MulAut.conj a) • (Q : Set C)
    exact Set.smul_mem_smul_set (hQ (mem_zpowers rC))
  have hrF : (((MulAut.conj a) rC : C) : G) ∈ F := by
    rw [← hPF]
    exact mem_map_of_mem C.subtype hrP
  have hsquare := hF2 _ hrF
  change ((MulAut.conj (a : G)) r) ^ 2 = 1 at hsquare
  rw [← map_pow, hr] at hsquare
  have hfix : (MulAut.conj (a : G)) x = x :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp a.property)
  exact hx1 (hfix.symm.trans hsquare)

end Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl.SquareObstruction
