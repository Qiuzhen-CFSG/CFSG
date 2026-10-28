module
public import Theory.GroupTheory.PrimeRankCentralizer
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.PGroup.CriticalSubgroup
public import Theory.GroupTheory.PGroup.NormalPrimeImage
public import Theory.GroupTheory.SylowLocalCore
public import Theory.SpecificGroups.HeisenbergPrime.ElementaryPlane

/-!
# Normalized subgroups around a Heisenberg three-group

In three-rank at most two, every cubic centralizing a Heisenberg group of
order 27 belongs to its central cubic. A nontrivial normal subgroup of a
three-group containing that Heisenberg subgroup therefore contains the
same cubic centrally. Sylow restriction in the product with a normalized
subgroup proves that each normalized subgroup divisible by three has an
invariant Sylow three-subgroup containing this cubic centrally.

The final transport retains the literal inclusions in a specified ambient
subgroup. Its source application is Aschbacher–Smith 14.7.26, printed p.1053,
refs/quasithin.pdf, for Y in the original residual and I in C_G(x).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A cubic centralizing Heisenberg27 lies in its central cubic when the
ambient three-rank is at most two. -/
theorem cubic_mem_center_of_centralizes_heisenberg
    (Y : Subgroup G) (e : Y ≃* HeisenbergPrime 3)
    (hr : primeRank 3 G ≤ 2) {x : G} (hx : x ^ 3 = 1)
    (hc : x ∈ centralizer (Y : Set G)) : x ∈ (center Y).map Y.subtype := by
  have hYr : primeRank 3 Y = 2 := by
    have hu := (_root_.primeRank_le_of_injective 3 Y.subtype Y.subtype_injective).trans hr
    have hl : 2 ≤ primeRank 3 Y := by
      rw [primeRank_congr 3 e]
      obtain ⟨E,hE,hcard⟩ := HeisenbergPrime.exists_elementary_plane (by decide : 3 ≠ 2)
      let := hE
      exact IsElementaryAbelian.primeRank_ge_of_card E hcard
    omega
  have hxY := mem_of_prime_pow_eq_one_of_centralizes_rank_two hr Y hYr hx hc
  refine ⟨⟨x,hxY⟩,mem_center_iff.mpr (fun y => ?_),rfl⟩
  exact Subtype.ext (hc y y.property)

/-- In a three-group containing Heisenberg27, each nontrivial normal
subgroup contains the same central cubic. -/
theorem heisenberg_center_le_normal_three_subgroup
    (Y P R : Subgroup G) (e : Y ≃* HeisenbergPrime 3)
    (hr : primeRank 3 G ≤ 2) (hP : IsPGroup 3 P)
    (hYP : Y ≤ P) (hRP : R ≤ P) (hPR : P ≤ normalizer (R : Set G))
    (hne : R ≠ ⊥) :
    (center Y).map Y.subtype ≤ R ∧
      (center Y).map Y.subtype ≤ centralizer (P : Set G) := by
  let R₀ := R.subgroupOf P
  let : R₀.Normal := normal_subgroupOf_of_le_normalizer hPR
  let : Fact (IsPGroup 3 P) := ⟨hP⟩
  have hR₀ : R₀ ≠ ⊥ := by
    intro he
    apply hne
    simpa only [R₀,map_subgroupOf_eq_of_le hRP,Subgroup.map_bot] using
      congrArg (map P.subtype) he
  obtain ⟨Z,_,hZR,hZcard,hZ⟩ := exists_central_subgroup_card_eq_prime_in_normal
    (p := 3) R₀ ((nontrivial_iff_ne_bot R₀).mpr hR₀)
  let Z₀ := Z.map P.subtype
  have hZC : Z₀ ≤ centralizer (P : Set G) := by
    rintro _ ⟨z,hz,rfl⟩ p hp
    exact congrArg Subtype.val (mem_center_iff.mp (hZ hz) ⟨p,hp⟩)
  have hZZ : Z₀ ≤ (center Y).map Y.subtype := by
    rintro _ ⟨z,hz,rfl⟩
    apply cubic_mem_center_of_centralizes_heisenberg Y e hr
    · have hh := pow_card_eq_one' (x := (⟨z,hz⟩ : Z))
      rw [hZcard] at hh
      exact congrArg (fun t : Z => ((t : P) : G)) hh
    · exact (centralizer_le hYP) (hZC (mem_map_of_mem P.subtype hz))
  have heq : Z₀ = (center Y).map Y.subtype := eq_of_le_of_card_ge hZZ (by
    rw [card_map_of_injective Y.subtype_injective,
      Nat.card_congr (centerCongr e).toEquiv,HeisenbergPrime.card_center]
    dsimp only [Z₀]
    rw [card_map_of_injective P.subtype_injective,hZcard])
  rw [←heq]
  exact ⟨by rintro _ ⟨z,hz,rfl⟩; exact hZR hz,hZC⟩

/-- A subgroup normalized by Heisenberg27 and divisible by three has an
invariant Sylow three-subgroup containing the common cubic centrally. -/
theorem exists_sylow_center_containing_heisenberg_center
    (Y I : Subgroup G) (e : Y ≃* HeisenbergPrime 3)
    (hr : primeRank 3 G ≤ 2) (hYI : Y ≤ normalizer (I : Set G))
    (hd : 3 ∣ Nat.card I) :
    ∃ P : Sylow 3 I,
      let R := (P : Subgroup I).map I.subtype
      Y ≤ normalizer (R : Set G) ∧
        (center Y).map Y.subtype ≤ (center R).map R.subtype := by
  let B := Y ⊔ I
  have hY : IsPGroup 3 Y := (IsPGroup.of_card (HeisenbergPrime.card (p := 3))).of_equiv e.symm
  have hYB : Y ≤ B := le_sup_left
  have hIB : I ≤ B := le_sup_right
  have hBI : B ≤ normalizer (I : Set G) := sup_le hYI I.le_normalizer
  obtain ⟨S,hYS⟩ := (hY.comap_subtype (K := B)).exists_le_sylow
  let S₀ := (S : Subgroup B).map B.subtype
  have hYS₀ : Y ≤ S₀ := by
    intro y hy
    exact ⟨⟨y,hYB hy⟩,hYS hy,rfl⟩
  obtain ⟨P,hP⟩ := S.exists_map_subtype_eq_inf_of_normalizes hIB hBI
  let R := (P : Subgroup I).map I.subtype
  have hYR : Y ≤ normalizer (R : Set G) := by
    change Y ≤ normalizer ((P : Subgroup I).map I.subtype : Set G)
    rw [hP]
    exact (le_inf (hYS₀.trans S₀.le_normalizer) hYI).trans inf_normalizer_le_normalizer_inf
  have hRne : R ≠ ⊥ := by
    intro he
    have hc : Nat.card (P : Subgroup I) = 1 := by
      rw [←card_map_of_injective I.subtype_injective,show (P : Subgroup I).map I.subtype = ⊥ from he]
      exact card_bot
    have hindex := (P : Subgroup I).card_mul_index
    rw [hc,one_mul] at hindex
    exact P.not_dvd_index (hindex.symm ▸ hd)
  have hp : IsPGroup 3 (Y ⊔ R : Subgroup G) :=
    hY.to_sup_of_normal_right' (P.isPGroup'.map I.subtype) hYR
  obtain ⟨hXR,hXC⟩ := heisenberg_center_le_normal_three_subgroup Y (Y ⊔ R) R e hr hp
    le_sup_left le_sup_right (sup_le hYR R.le_normalizer) hRne
  refine ⟨P,hYR,?_⟩
  change (center Y).map Y.subtype ≤ (center R).map R.subtype
  rw [map_center_subtype_eq_inf_centralizer R]
  exact le_inf hXR (hXC.trans (centralizer_le (show R ≤ Y ⊔ R from le_sup_right)))

/-- The same Sylow selection inside a specified ambient subgroup, with
all centers and normalizers transported back along the actual inclusions. -/
theorem exists_sylow_center_containing_heisenberg_center_in
    (Y I C : Subgroup G) (e : Y ≃* HeisenbergPrime 3)
    (hr : primeRank 3 C ≤ 2) (hYC : Y ≤ C) (hIC : I ≤ C)
    (hYI : Y ≤ normalizer (I : Set G)) (hd : 3 ∣ Nat.card I) :
    ∃ P : Sylow 3 I,
      let R := (P : Subgroup I).map I.subtype
      Y ≤ normalizer (R : Set G) ∧
        (center Y).map Y.subtype ≤ (center R).map R.subtype := by
  let Y₀ := Y.subgroupOf C
  let I₀ := I.subgroupOf C
  let eY := subgroupOfEquivOfLe hYC
  let eI := subgroupOfEquivOfLe hIC
  have hn : Y₀ ≤ normalizer (I₀ : Set C) := by
    rw [←subgroupOf_normalizer_eq hIC]
    exact comap_mono hYI
  obtain ⟨P₀,hYP,hZP⟩ := exists_sylow_center_containing_heisenberg_center
    Y₀ I₀ (eY.trans e) hr hn (by rw [Nat.card_congr eI.toEquiv]; exact hd)
  let P := P₀.mapSurjective (f := eI.toMonoidHom) eI.surjective
  let R₀ := (P₀ : Subgroup I₀).map I₀.subtype
  let R := (P : Subgroup I).map I.subtype
  have hR : R = R₀.map C.subtype := by
    change ((P₀ : Subgroup I₀).map eI.toMonoidHom).map I.subtype =
      ((P₀ : Subgroup I₀).map I₀.subtype).map C.subtype
    rw [map_map,map_map]
    rfl
  refine ⟨P,?_,?_⟩
  · change Y ≤ normalizer (R : Set G)
    rw [hR]
    have hh := (map_mono (f := C.subtype) hYP).trans (R₀.le_normalizer_map C.subtype)
    simpa only [Y₀,map_subgroupOf_eq_of_le hYC] using hh
  · change (center Y).map Y.subtype ≤ (center R).map R.subtype
    rintro _ ⟨y,hy,rfl⟩
    have hy₀ : eY.symm y ∈ center Y₀ := ((centerCongr eY.symm) ⟨y,hy⟩).property
    have hm := hZP (mem_map_of_mem Y₀.subtype hy₀)
    obtain ⟨r,hr,rhe⟩ := hm
    have heval : ((r : C) : G) = (y : G) := congrArg Subtype.val rhe
    have hyr : (y : G) ∈ R := by
      rw [hR]
      exact heval ▸ mem_map_of_mem C.subtype r.property
    refine ⟨⟨y,hyr⟩,mem_center_iff.mpr (fun s => ?_),rfl⟩
    have hs : (s : G) ∈ R₀.map C.subtype := hR ▸ s.property
    obtain ⟨t,ht,hte⟩ := hs
    have hh := congrArg (fun a : R₀ => ((a : C) : G))
      (mem_center_iff.mp hr ⟨t,ht⟩)
    apply Subtype.ext
    change (s : G) * (y : G) = (y : G) * (s : G)
    change (t : G) * ((r : C) : G) = ((r : C) : G) * (t : G) at hh
    change (t : G) = (s : G) at hte
    simpa only [heval,hte] using hh

end Subgroup

