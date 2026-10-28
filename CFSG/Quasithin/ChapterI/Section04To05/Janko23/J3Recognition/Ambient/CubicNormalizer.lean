module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.CubicCentralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Sylow

/-!
# The actual cubic normalizer and its alternating derived quotient

For a cubic in an H-type involution centralizer, the dihedral core fixed
subgroup gives a centralizer of order 24. The action on the cubic line
bounds its normalizer index by two; Sylow's normalizer congruence modulo
nine excludes index one and gives order 48. Simultaneous conjugation of
the cubic and a commuting involution then forces index two in the full
ambient normalizer.

For the cubic already selected in a plane complement, its proved A₆
centralizer quotient gives orders 1080, 2160 and 720 for the centralizer,
normalizer and normalizer quotient. The literal inclusion of quotients is
injective, has image of index two and identifies that image with the whole
derived subgroup. The centralizer's center is exactly the original cubic.
An actual normalizing element inverts its generator.

This increment uses neither a local A₅ complement nor the J₂ census.
It does not assert that the inverter is an involution: Baumeister's
split-centralizer hypothesis must still be supplied in the original H-type
context, or the involutory inverter constructed independently, before the
remaining PGL₂(9) identification and splitting argument can be applied.

Source: Baumeister, *A geometry for groups of J₃-type* (2007),
Lemma 2.4, p.495. The local index argument also occurs in Aschbacher,
*Sporadic Groups* (1994), the proof of 47.3, p.262.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The cubic centralizer inside the original involution centralizer has order 24. -/
theorem cubic_local_centralizer_card (h : HTypeAt z)
    (s : involutionCentralizer z) (hs : orderOf s = 3) :
    Nat.card (centralizer ({s} : Set (involutionCentralizer z))) = 24 := by
  obtain ⟨hd, hgen⟩ := cubic_local_product h s hs
  have he := (cubic_core_fixed h s hs).some
  have hcard : Nat.card (localCore z ⊓ centralizer ({s} : Set (involutionCentralizer z)) :
      Subgroup (involutionCentralizer z)) = 8 :=
    (Nat.card_congr he.toEquiv).trans DihedralGroup.nat_card
  have hn : zpowers s ≤ normalizer
      ((localCore z ⊓ centralizer ({s} : Set (involutionCentralizer z)) :
        Subgroup (involutionCentralizer z)) : Set _) := by
    apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro x hx
    apply mem_centralizer_iff.mpr
    intro y hy
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hy
    exact ((show Commute x s from mem_centralizer_singleton_iff.mp hx.2).zpow_right n).symm
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (localCore z ⊓ centralizer ({s} : Set (involutionCentralizer z))) (zpowers s) hn
  rw [hcard, hd.eq_bot, card_bot, one_mul, hgen, Nat.card_zpowers, hs] at hh
  exact hh.symm

/-- Sylow congruence forces the local cubic normalizer to have order 48. -/
theorem cubic_local_normalizer_card (h : HTypeAt z)
    (s : involutionCentralizer z) (hs : orderOf s = 3) :
    Nat.card (normalizer (zpowers s : Set (involutionCentralizer z))) = 48 := by
  let H := involutionCentralizer z
  let Y := zpowers s
  let N := normalizer (Y : Set H)
  have hY : Nat.card Y = 3 := (Nat.card_zpowers s).trans hs
  have hC : centralizer (Y : Set H) = centralizer ({s} : Set H) := by dsimp only [Y]; rw [zpowers_eq_closure, centralizer_closure]
  have hi : ((centralizer (Y : Set H)).subgroupOf N).index ∣ 2 := by
    have hh := card_dvd_of_injective _ (QuotientGroup.kerLift_injective Y.normalizerMonoidHom)
    rw [normalizerMonoidHom_ker, ← index, IsCyclic.card_mulAut, hY] at hh
    simpa only [Nat.totient_prime Nat.prime_three] using hh
  have hc : Nat.card ((centralizer (Y : Set H)).subgroupOf N) = 24 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (Y : Set H))).toEquiv,
      hC, cubic_local_centralizer_card h s hs]
  have hh := ((centralizer (Y : Set H)).subgroupOf N).index_mul_card
  rw [hc] at hh
  have hm := Sylow.card_normalizer_modEq_card (p := 3) (n := 1) (H := Y) (by simpa using hY)
  rw [h.centralizer_card] at hm
  change Nat.card N % 9 = 1920 % 9 at hm
  rcases (Nat.dvd_prime Nat.prime_two).mp hi with hi | hi
  · rw [hi] at hh
    norm_num at hh
    rw [← hh] at hm
    norm_num at hm
  · rw [hi] at hh
    exact hh.symm


/-- The cubic centralizer has index two in its actual ambient normalizer. -/
theorem cubic_normalizer_index (h : HTypeAt z) (hc : OneInvolutionClass G)
    (s t : G) (hs : orderOf s = 3) (ht : orderOf t = 2) (hst : Commute s t) :
    ((centralizer ({s} : Set G)).subgroupOf (normalizer (zpowers s : Set G))).index = 2 := by
  let Y := zpowers s
  let C := centralizer ({s} : Set G)
  let N := normalizer (Y : Set G)
  have hC : centralizer (Y : Set G) = C := by dsimp only [Y]; rw [zpowers_eq_closure, centralizer_closure]
  have hY : Nat.card Y = 3 := (Nat.card_zpowers s).trans hs
  have hi : (C.subgroupOf N).index ∣ 2 := by
    have hh := card_dvd_of_injective _ (QuotientGroup.kerLift_injective Y.normalizerMonoidHom)
    rw [normalizerMonoidHom_ker, ← index, IsCyclic.card_mulAut, hY, hC] at hh
    simpa only [Nat.totient_prime Nat.prime_three] using hh
  rcases (Nat.dvd_prime Nat.prime_two).mp hi with hi | hi
  · have hNC : N ≤ C := relIndex_eq_one.mp hi
    obtain ⟨g,hg⟩ := isConj_iff.mp (hc.isConj h.involution ht)
    let e := MulAut.conj g
    have het : e t = z := hg
    let H := involutionCentralizer z
    let u : H := ⟨e s, mem_centralizer_singleton_iff.mpr (by
      rw [← het, ← map_mul, ← map_mul, hst.eq])⟩
    have hu : orderOf u = 3 := (orderOf_coe u).symm.trans ((e.orderOf_eq s).trans hs)
    let j : H →* G := e.symm.toMonoidHom.comp H.subtype
    have hj : Function.Injective j := e.symm.injective.comp H.subtype_injective
    have hju : j u = s := e.symm_apply_apply s
    have hmap : (zpowers u).map j = Y := by rw [MonoidHom.map_zpowers, hju]
    have hle : normalizer (zpowers u : Set H) ≤ centralizer ({u} : Set H) := by
      intro x hx
      have hxN : j x ∈ N := by
        change j x ∈ normalizer (Y : Set G)
        rw [← hmap]
        exact (zpowers u).le_normalizer_map j (mem_map_of_mem j hx)
      apply mem_centralizer_singleton_iff.mpr
      apply hj
      simpa only [map_mul, hju] using mem_centralizer_singleton_iff.mp (hNC hxN)
    have hh := card_le_of_le hle
    rw [cubic_local_normalizer_card h u hu, cubic_local_centralizer_card h u hu] at hh
    omega
  · exact hi

/-- Relative to the normalizer, the kernel is the same original cubic line. -/
@[expose] def cubicNormalizerKernel (s : G) : Subgroup (normalizer (zpowers s : Set G)) :=
  (zpowers s).subgroupOf (normalizer (zpowers s : Set G))

instance cubicNormalizerKernel_normal (s : G) : (cubicNormalizerKernel s).Normal :=
  (normal_subgroupOf_iff_le_normalizer (zpowers s).le_normalizer).mpr le_rfl

omit [Finite G] in
/-- The actual inclusion of the cubic centralizer into the cubic normalizer. -/
theorem cubic_centralizer_le_normalizer (s : G) :
    centralizer ({s} : Set G) ≤ normalizer (zpowers s : Set G) := by
  rw [← centralizer_closure, ← zpowers_eq_closure]
  exact Subgroup.centralizer_le_normalizer _

/-- The literal inclusion after quotienting both overgroups by the same cubic. -/
def cubicQuotientInclusion (s : G) :
    (centralizer ({s} : Set G) ⧸ cubicKernel s) →*
      (normalizer (zpowers s : Set G) ⧸ cubicNormalizerKernel s) :=
  QuotientGroup.map (cubicKernel s) (cubicNormalizerKernel s)
    (inclusion (cubic_centralizer_le_normalizer s)) (fun _ hx => hx)

omit [Finite G] in
/-- On every original representative, the quotient inclusion is the expected quotient map. -/
theorem cubicQuotientInclusion_mk (s : G) (x : centralizer ({s} : Set G)) :
    cubicQuotientInclusion s (QuotientGroup.mk' (cubicKernel s) x) =
      QuotientGroup.mk' (cubicNormalizerKernel s)
        ⟨(x : G), cubic_centralizer_le_normalizer s x.property⟩ := by rfl

omit [Finite G] in
/-- No extra kernel is introduced by the inclusion of centralizer quotients. -/
theorem cubicQuotientInclusion_injective (s : G) :
    Function.Injective (cubicQuotientInclusion s) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (cubicKernel s) x
  rw [cubicQuotientInclusion_mk] at hx
  exact (QuotientGroup.eq_one_iff x).mpr
    ((QuotientGroup.eq_one_iff (⟨(x : G), cubic_centralizer_le_normalizer s x.property⟩ :
      normalizer (zpowers s : Set G))).mp hx)

omit [Finite G] in
/-- The original centralizer has order 1080, from its already identified quotient. -/
theorem cubic_centralizer_card (s : G) (hs : orderOf s = 3)
    (e : (centralizer ({s} : Set G) ⧸ cubicKernel s) ≃* alternatingGroup (Fin 6)) :
    Nat.card (centralizer ({s} : Set G)) = 1080 := by
  have hh := (cubicKernel s).index_mul_card
  change Nat.card (centralizer ({s} : Set G) ⧸ cubicKernel s) *
    Nat.card (cubicKernel s) = _ at hh
  rw [Nat.card_congr e.toEquiv, cubicKernel_card s hs, nat_card_alternatingGroup] at hh
  norm_num at hh
  exact hh.symm

/-- The full actual normalizer has order 2160. -/
theorem cubic_normalizer_card (h : HTypeAt z) (hc : OneInvolutionClass G)
    (s : G) (hs : orderOf s = 3)
    (e : (centralizer ({s} : Set G) ⧸ cubicKernel s) ≃* alternatingGroup (Fin 6)) :
    Nat.card (normalizer (zpowers s : Set G)) = 2160 := by
  have hC := cubic_centralizer_card s hs e
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := centralizer ({s} : Set G))
    2 (by rw [hC]; decide)
  have hi := cubic_normalizer_index h hc s t hs ((orderOf_coe t).trans ht)
    (mem_centralizer_singleton_iff.mp t.property).symm
  have hh := ((centralizer ({s} : Set G)).subgroupOf
    (normalizer (zpowers s : Set G))).index_mul_card
  rw [hi, Nat.card_congr (subgroupOfEquivOfLe (cubic_centralizer_le_normalizer s)).toEquiv,
    hC] at hh
  exact hh.symm

/-- The actual normalizer quotient has order 720. -/
theorem cubic_normalizer_quotient_card (h : HTypeAt z) (hc : OneInvolutionClass G)
    (s : G) (hs : orderOf s = 3)
    (e : (centralizer ({s} : Set G) ⧸ cubicKernel s) ≃* alternatingGroup (Fin 6)) :
    Nat.card (normalizer (zpowers s : Set G) ⧸ cubicNormalizerKernel s) = 720 := by
  have hk : Nat.card (cubicNormalizerKernel s) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe (zpowers s).le_normalizer).toEquiv).trans
      ((Nat.card_zpowers s).trans hs)
  have hh := (cubicNormalizerKernel s).index_mul_card
  rw [hk, cubic_normalizer_card h hc s hs e] at hh
  change Nat.card (normalizer (zpowers s : Set G) ⧸ cubicNormalizerKernel s) * 3 = 2160 at hh
  omega

/-- The embedded A₆ is an index-two subgroup of the literal normalizer quotient. -/
theorem cubicQuotientInclusion_index (h : HTypeAt z) (hc : OneInvolutionClass G)
    (s : G) (hs : orderOf s = 3)
    (e : (centralizer ({s} : Set G) ⧸ cubicKernel s) ≃* alternatingGroup (Fin 6)) :
    (cubicQuotientInclusion s).range.index = 2 := by
  have hh := (cubicQuotientInclusion s).range.index_mul_card
  have hr : Nat.card (cubicQuotientInclusion s).range = 360 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (cubicQuotientInclusion_injective s)).toEquiv,
      Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  rw [hr, cubic_normalizer_quotient_card h hc s hs e] at hh
  omega


omit [Finite G] in
/-- The center of the cubic centralizer is precisely the same cubic kernel. -/
theorem cubic_centralizer_center (s : G)
    (e : (centralizer ({s} : Set G) ⧸ cubicKernel s) ≃* alternatingGroup (Fin 6)) :
    center (centralizer ({s} : Set G)) = cubicKernel s := by
  apply le_antisymm ?_ (cubicKernel_central s)
  intro x hx
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (cubicKernel s))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hz : f x ∈ center (alternatingGroup (Fin 6)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y,rfl⟩ := hf y
    rw [← map_mul, ← map_mul, mem_center_iff.mp hx y]
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hz
  exact (QuotientGroup.eq_one_iff x).mp ((e.map_eq_one_iff).mp hz)

/-- The A₆ embedded by the original inclusion is exactly the quotient's derived subgroup. -/
theorem cubic_normalizer_quotient_commutator (h : HTypeAt z) (hc : OneInvolutionClass G)
    (s : G) (hs : orderOf s = 3)
    (e : (centralizer ({s} : Set G) ⧸ cubicKernel s) ≃* alternatingGroup (Fin 6)) :
    _root_.commutator (normalizer (zpowers s : Set G) ⧸ cubicNormalizerKernel s) =
      (cubicQuotientInclusion s).range := by
  let L := (cubicQuotientInclusion s).range
  have hi : L.index = 2 := cubicQuotientInclusion_index h hc s hs e
  let : L.Normal := normal_of_index_eq_two hi
  let : IsCyclic ((normalizer (zpowers s : Set G) ⧸ cubicNormalizerKernel s) ⧸ L) :=
    isCyclic_of_prime_card hi
  let hA : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (centralizer ({s} : Set G) ⧸ cubicKernel s) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsPerfect L := Group.IsPerfect.range (cubicQuotientInclusion s)
  apply le_antisymm
  · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  · change L ≤ _
    rw [← L.commutator_eq_self]
    exact commutator_mono le_top le_top

/-- There is an actual normalizing element inverting the same selected cubic.
No order-two assertion is built into this intermediate statement. -/
theorem cubic_normalizer_inverter (h : HTypeAt z) (hc : OneInvolutionClass G)
    (s : G) (hs : orderOf s = 3)
    (e : (centralizer ({s} : Set G) ⧸ cubicKernel s) ≃* alternatingGroup (Fin 6)) :
    ∃ r : normalizer (zpowers s : Set G), (r : G) * s * (r : G)⁻¹ = s⁻¹ := by
  classical
  let N := normalizer (zpowers s : Set G)
  let C := centralizer ({s} : Set G)
  have hn : ¬ N ≤ C := by
    intro hh
    have hd := card_le_of_le hh
    rw [cubic_normalizer_card h hc s hs e, cubic_centralizer_card s hs e] at hd
    omega
  obtain ⟨r,hrN,hrC⟩ := SetLike.not_le_iff_exists.mp hn
  have hmem : r * s * r⁻¹ ∈ zpowers s :=
    (mem_normalizer_iff.mp hrN s).mp (mem_zpowers s)
  rw [mem_zpowers_iff_mem_range_orderOf, hs] at hmem
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hmem
  have hn3 : n < 3 := Finset.mem_range.mp hn
  refine ⟨⟨r,hrN⟩,?_⟩
  interval_cases n
  · have hu : r * s * r⁻¹ = 1 := by simpa using he.symm
    have hs1 : s = 1 := (MulAut.conj r).injective (hu.trans (map_one _).symm)
    simp [hs1] at hs
  · have hu : r * s * r⁻¹ = s := by simpa using he.symm
    exact (hrC (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hu))).elim
  · have hu : s ^ 2 = s⁻¹ := eq_inv_of_mul_eq_one_left (by
      rw [← pow_succ]
      simpa only [hs] using pow_orderOf_eq_one s)
    exact he.symm.trans hu

end CFSG.Quasithin.Janko23.J3Recognition.Ambient
