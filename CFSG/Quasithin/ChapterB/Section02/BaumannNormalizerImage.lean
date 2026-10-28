module
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.BaumannTwoOvergroupTransport
public import Stellmacher.BaumannNormalizer
public import Stellmacher.BaumannMap
public import Theory.GroupTheory.SylowNormalizerFrattini
public import Theory.GroupTheory.SylowImageIntersection
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Images of restricted Baumann normalizers

For a Sylow two-subgroup P, its Baumann subgroup can be lifted through an
arbitrary homomorphism at the level of normalizers. The Frattini argument
inside the full preimage of the Baumann image first handles a surjective map.
Passing to the range handles any map. If a normal subgroup N supplements P,
the Sylow intersection argument corrects the lift into N.

The embedded two-residual maps to the embedded residual of the resulting
normalizer image. A factor of three in that image therefore supplies a
two-perfect subgroup of N intersected with the original Baumann normalizer.
This is the subgroup-selection step in the terminal argument of Lemma 13.7.4(1).

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
Lemma 13.7.4(1), printed p.938; the generic normalizer lifting argument also
appears in the proof of Lemma 13.6.20, printed p.931.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterB
variable {G D : Type*} [Group G] [Group D] [Finite G]

/-- Baumann normalizers map onto their image normalizers, for arbitrary kernels. -/
theorem baumann_normalizer_map (P : Sylow 2 G) (f : G →* D)
    (hf : Function.Surjective f) :
    (normalizer (baumann (P : Subgroup G) : Set G)).map f =
      normalizer ((baumann (P : Subgroup G)).map f : Set D) := by
  let B := baumann (P : Subgroup G)
  let C := (B.map f).comap f
  let N := (normalizer (B.map f : Set D)).comap f
  have hBC : B ≤ C := le_comap_map f B
  have hBp : IsPGroup 2 B := P.isPGroup'.to_le inf_le_left
  have hBp' : IsPGroup 2 (B.subgroupOf C) :=
    hBp.of_injective (subgroupOfEquivOfLe hBC).toMonoidHom
      (subgroupOfEquivOfLe hBC).injective
  obtain ⟨Q, hBQ⟩ := hBp'.exists_le_sylow
  have hBQ' : B ≤ (Q : Subgroup C).map C.subtype := by
    rw [← map_subgroupOf_eq_of_le hBC]
    exact map_mono hBQ
  have hBaum : baumann ((Q : Subgroup C).map C.subtype) = B :=
    (twoSubgroup_thompson_baumann_eq P _ (Q.isPGroup'.map C.subtype) hBQ').2
  have hnorm : normalizer ((Q : Subgroup C).map C.subtype : Set G) ≤
      normalizer (B : Set G) := by
    rw [← hBaum]
    exact normalizer_le_normalizer_baumann _
  have hfr := le_normalizer_sylow_sup C N (comap_mono (B.map f).le_normalizer)
    ((comap_normalizer_eq_of_surjective (B.map f) hf).le) Q
  apply le_antisymm (B.le_normalizer_map f)
  have hmap := map_mono (f := f) hfr
  rw [Subgroup.map_sup, show C.map f = B.map f from map_comap_eq_self_of_surjective hf _] at hmap
  have hmap' : N.map f ≤ (normalizer (B : Set G)).map f :=
    hmap.trans (sup_le (map_mono hnorm) (map_mono B.le_normalizer))
  simpa only [N, map_comap_eq_self_of_surjective hf] using hmap'

private theorem baumann_lift (P : Sylow 2 G) (f : G →* D) (x : G)
    (hx : f x ∈ normalizer ((baumann (P : Subgroup G)).map f : Set D)) :
    ∃ a ∈ normalizer (baumann (P : Subgroup G) : Set G), f a = f x := by
  let B := baumann (P : Subgroup G)
  have hB : (B.map f).subgroupOf f.range = B.map f.rangeRestrict := by
    apply map_injective f.range.subtype_injective
    rw [map_subgroupOf_eq_of_le (map_le_range _ _), map_map]
    rfl
  have hx' : f.rangeRestrict x ∈ normalizer (B.map f.rangeRestrict : Set f.range) := by
    rw [← hB, ← subgroupOf_normalizer_eq (map_le_range _ _)]
    exact hx
  rw [← baumann_normalizer_map P f.rangeRestrict f.rangeRestrict_surjective] at hx'
  obtain ⟨a, ha, he⟩ := hx'
  exact ⟨a, ha, congrArg Subtype.val he⟩

theorem normal_baumann_normalizer_image
    (P : Sylow 2 G) (N : Subgroup G) [N.Normal]
    (hNP : N ⊔ (P : Subgroup G) = ⊤) (f : G →* D) :
    (N ⊓ normalizer (baumann (P : Subgroup G) : Set G)).map f =
      N.map f ⊓ normalizer ((baumann (P : Subgroup G)).map f : Set D) := by
  apply le_antisymm (le_inf (map_mono inf_le_left)
    ((map_mono inf_le_right).trans ((baumann (P : Subgroup G)).le_normalizer_map f)))
  rintro q ⟨⟨n, hn, rfl⟩, hqn⟩
  obtain ⟨a, ha, he⟩ := baumann_lift P f n hqn
  obtain ⟨k, hk, t, ht, hkt⟩ := mem_sup_of_normal_left.mp (hNP.symm ▸ mem_top a)
  have htB : t ∈ normalizer (baumann (P : Subgroup G) : Set G) :=
    normalizer_le_normalizer_baumann _ ((P : Subgroup G).le_normalizer ht)
  have hkB : k ∈ normalizer (baumann (P : Subgroup G) : Set G) := by
    have hh := (normalizer (baumann (P : Subgroup G) : Set G)).mul_mem ha
      ((normalizer (baumann (P : Subgroup G) : Set G)).inv_mem htB)
    simpa only [← hkt, mul_inv_cancel_right] using hh
  obtain ⟨Q, hQ⟩ := P.exists_sylow_map_eq_inf_of_normal N
  have hi := P.map_image_eq_inf N _ Q hQ inf_le_left f
  have hft : f t ∈ N.map f := by
    have hh : f t = (f k)⁻¹ * f n := by rw [← he, ← hkt, map_mul]; group
    rw [hh]
    exact mul_mem (inv_mem (mem_map_of_mem f hk)) (mem_map_of_mem f hn)
  have hm : f t ∈ ((P : Subgroup G) ⊓ N).map f := by
    rw [hi]
    exact ⟨mem_map_of_mem f ht, hft⟩
  obtain ⟨u, hu, heu⟩ := hm
  refine ⟨k * u, ⟨mul_mem hk hu.2, mul_mem hkB ?_⟩, ?_⟩
  · exact normalizer_le_normalizer_baumann _ ((P : Subgroup G).le_normalizer hu.1)
  · rw [map_mul, heu, ← map_mul, hkt, he]

/-- The restricted Baumann normalizer calculation retains the literal
embedded residual through an arbitrary homomorphism. -/
theorem normal_baumann_normalizer_residual_image
    (P : Sylow 2 G) (N : Subgroup G) [N.Normal]
    (hNP : N ⊔ (P : Subgroup G) = ⊤) (f : G →* D) :
    let M := N ⊓ normalizer (baumann (P : Subgroup G) : Set G)
    let A := N.map f ⊓ normalizer ((baumann (P : Subgroup G)).map f : Set D)
    ((pResidual 2 M).map M.subtype).map f = (pResidual 2 A).map A.subtype := by
  dsimp only
  rw [map_embedded_pResidual, normal_baumann_normalizer_image P N hNP f]

/-- An actual cubic factor in the restricted Baumann normalizer image supplies
a two-perfect cubic subgroup inside the original restricted normalizer. -/
theorem exists_twoPerfect_three_dvd_le_normal_baumann_normalizer
    (P : Sylow 2 G) (N : Subgroup G) [N.Normal]
    (hNP : N ⊔ (P : Subgroup G) = ⊤) (f : G →* D)
    (h3 : 3 ∣ Nat.card (N.map f ⊓
      normalizer ((baumann (P : Subgroup G)).map f : Set D) : Subgroup D)) :
    ∃ K : Subgroup G, K ≤ N ⊓ normalizer (baumann (P : Subgroup G) : Set G) ∧
      IsPPerfect 2 K ∧ 3 ∣ Nat.card K := by
  let M := N ⊓ normalizer (baumann (P : Subgroup G) : Set G)
  let K := (pResidual 2 M).map M.subtype
  have h3M : 3 ∣ Nat.card M := by
    have he := normal_baumann_normalizer_image P N hNP f
    change M.map f = _ at he
    have hi : 3 ∣ Nat.card (M.map f) := he ▸ h3
    exact hi.trans (card_map_dvd M f)
  have h3R : 3 ∣ Nat.card (pResidual 2 M) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pResidual 2 M)] at h3M
    apply (Nat.prime_three.dvd_mul.mp h3M).resolve_left
    obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual 2 (G := M)).exists_card_eq
    rw [hn]
    intro hd
    have hh : ¬ 3 ∣ 2 := by decide
    exact hh (Nat.prime_three.dvd_of_dvd_pow hd)
  refine ⟨K,map_subtype_le _,isPPerfect_embedded_pResidual 2 M,?_⟩
  rwa [card_map_of_injective M.subtype_injective]

end CFSG.Quasithin.ChapterB
