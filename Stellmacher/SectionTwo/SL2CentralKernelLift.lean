module

public import Stellmacher.SL2TwoTranspositionNormalizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The Sylow lift of a nontrivial two-subgroup through SL₂(2)

For a surjection to SL₂(2) with central two-group kernel `N`, a two-subgroup
`V` disjoint from `N` and with nontrivial image has order two. Its join with
`N` has order `2 * |N|` and index three, hence is Sylow. Centrality of `N`
and cyclicity of `V` make this join abelian. The order-two image is
self-normalizing in SL₂(2), so the full preimage is self-normalizing too.
Consequently its normalizer centralizes it, as required for Burnside transfer.

The cardinal, index and self-normalizer lemmas do not require centrality;
the hypotheses appear only where used. `centralKernelLift` packages the
original central-kernel hypotheses and all conclusions for transfer consumers.
-/

namespace Stellmacher.SectionTwo

open Later

public theorem sl2Two_two_subgroup_card (U : Subgroup SL2Two)
    (hU : IsPGroup 2 U) (hne : U ≠ ⊥) : Nat.card U = 2 := by
  have hdvd : Nat.card U ∣ 6 := by
    rw [← SectionOne.RankOneThreeGroupAssembly.isSL2Two_card
      (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)]
    exact Subgroup.card_subgroup_dvd_card U
  have hcoprime : Nat.Coprime (Nat.card U) 3 := by
    obtain ⟨exponent, hexponent⟩ := hU.exists_card_eq
    rw [hexponent]
    exact (by decide : Nat.Coprime 2 3).pow_left exponent
  have htwo : Nat.card U ∣ 2 := hcoprime.dvd_of_dvd_mul_right hdvd
  exact ((Nat.dvd_prime Nat.prime_two).mp htwo).resolve_left
    (fun hone => hne (Subgroup.card_eq_one.mp hone))

public theorem centralKernelLift_image_card
    {H : Type*} [Group H] (projection : H →* SL2Two)
    (V : Subgroup H) (hV : IsPGroup 2 V) (hne : V.map projection ≠ ⊥) :
    Nat.card (V.map projection) = 2 :=
  sl2Two_two_subgroup_card (V.map projection) (hV.map projection) hne

public theorem centralKernelLift_seed_card
    {H : Type*} [Group H] (projection : H →* SL2Two)
    (N V : Subgroup H) (hker : projection.ker = N)
    (hV : IsPGroup 2 V) (hdisj : V ⊓ N = ⊥) (hne : V.map projection ≠ ⊥) :
    Nat.card V = 2 := by
  have himage := centralKernelLift_image_card projection V hV hne
  rw [← Subgroup.relIndex_ker, hker, ← Subgroup.inf_relIndex_left V N,
    hdisj, Subgroup.relIndex_bot_left] at himage
  exact himage

public theorem centralKernelLift_kernel_index
    {H : Type*} [Group H] (projection : H →* SL2Two)
    (hsurj : Function.Surjective projection) : projection.ker.index = 6 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
  exact SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩

public theorem centralKernelLift_ambient_card
    {H : Type*} [Group H] (projection : H →* SL2Two)
    (hsurj : Function.Surjective projection) (N : Subgroup H)
    (hker : projection.ker = N) : Nat.card H = Nat.card N * 6 := by
  have hindex : N.index = 6 := hker ▸ centralKernelLift_kernel_index projection hsurj
  simpa only [hindex] using N.card_mul_index.symm

public theorem centralKernelLift_card
    {H : Type*} [Group H] (projection : H →* SL2Two)
    (N V : Subgroup H) (hker : projection.ker = N)
    (hV : IsPGroup 2 V) (hdisj : V ⊓ N = ⊥) (hne : V.map projection ≠ ⊥) :
    Nat.card ↥(N ⊔ V) = Nat.card N * 2 := by
  let : N.Normal := hker ▸ projection.normal_ker
  rw [Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint N V
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    (disjoint_iff.mpr (by simpa only [inf_comm] using hdisj)),
    centralKernelLift_seed_card projection N V hker hV hdisj hne]

public theorem centralKernelLift_index
    {H : Type*} [Group H] [Finite H] (projection : H →* SL2Two)
    (hsurj : Function.Surjective projection) (N V : Subgroup H)
    (hker : projection.ker = N) (hV : IsPGroup 2 V)
    (hdisj : V ⊓ N = ⊥) (hne : V.map projection ≠ ⊥) :
    (N ⊔ V).index = 3 := by
  have hmul := (N ⊔ V).card_mul_index
  rw [centralKernelLift_card projection N V hker hV hdisj hne,
    centralKernelLift_ambient_card projection hsurj N hker, mul_assoc] at hmul
  have hpositive := Nat.card_pos (α := N)
  have htwo : 2 * (N ⊔ V).index = 6 := Nat.eq_of_mul_eq_mul_left hpositive hmul
  omega

public theorem centralKernelLift_map
    {H : Type*} [Group H] (projection : H →* SL2Two)
    (N V : Subgroup H) (hker : projection.ker = N) :
    (N ⊔ V).map projection = V.map projection := by
  rw [Subgroup.map_sup, ← hker, Subgroup.map_ker_self, bot_sup_eq]

public theorem centralKernelLift_normalizer_of_image
    {H : Type*} [Group H] (projection : H →* SL2Two)
    (T : Subgroup H) (hker : projection.ker ≤ T)
    (hcard : Nat.card (T.map projection) = 2) :
    Subgroup.normalizer (T : Set H) ≤ T := by
  have hmap := Subgroup.le_normalizer_map (H := T) projection
  rw [Stellmacher.sl2Two_normalizer_eq_of_card_two (T.map projection) hcard] at hmap
  have hle := Subgroup.map_le_iff_le_comap.mp hmap
  simpa only [Subgroup.comap_map_eq_self hker] using hle

public theorem centralKernelLift_normalizer_eq
    {H : Type*} [Group H] (projection : H →* SL2Two)
    (N V : Subgroup H) (hker : projection.ker = N)
    (hV : IsPGroup 2 V) (hne : V.map projection ≠ ⊥) :
    Subgroup.normalizer ((N ⊔ V : Subgroup H) : Set H) = N ⊔ V := by
  apply le_antisymm ?_ Subgroup.le_normalizer
  apply centralKernelLift_normalizer_of_image projection (N ⊔ V)
    (by rw [hker]; exact le_sup_left)
  rw [centralKernelLift_map projection N V hker]
  exact centralKernelLift_image_card projection V hV hne

public theorem centralKernelLift_isMulCommutative
    {H : Type*} [Group H] (projection : H →* SL2Two)
    (N V : Subgroup H) (hker : projection.ker = N)
    (hcentral : N ≤ Subgroup.center H) (hV : IsPGroup 2 V)
    (hdisj : V ⊓ N = ⊥) (hne : V.map projection ≠ ⊥) :
    IsMulCommutative ↥(N ⊔ V) := by
  let : IsCyclic V := isCyclic_of_prime_card
    (centralKernelLift_seed_card projection N V hker hV hdisj hne)
  have hVV : V ≤ Subgroup.centralizer (V : Set H) := Subgroup.le_centralizer V
  have hNV : N ≤ Subgroup.centralizer (V : Set H) :=
    hcentral.trans (Subgroup.center_le_centralizer _)
  apply Subgroup.le_centralizer_iff_isMulCommutative.mp
  apply sup_le
  · exact hcentral.trans (Subgroup.center_le_centralizer _)
  · apply Subgroup.le_centralizer_iff.mpr
    exact sup_le hNV hVV

public theorem centralKernelLift_isSylow
    {H : Type*} [Group H] [Finite H] (projection : H →* SL2Two)
    (hsurj : Function.Surjective projection) (N V : Subgroup H)
    (hker : projection.ker = N) (hN : IsPGroup 2 N) (hV : IsPGroup 2 V)
    (hdisj : V ⊓ N = ⊥) (hne : V.map projection ≠ ⊥) :
    ∃ P : Sylow 2 H, (P : Subgroup H) = N ⊔ V := by
  let : N.Normal := hker ▸ projection.normal_ker
  have hT : IsPGroup 2 ↥(N ⊔ V) := hN.to_sup_of_normal_left hV
  have hindex := centralKernelLift_index projection hsurj N V hker hV hdisj hne
  exact ⟨hT.toSylow (by rw [hindex]; decide), rfl⟩

public theorem centralKernelLift_normalizer_le_centralizer
    {H : Type*} [Group H] (projection : H →* SL2Two)
    (N V : Subgroup H) (hker : projection.ker = N)
    (hcentral : N ≤ Subgroup.center H) (hV : IsPGroup 2 V)
    (hdisj : V ⊓ N = ⊥) (hne : V.map projection ≠ ⊥) :
    Subgroup.normalizer ((N ⊔ V : Subgroup H) : Set H) ≤
      Subgroup.centralizer ((N ⊔ V : Subgroup H) : Set H) := by
  rw [centralKernelLift_normalizer_eq projection N V hker hV hne]
  exact Subgroup.le_centralizer_iff_isMulCommutative.mpr
    (centralKernelLift_isMulCommutative projection N V hker hcentral hV hdisj hne)

public theorem centralKernelLift
    {H : Type*} [Group H] [Finite H] (projection : H →* SL2Two)
    (hsurj : Function.Surjective projection) (N V : Subgroup H)
    (hker : projection.ker = N) (hcentral : N ≤ Subgroup.center H)
    (hN : IsPGroup 2 N) (hV : IsPGroup 2 V)
    (hdisj : V ⊓ N = ⊥) (hne : V.map projection ≠ ⊥) :
    Nat.card (V.map projection) = 2 ∧ Nat.card V = 2 ∧
      Nat.card H = Nat.card N * 6 ∧ Nat.card ↥(N ⊔ V) = Nat.card N * 2 ∧
      (N ⊔ V).index = 3 ∧
      ∃ P : Sylow 2 H, (P : Subgroup H) = N ⊔ V ∧
        IsMulCommutative P ∧
        Subgroup.normalizer (P : Set H) = (P : Subgroup H) ∧
        Subgroup.normalizer (P : Set H) ≤ Subgroup.centralizer (P : Set H) := by
  obtain ⟨P, hP⟩ := centralKernelLift_isSylow projection hsurj N V hker hN hV hdisj hne
  refine ⟨centralKernelLift_image_card projection V hV hne,
    centralKernelLift_seed_card projection N V hker hV hdisj hne,
    centralKernelLift_ambient_card projection hsurj N hker,
    centralKernelLift_card projection N V hker hV hdisj hne,
    centralKernelLift_index projection hsurj N V hker hV hdisj hne, P, hP, ?_⟩
  change IsMulCommutative (P : Subgroup H) ∧
    Subgroup.normalizer ((P : Subgroup H) : Set H) = (P : Subgroup H) ∧
    Subgroup.normalizer ((P : Subgroup H) : Set H) ≤
      Subgroup.centralizer ((P : Subgroup H) : Set H)
  rw [hP]
  exact ⟨centralKernelLift_isMulCommutative projection N V hker hcentral hV hdisj hne,
    centralKernelLift_normalizer_eq projection N V hker hV hne,
    centralKernelLift_normalizer_le_centralizer projection N V hker hcentral hV hdisj hne⟩

end Stellmacher.SectionTwo
