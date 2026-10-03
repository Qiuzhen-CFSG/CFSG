module

public import Stellmacher.LaterDefs
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SL2Products
public import Stellmacher.SectionEight.SL2CentralKernelSeedDisjoint

/-!
# Normal closure of a centralizing SL₂(2) seed

For a finite group mapping onto SL₂(2) with normal two-group kernel `N`,
a two-subgroup `V` that centralizes `N` and intersects it trivially has
normal closure disjoint from `N` as well. This is the abstract finite-group
input for Stellmacher (8.6)(1), printed p.41, without graph or generation data.

For nontrivial `V`, the normal image of the centralizer of `N` contains
a nontrivial two-subgroup of SL₂(2), so the restricted projection is onto.
Its kernel is central, permitting the central-kernel transfer theorem.
Ambient conjugation adds nothing: each actor differs from a centralizer
lift by an element of `N`, which centralizes the seed.
-/

namespace Stellmacher.SectionEight

open Later

universe u

private theorem normal_card_two_central
    {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) [K.Normal] (hcard : Nat.card K = 2) :
    K ≤ Subgroup.center H := by
  obtain ⟨other, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : K)).mp hcard
  intro element helement
  rw [Subgroup.mem_center_iff]
  intro actor
  by_cases hone : element = 1
  · simp [hone]
  have heq : (⟨element, helement⟩ : K) = other :=
    hunique _ (fun heq => hone (congrArg Subtype.val heq))
  have hmem : actor * element * actor⁻¹ ∈ K :=
    (inferInstance : K.Normal).conj_mem element helement actor
  have hne : actor * element * actor⁻¹ ≠ 1 := by
    intro heq
    have heq' := congrArg (fun value : H => actor⁻¹ * value * actor) heq
    exact hone (by simpa [mul_assoc] using heq')
  have hconj : (⟨actor * element * actor⁻¹, hmem⟩ : K) = other :=
    hunique _ (fun heq => hne (congrArg Subtype.val heq))
  have heq' := congrArg (fun value : K => (value : H) * actor) (hconj.trans heq.symm)
  simpa [mul_assoc] using heq'

private theorem sl2_normal_overgroup_eq_top
    (K P : Subgroup SL2Two) [K.Normal] (hPtwo : IsPGroup 2 P)
    (hPK : P ≤ K) (hPne : P ≠ ⊥) : K = ⊤ := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card SL2Two = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  have hKd : Nat.card K ∣ 6 := hcard ▸ K.card_subgroup_dvd_card
  have hcases : Nat.card K = 1 ∨ Nat.card K = 2 ∨
      Nat.card K = 3 ∨ Nat.card K = 6 := by
    have hmem := Nat.mem_divisors.mpr ⟨hKd, by decide⟩
    norm_num [Nat.divisors] at hmem
    obtain ⟨⟨hlower, hupper⟩, _⟩ := hmem
    interval_cases hvalue : Nat.card K <;> norm_num at *
  have htwo : 2 ∣ Nat.card K := by
    obtain ⟨exponent, hexponent⟩ := hPtwo.exists_card_eq
    have hexponent_ne : exponent ≠ 0 := by
      intro heq
      simp only [heq, pow_zero] at hexponent
      exact hPne (Subgroup.card_eq_one.mp hexponent)
    apply dvd_trans ?_ (Subgroup.card_dvd_of_le hPK)
    rw [hexponent]
    exact dvd_pow_self 2 hexponent_ne
  rcases hcases with hone | htwoCard | hthree | hsix
  · omega
  · have hcentral := normal_card_two_central K htwoCard
    rw [SectionOne.RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two
      (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)] at hcentral
    exact (hPne (bot_unique (hPK.trans hcentral))).elim
  · omega
  · exact K.eq_top_of_card_eq (hsix.trans hcard.symm)

private theorem sl2_centralizer_projection_surjective
    {H : Type u} [Group H] [Finite H]
    (N V : Subgroup H) [N.Normal]
    (projection : H →* SL2Two) (hsurj : Function.Surjective projection)
    (hker : projection.ker = N) (hVtwo : IsPGroup 2 V)
    (hcomm : ⁅N, V⁆ = ⊥) (hinter : V ⊓ N = ⊥) (hVne : V ≠ ⊥) :
    Function.Surjective (projection.comp (Subgroup.centralizer (N : Set H)).subtype) := by
  let D := Subgroup.centralizer (N : Set H)
  have hVD : V ≤ D := Subgroup.le_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  let _ : D.Normal := Subgroup.normal_centralizer
  let _ : (D.map projection).Normal := (inferInstance : D.Normal).map projection hsurj
  have himage_ne : V.map projection ≠ ⊥ := by
    intro heq
    have hVN : V ≤ N := by
      rw [← hker]
      exact (Subgroup.map_eq_bot_iff V).mp heq
    exact hVne (by simpa [inf_eq_left.mpr hVN] using hinter)
  have hfull : D.map projection = ⊤ := sl2_normal_overgroup_eq_top
    (D.map projection) (V.map projection) (hVtwo.map projection)
    (Subgroup.map_mono hVD) himage_ne
  intro target
  have hmem : target ∈ D.map projection := hfull.symm ▸ Subgroup.mem_top target
  obtain ⟨element, helement, heq⟩ := hmem
  exact ⟨⟨element, helement⟩, heq⟩

private theorem centralizing_closure_le_centralizer_closure
    {H : Type u} [Group H] (N V : Subgroup H)
    (projection : H →* SL2Two) (hker : projection.ker = N)
    (hVD : V ≤ Subgroup.centralizer (N : Set H))
    (hsurj : Function.Surjective
      (projection.comp (Subgroup.centralizer (N : Set H)).subtype)) :
    conjugateClosure V (⊤ : Subgroup H) ≤
      (conjugateClosure (V.subgroupOf (Subgroup.centralizer (N : Set H))) ⊤).map
        (Subgroup.centralizer (N : Set H)).subtype := by
  let D := Subgroup.centralizer (N : Set H)
  rw [conjugateClosure, Subgroup.closure_le]
  rintro element ⟨actor, generator, rfl⟩
  obtain ⟨lift, hlift⟩ := hsurj (projection actor)
  have hlift' : projection (lift : H) = projection actor := hlift
  let kernelElement : H := (lift : H)⁻¹ * actor
  have hkernel : kernelElement ∈ N := by
    rw [← hker, MonoidHom.mem_ker]
    simp [kernelElement, hlift']
  have hcommute : kernelElement * (generator : H) = generator * kernelElement :=
    Subgroup.mem_centralizer_iff.mp (hVD generator.property) kernelElement hkernel
  have hconjugate : (actor : H) * generator * (actor : H)⁻¹ =
      (lift : H) * generator * (lift : H)⁻¹ := by
    calc
      _ = (lift : H) * (kernelElement * (generator : H) * kernelElement⁻¹) *
          (lift : H)⁻¹ := by dsimp [kernelElement]; group
      _ = _ := by rw [hcommute]; group
  let generatorD : D := ⟨generator, hVD generator.property⟩
  have hgen : lift * generatorD * lift⁻¹ ∈
      conjugateClosure (V.subgroupOf D) (⊤ : Subgroup D) := by
    apply Subgroup.subset_closure
    exact ⟨⟨lift, Subgroup.mem_top _⟩, ⟨generatorD, generator.property⟩, rfl⟩
  exact ⟨lift * generatorD * lift⁻¹, hgen, hconjugate.symm⟩

private theorem centralizer_kernel_central
    {H : Type u} [Group H] (N : Subgroup H) :
    N.subgroupOf (Subgroup.centralizer (N : Set H)) ≤
      Subgroup.center (Subgroup.centralizer (N : Set H)) := by
  intro element helement
  rw [Subgroup.mem_center_iff]
  intro actor
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp actor.property element helement).symm

private theorem centralizer_projection_kernel
    {H : Type u} [Group H] (N : Subgroup H)
    (projection : H →* SL2Two) (hker : projection.ker = N) :
    (projection.comp (Subgroup.centralizer (N : Set H)).subtype).ker =
      N.subgroupOf (Subgroup.centralizer (N : Set H)) := by
  ext element
  change projection (element : H) = 1 ↔ (element : H) ∈ N
  simpa only [hker] using
    (MonoidHom.mem_ker (f := projection) (x := (element : H))).symm

private theorem centralizer_seed_intersection
    {H : Type u} [Group H] (N V : Subgroup H)
    (hinter : V ⊓ N = ⊥) :
    V.subgroupOf (Subgroup.centralizer (N : Set H)) ⊓
      N.subgroupOf (Subgroup.centralizer (N : Set H)) = ⊥ := by
  apply bot_unique
  intro element helement
  have hone : (element : H) ∈ V ⊓ N := helement
  rw [hinter] at hone
  exact Subtype.ext hone

private theorem closure_disjoint_of_centralizer_closure_disjoint
    {H : Type u} [Group H] (N V : Subgroup H)
    (projection : H →* SL2Two) (hker : projection.ker = N)
    (hVD : V ≤ Subgroup.centralizer (N : Set H))
    (hsurj : Function.Surjective
      (projection.comp (Subgroup.centralizer (N : Set H)).subtype))
    (hlocal : conjugateClosure (V.subgroupOf (Subgroup.centralizer (N : Set H))) ⊤ ⊓
      N.subgroupOf (Subgroup.centralizer (N : Set H)) = ⊥) :
    conjugateClosure V (⊤ : Subgroup H) ⊓ N = ⊥ := by
  apply bot_unique
  rintro element ⟨hclosure, hkernel⟩
  obtain ⟨lift, hlift, heq⟩ :=
    centralizing_closure_le_centralizer_closure N V projection hker hVD hsurj hclosure
  change (lift : H) = element at heq
  have hliftKernel : lift ∈ N.subgroupOf (Subgroup.centralizer (N : Set H)) := by
    change (lift : H) ∈ N
    rwa [heq]
  have hone : lift ∈ (⊥ : Subgroup (Subgroup.centralizer (N : Set H))) :=
    hlocal ▸ ⟨hlift, hliftKernel⟩
  change element = 1
  rw [← heq, (show lift = 1 from hone)]
  rfl

private theorem bottom_seed_closure
    {H : Type u} [Group H] (actors : Subgroup H) :
    conjugateClosure (⊥ : Subgroup H) actors = ⊥ := by
  apply bot_unique
  rw [conjugateClosure, Subgroup.closure_le]
  rintro element ⟨actor, generator, rfl⟩
  have hone : (generator : H) = 1 := generator.property
  simp [hone]

public theorem sl2_centralizing_seed_closure_disjoint
    {H : Type u} [Group H] [Finite H]
    (N V : Subgroup H) [N.Normal] (hNtwo : IsPGroup 2 N)
    (projection : H →* Stellmacher.Later.SL2Two)
    (hsurj : Function.Surjective projection) (hker : projection.ker = N)
    (hVtwo : IsPGroup 2 V) (hcomm : ⁅N, V⁆ = ⊥) (hinter : V ⊓ N = ⊥) :
    Stellmacher.conjugateClosure V (⊤ : Subgroup H) ⊓ N = ⊥ := by
  by_cases hVbot : V = ⊥
  · rw [hVbot, bottom_seed_closure, bot_inf_eq]
  let D := Subgroup.centralizer (N : Set H)
  have hVD : V ≤ D := Subgroup.le_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hrestricted := sl2_centralizer_projection_surjective
    N V projection hsurj hker hVtwo hcomm hinter hVbot
  have hlocal := sl2_central_kernel_seed_closure_disjoint
    (N.subgroupOf D) (V.subgroupOf D) hNtwo.comap_subtype
    (centralizer_kernel_central N) (projection.comp D.subtype) hrestricted
    (centralizer_projection_kernel N projection hker) hVtwo.comap_subtype
    (centralizer_seed_intersection N V hinter)
  exact closure_disjoint_of_centralizer_closure_disjoint
    N V projection hker hVD hrestricted hlocal


end Stellmacher.SectionEight
