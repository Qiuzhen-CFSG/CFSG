module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.RootSubgroups
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.RadicalAction
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.GroupTheory.PCoreSurjective

/-!
# The Suzuki-side Ree two-core and its concrete quotient

For `m ≥ 1`, the specified Suzuki matrix group has trivial two-core: it is
simple and nonsolvable, whereas finite two-groups are solvable. Consequently
a surjection from the root-defined Ree seed to that matrix group, whose
kernel is the root-defined radical and is a two-group, identifies the radical
with the intrinsic two-core. The first isomorphism theorem then gives the
actual quotient equivalence, with its formula on quotient representatives.

If the radical is self-centralizing in the seed, the intrinsic two-core is
self-centralizing and nontrivial. For nontriviality, a trivial radical would
force the seed to be trivial, contradicting surjectivity onto the nontrivial
Suzuki group. Thus a separate nonidentity radical element is unnecessary.

The final declarations discharge these premises using the concrete fixed-Levi
projection and the root-radical calculations. For every `LocalBlockInput m`
with `m ≥ 1`, they identify the root radical with the nontrivial,
self-centralizing intrinsic two-core and construct its quotient equivalence
with the actual Suzuki matrix group. No ambient Ree simplicity assumption is
needed. The earlier conditional APIs remain available.

Source: the local calculation in Aschbacher–Smith F.1.12(I)(5), printed p.263,
used in 2.3.9(7), printed p.526. Normality and centralization here are inside
the root-defined seed, which excludes the complementary parabolic torus.
-/

@[expose] public section

namespace ReeF4.LargeLocalSeeds

open Subgroup BenderSuzuki.MatrixGroups

/-- The exact Suzuki target has no nontrivial normal two-subgroup. -/
theorem suzukiQuotient_twoCore_eq_bot (m : ℕ) (hm : 1 ≤ m) :
    pCore 2 (SuzukiMatrixGroup m) = ⊥ := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (pCore 2 (SuzukiMatrixGroup m)) inferInstance with h | h
  · exact h
  · have hp : IsPGroup 2 (⊤ : Subgroup (SuzukiMatrixGroup m)) :=
      h ▸ pCore_isPGroup
    let := (hp.of_equiv Subgroup.topEquiv).isNilpotent
    exact (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
      inferInstance).elim

/-- An exact kernel calculation gives relative normality in the local seed. -/
theorem suzuki_seedRadical_normal_of_kernel {m : ℕ} (d : LocalBlockInput m)
    (π : standardSeed d .suzuki →* SuzukiMatrixGroup m)
    (hker : π.ker = seedRadical d .suzuki) :
    (seedRadical d .suzuki).Normal := hker ▸ inferInstance

/-- A concrete Suzuki projection with two-group kernel identifies the root
radical with the intrinsic two-core of its seed. -/
theorem suzuki_seedRadical_eq_pCore_of_projection {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m) (π : standardSeed d .suzuki →* SuzukiMatrixGroup m)
    (hπ : Function.Surjective π) (hker : π.ker = seedRadical d .suzuki)
    (hP : IsPGroup 2 (seedRadical d .suzuki)) :
    seedRadical d .suzuki = pCore 2 (standardSeed d .suzuki) := by
  have hkP : IsPGroup 2 π.ker := hker ▸ hP
  have h := π.comap_pCore_of_ker_isPGroup hπ hkP
  simpa only [suzukiQuotient_twoCore_eq_bot m hm, MonoidHom.comap_bot,
    ← hker] using h

/-- The first-isomorphism equivalence uses the intrinsic two-core, after the
projection kernel has been identified with the root-defined radical. -/
noncomputable def suzuki_coreQuotientEquivOfProjection {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m) (π : standardSeed d .suzuki →* SuzukiMatrixGroup m)
    (hπ : Function.Surjective π) (hker : π.ker = seedRadical d .suzuki)
    (hP : IsPGroup 2 (seedRadical d .suzuki)) :
    (standardSeed d .suzuki ⧸ pCore 2 (standardSeed d .suzuki)) ≃*
      SuzukiMatrixGroup m :=
  (QuotientGroup.quotientMulEquivOfEq
      ((suzuki_seedRadical_eq_pCore_of_projection hm d π hπ hker hP).symm.trans
        hker.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)

/-- The induced equivalence sends the coset of `x` to its actual projection. -/
theorem suzuki_coreQuotientEquivOfProjection_mk {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m) (π : standardSeed d .suzuki →* SuzukiMatrixGroup m)
    (hπ : Function.Surjective π) (hker : π.ker = seedRadical d .suzuki)
    (hP : IsPGroup 2 (seedRadical d .suzuki)) (x : standardSeed d .suzuki) :
    suzuki_coreQuotientEquivOfProjection hm d π hπ hker hP
      (QuotientGroup.mk' (pCore 2 (standardSeed d .suzuki)) x) = π x := by
  rfl

/-- A centralizer calculation for the root radical gives local
characteristic two for the intrinsic two-core. -/
theorem suzuki_core_centralizer_le_of_projection {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m) (π : standardSeed d .suzuki →* SuzukiMatrixGroup m)
    (hπ : Function.Surjective π) (hker : π.ker = seedRadical d .suzuki)
    (hP : IsPGroup 2 (seedRadical d .suzuki))
    (hc : centralizer (seedRadical d .suzuki : Set (standardSeed d .suzuki)) ≤
      seedRadical d .suzuki) :
    centralizer (pCore 2 (standardSeed d .suzuki) : Set (standardSeed d .suzuki)) ≤
      pCore 2 (standardSeed d .suzuki) := by
  rwa [suzuki_seedRadical_eq_pCore_of_projection hm d π hπ hker hP] at hc

/-- Self-centralization and the nontrivial Suzuki image force the intrinsic
two-core to be nontrivial; no separate radical nontriviality premise is needed. -/
theorem suzuki_core_ne_bot_of_projection {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m) (π : standardSeed d .suzuki →* SuzukiMatrixGroup m)
    (hπ : Function.Surjective π) (hker : π.ker = seedRadical d .suzuki)
    (hP : IsPGroup 2 (seedRadical d .suzuki))
    (hc : centralizer (seedRadical d .suzuki : Set (standardSeed d .suzuki)) ≤
      seedRadical d .suzuki) :
    pCore 2 (standardSeed d .suzuki) ≠ ⊥ := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  have hcentral := suzuki_core_centralizer_le_of_projection hm d π hπ hker hP hc
  intro hbot
  rw [hbot] at hcentral
  have htriv (x : standardSeed d .suzuki) : x = 1 := by
    apply Subgroup.mem_bot.mp (hcentral ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Subgroup.mem_bot.mp hy]
    simp
  obtain ⟨y, hy⟩ := exists_ne (1 : SuzukiMatrixGroup m)
  obtain ⟨x, rfl⟩ := hπ y
  exact hy (by rw [htriv x, map_one])

/-- The concrete Suzuki radical is normal inside its root-defined seed. -/
theorem suzuki_seedRadical_normal {m : ℕ} (d : LocalBlockInput m) :
    (seedRadical d .suzuki).Normal :=
  suzuki_seedRadical_normal_of_kernel d (SuzukiLeviProjection.projection d)
    (SuzukiLeviProjection.projection_ker d)

/-- The actual root radical is the intrinsic two-core of the Suzuki-side seed. -/
theorem suzuki_seedRadical_eq_pCore {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m) :
    seedRadical d .suzuki = pCore 2 (standardSeed d .suzuki) :=
  suzuki_seedRadical_eq_pCore_of_projection hm d (SuzukiLeviProjection.projection d)
    (SuzukiLeviProjection.projection_surjective d) (SuzukiLeviProjection.projection_ker d)
    (suzuki_seedRadical_isPGroup d)

/-- The root radical is self-centralizing in the seed, with its concrete
Suzuki projection supplied. -/
theorem suzuki_seedRadical_centralizer_le {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m) :
    centralizer (seedRadical d .suzuki : Set (standardSeed d .suzuki)) ≤
      seedRadical d .suzuki :=
  suzuki_seedRadical_centralizer_le_of_projection hm d (SuzukiLeviProjection.projection d)
    (SuzukiLeviProjection.projection_surjective d) (SuzukiLeviProjection.projection_ker d)

/-- The Suzuki-side seed has local characteristic two. -/
theorem suzuki_core_centralizer_le {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m) :
    centralizer (pCore 2 (standardSeed d .suzuki) : Set (standardSeed d .suzuki)) ≤
      pCore 2 (standardSeed d .suzuki) := by
  rw [← suzuki_seedRadical_eq_pCore hm d]
  exact suzuki_seedRadical_centralizer_le hm d

/-- The intrinsic two-core of the Suzuki-side seed is nonidentity. -/
theorem suzuki_core_ne_bot {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m) :
    pCore 2 (standardSeed d .suzuki) ≠ ⊥ :=
  suzuki_core_ne_bot_of_projection hm d (SuzukiLeviProjection.projection d)
    (SuzukiLeviProjection.projection_surjective d) (SuzukiLeviProjection.projection_ker d)
    (suzuki_seedRadical_isPGroup d) (suzuki_seedRadical_centralizer_le hm d)

/-- The quotient by the intrinsic two-core is the concrete Suzuki matrix group. -/
noncomputable def suzuki_coreQuotientEquiv {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m) :
    (standardSeed d .suzuki ⧸ pCore 2 (standardSeed d .suzuki)) ≃*
      SuzukiMatrixGroup m :=
  suzuki_coreQuotientEquivOfProjection hm d (SuzukiLeviProjection.projection d)
    (SuzukiLeviProjection.projection_surjective d) (SuzukiLeviProjection.projection_ker d)
    (suzuki_seedRadical_isPGroup d)

/-- On a coset representative, the quotient equivalence is the actual
projection through the fixed middle-node Levi. -/
@[simp] theorem suzuki_coreQuotientEquiv_mk {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m) (x : standardSeed d .suzuki) :
    suzuki_coreQuotientEquiv hm d
      (QuotientGroup.mk' (pCore 2 (standardSeed d .suzuki)) x) =
        SuzukiLeviProjection.projection d x := rfl

end ReeF4.LargeLocalSeeds

end
