module

public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationContracts
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.SourceChecks
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product00
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product01
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product02
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product03
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product04
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product05
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product06
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product07
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product08
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product09
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product10
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product11
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product12
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product13
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product14
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product15
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product16
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product17
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product18
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product19
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product20
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product21
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product22
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product23
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Product24

/-!
# Exact generator matrices of the Lyons local program

The twenty-five certified products implement all sixteen instructions of
`max1Program`, using addition chains for powers seven and twenty-five.
One-sided inverse checks identify the three inverse candidates with inverses
of the existing matrix units. Thus the four fixed seed matrices are exactly
the identity and the letter values in the local presentation.

Source: R. A. Wilson et al., ATLAS of Finite Group Representations,
`Atlas111OrderSource/LyG1-max1W1`; original matrices in `Atlas111Source/`.
Candidate generation: `Atlas111LocalRelationSeedSource/Generate.py`.
No subgroup identification, group order, or simplicity premise is used.
-/

namespace Lyons.RelationCertificate

public theorem seedIdentities : SeedIdentities := by
  let u3 := atlasA * atlasB
  have h3 : decode Seed.r3 = ↑u3 :=
    Seed.mul_value _ _ Seed.a_eq Seed.b_eq Seed.mul_r3
  let u4 := u3 * atlasB
  have h4 : decode Seed.r4 = ↑u4 := Seed.mul_value _ _ h3 Seed.b_eq Seed.mul_r4
  let u5 := u3 * u4
  have h5 : decode Seed.r5 = ↑u5 := Seed.mul_value _ _ h3 h4 Seed.mul_r5
  let u9 := u5 * atlasB
  have h9 : decode Seed.r9 = ↑u9 := Seed.mul_value _ _ h5 Seed.b_eq Seed.mul_r9
  let u6 := u3 * u5
  have h6 : decode Seed.r6 = ↑u6 := Seed.mul_value _ _ h3 h5 Seed.mul_r6
  let u7 := u6 * u3
  have h7 : decode Seed.r7 = ↑u7 := Seed.mul_value _ _ h6 h3 Seed.mul_r7
  let u8 := u7 * u7
  have h8 : decode Seed.r8 = ↑u8 := Seed.mul_value _ _ h7 h7 Seed.mul_r8
  let u2 := u7 * u8
  have h2 : decode Seed.r2 = ↑u2 := Seed.mul_value _ _ h7 h8 Seed.mul_r2
  have hp2 : decode Seed.p2 = ↑(u9 ^ 2) := by
    simpa only [pow_two] using Seed.mul_value _ _ h9 h9 Seed.mul_p2
  have hp4 : decode Seed.p4 = ↑(u9 ^ 4) := by
    simpa only [← pow_add] using Seed.mul_value _ _ hp2 hp2 Seed.mul_p4
  have hp6 : decode Seed.p6 = ↑(u9 ^ 6) := by
    simpa only [← pow_add] using Seed.mul_value _ _ hp2 hp4 Seed.mul_p6
  have hp7 : decode Seed.p7 = ↑(u9 ^ 7) := by
    simpa only [← pow_succ'] using Seed.mul_value _ _ h9 hp6 Seed.mul_p7
  have hpi : decode Seed.pi = ↑((u9 ^ 7)⁻¹) :=
    Seed.inv_value _ hp7 (Seed.mul_pi.trans Seed.one_eq)
  have hpa : decode Seed.pa = ↑(u9 ^ 7 * atlasA) :=
    Seed.mul_value _ _ hp7 Seed.a_eq Seed.mul_pa
  have hm1 : decode m1 = ↑(u9 ^ 7 * atlasA * (u9 ^ 7)⁻¹) :=
    Seed.mul_value _ _ hpa hpi Seed.mul_m1
  have hq2 : decode Seed.q2 = ↑(u6 ^ 2) := by
    simpa only [pow_two] using Seed.mul_value _ _ h6 h6 Seed.mul_q2
  have hq4 : decode Seed.q4 = ↑(u6 ^ 4) := by
    simpa only [← pow_add] using Seed.mul_value _ _ hq2 hq2 Seed.mul_q4
  have hq8 : decode Seed.q8 = ↑(u6 ^ 8) := by
    simpa only [← pow_add] using Seed.mul_value _ _ hq4 hq4 Seed.mul_q8
  have hq16 : decode Seed.q16 = ↑(u6 ^ 16) := by
    simpa only [← pow_add] using Seed.mul_value _ _ hq8 hq8 Seed.mul_q16
  have hq24 : decode Seed.q24 = ↑(u6 ^ 24) := by
    simpa only [← pow_add] using Seed.mul_value _ _ hq8 hq16 Seed.mul_q24
  have hq25 : decode Seed.q25 = ↑(u6 ^ 25) := by
    simpa only [← pow_succ'] using Seed.mul_value _ _ h6 hq24 Seed.mul_q25
  have hqi : decode Seed.qi = ↑((u6 ^ 25)⁻¹) :=
    Seed.inv_value _ hq25 (Seed.mul_qi.trans Seed.one_eq)
  have hqr : decode Seed.qr = ↑((u6 ^ 25)⁻¹ * u2) :=
    Seed.mul_value _ _ hqi h2 Seed.mul_qr
  have hm2 : decode m2 = ↑((u6 ^ 25)⁻¹ * u2 * u6 ^ 25) :=
    Seed.mul_value _ _ hqr hq25 Seed.mul_m2
  have hm3 : decode m3 = ↑(((u6 ^ 25)⁻¹ * u2 * u6 ^ 25)⁻¹) :=
    Seed.inv_value _ hm2 (Seed.mul_m3.trans Seed.one_eq)
  exact ⟨Seed.one_eq, hm1, hm2, hm3⟩

end Lyons.RelationCertificate
