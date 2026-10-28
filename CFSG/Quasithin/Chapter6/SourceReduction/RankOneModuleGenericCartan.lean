module

public import CFSG.Quasithin.Chapter6.SourceDefs
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard
public import Theory.GroupTheory.Hall.OddNormalProducts
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The literal Cartan and residual subgroups in the generic rank-one case

Notation 5.1.9 chooses odd Hall subgroups D of N_L(T ∩ L) and B of
N_G(L) ∩ H, with B normalizing D. The obstruction removed in 5.2.2 is
whether D normalizes the actual embedded O²(H). These definitions retain
both Hall conditions, including their relative ambient groups.

The Sylow supplement shows that this residual escapes N_G(L) whenever
H does. The Hall supplement and residual normality give the product and
normalization used in 5.2.4. None of these assertions recognizes the
resulting amalgam or its completion.

Source: Aschbacher--Smith, 5.1.9 and 5.2.2--5.2.5, pp.634,646--650.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The earlier hypotheses of 5.2.3 at M=N_G(L), with the standing outside
guard. The selected reduced subgroup W is retained in its original ambient
group. No exceptional-module or global-recognition conclusion is a field. -/
structure Input (κ : GroupClass.{u}) (T : Sylow 2 G)
    (L W : Subgroup G) (n : ℕ) : Prop where
  qtke : IsSimpleQTKE κ G
  local_mem : L ∈ faithfulMaximalFamily (T : Subgroup G)
  exponent : 1 < n
  linear : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)
  maximal : IsMaximalTwoLocal (normalizer (L : Set G))
  sylow_normalizes : (T : Subgroup G) ≤ normalizer (L : Set G)
  reduced : W ∈ reducedFamily (L ⊔ (T : Subgroup G))
  noncentral : ⁅W, L⁆ ≠ ⊥
  outside : Chapter3.HasMaximalOutside T (normalizer (L : Set G))

/-- The source K, using the inclusion of H into the original ambient group. -/
abbrev residual (H : Subgroup G) : Subgroup G := (pResidual 2 H).map H.subtype

/-- The source N_L(T ∩ L), kept in the original ambient group. -/
abbrev localBorel (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  L ⊓ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)

omit [Finite G] in
/-- The ambient intersection is exactly the image of the relative normalizer,
so the branch condition does not change when using intrinsic notation. -/
theorem localBorel_eq_map (T : Sylow 2 G) (L : Subgroup G) :
    localBorel T L =
      (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype := by
  rw [← inf_subgroupOf_right (T : Subgroup G) L,
    ← subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ L ≤ L from inf_le_right),
    subgroupOf_map_subtype, inf_comm]

private theorem sylow_intersection (T : Sylow 2 G) (L : Subgroup G)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  let J := L ⊔ (T : Subgroup G)
  have hLJ : L ≤ J := le_sup_left
  let : (L.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTL)
  obtain ⟨P, hP⟩ :=
    (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal
      (L.subgroupOf J)
  let e := subgroupOfEquivOfLe hLJ
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (P : Subgroup (L.subgroupOf J)).map e.toMonoidHom = _
  rw [hP]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x, hLJ x.property⟩, x.property⟩, hx, rfl⟩

/-- The local Borel has the literal Sylow intersection T∩L. -/
theorem exists_sylow_localBorel (T : Sylow 2 G) (L : Subgroup G)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ S : Sylow 2 (localBorel T L),
      (S : Subgroup (localBorel T L)).map (localBorel T L).subtype =
        (T : Subgroup G) ⊓ L := by
  obtain ⟨P, hP⟩ := sylow_intersection T L hTL
  let f := inclusion (show localBorel T L ≤ L from inf_le_left)
  have hPf : (P : Subgroup L) ≤ f.range := by
    intro x hx
    have hxT : (x : G) ∈ (T : Subgroup G) := by
      simpa only [hP, mem_subgroupOf] using hx
    exact ⟨⟨x, x.property, ((T : Subgroup G) ⊓ L).le_normalizer ⟨hxT, x.property⟩⟩, rfl⟩
  refine ⟨P.comapOfInjective f (inclusion_injective _) hPf, ?_⟩
  change ((P : Subgroup L).comap f).map (localBorel T L).subtype = _
  rw [hP]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property.1⟩
  · intro hx
    exact ⟨⟨x, hx.2, ((T : Subgroup G) ⊓ L).le_normalizer hx⟩, hx.1, rfl⟩

/-- The two Hall subgroups in Notation 5.1.9, with their actual inclusions.
Normalization of O²(H) is deliberately a separate source obligation. -/
structure CartanPair (T : Sylow 2 G) (L H D B : Subgroup G) : Prop where
  left_le : D ≤ localBorel T L
  left_hall : IsHallSubgroup OddHall.oddPrimes (D.subgroupOf (localBorel T L))
  right_le : B ≤ normalizer (L : Set G) ⊓ H
  right_hall : IsHallSubgroup OddHall.oddPrimes
    (B.subgroupOf (normalizer (L : Set G) ⊓ H))
  right_normalizes_left : B ≤ normalizer (D : Set G)

/-- Every source Cartan supplements the actual Sylow intersection in N_L(T∩L). -/
theorem CartanPair.left_sup_intersection {T : Sylow 2 G} {L H D B : Subgroup G}
    (c : CartanPair T L H D B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ((T : Subgroup G) ⊓ L) ⊔ D = localBorel T L := by
  obtain ⟨S, hS⟩ := exists_sylow_localBorel T L hTL
  have he := congrArg (fun A : Subgroup (localBorel T L) =>
    A.map (localBorel T L).subtype)
    (OddHall.sylow_complement_of_hall S c.left_hall).sup_eq_top
  simpa only [Subgroup.map_sup, hS, map_subgroupOf_eq_of_le c.left_le,
    ← MonoidHom.range_eq_map, range_subtype] using he

/-- The literal source residual is supplemented by the ambient Sylow subgroup. -/
theorem residual_sup_sylow (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) : residual H ⊔ (T : Subgroup G) = H := by
  have he := congrArg (fun A : Subgroup H => A.map H.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTH))
  simpa only [Subgroup.map_sup, Sylow.coe_subtype,
    map_subgroupOf_eq_of_le hTH, ← MonoidHom.range_eq_map, range_subtype] using he

/-- H escaping a Sylow overgroup forces its actual residual to escape it. -/
theorem residual_not_le (T : Sylow 2 G) (H M : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hTM : (T : Subgroup G) ≤ M)
    (hout : ¬ H ≤ M) : ¬ residual H ≤ M := by
  intro hK
  apply hout
  rw [← residual_sup_sylow T H hTH]
  exact sup_le hK hTM

omit [Finite G] in
/-- Relative normality in H yields ambient normalization of its embedded residual. -/
theorem le_normalizer_residual (H : Subgroup G) :
    H ≤ normalizer (residual H : Set G) := by
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    (pResidual 2 H).le_normalizer_map H.subtype

/-- Testing normalization on the source odd Cartan is equivalent to testing
it on the full relative Borel: T∩L already normalizes O²(H). -/
theorem CartanPair.normalizes_residual_iff {T : Sylow 2 G} {L H D B : Subgroup G}
    (c : CartanPair T L H D B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) :
    D ≤ normalizer (residual H : Set G) ↔
      localBorel T L ≤ normalizer (residual H : Set G) := by
  constructor
  · intro hD
    rw [← c.left_sup_intersection hTL]
    exact sup_le (inf_le_left.trans (hTH.trans (le_normalizer_residual H))) hD
  · exact fun hN => c.left_le.trans hN

/-- The Hall condition gives the literal product supplement from 5.1.9.
The complement statement is inside N_G(L) ∩ H. -/
theorem CartanPair.sylow_complement {T : Sylow 2 G} {L H D B : Subgroup G}
    (c : CartanPair T L H D B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) :
    ((T : Subgroup G).subgroupOf (normalizer (L : Set G) ⊓ H)).IsComplement'
      (B.subgroupOf (normalizer (L : Set G) ⊓ H)) :=
  OddHall.sylow_complement_of_hall (T.subtype (le_inf hTL hTH)) c.right_hall

/-- The original B and T generate exactly M ∩ H, rather than an arbitrary
overgroup of that intersection. -/
theorem CartanPair.sylow_sup_right {T : Sylow 2 G} {L H D B : Subgroup G}
    (c : CartanPair T L H D B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) :
    (T : Subgroup G) ⊔ B = normalizer (L : Set G) ⊓ H := by
  have he := congrArg
    (fun A : Subgroup (normalizer (L : Set G) ⊓ H : Subgroup G) =>
      A.map (normalizer (L : Set G) ⊓ H).subtype)
    (c.sylow_complement hTL hTH).sup_eq_top
  simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le (le_inf hTL hTH),
    map_subgroupOf_eq_of_le c.right_le, ← MonoidHom.range_eq_map, range_subtype] using he

omit [Finite G] in
/-- The normalized-Cartan branch acts on the same residual even after adjoining
the entire intersection M ∩ H, as needed to form the second parabolic. -/
theorem CartanPair.generated_normalizes_residual {T : Sylow 2 G}
    {L H D B : Subgroup G} (c : CartanPair T L H D B)
    (hTH : (T : Subgroup G) ≤ H)
    (hD : D ≤ normalizer (residual H : Set G)) :
    D ⊔ (T : Subgroup G) ⊔ B ≤ normalizer (residual H : Set G) := by
  exact sup_le (sup_le hD (hTH.trans (le_normalizer_residual H)))
    ((c.right_le.trans inf_le_right).trans (le_normalizer_residual H))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
