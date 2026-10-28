module

public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableParabolic.RankOne
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic
public import Mathlib.Algebra.CharP.Reduced

/-!
# Solvable Sylow overgroups in the full Sp₄ parabolics

Over a nonbinary finite field of characteristic two, a solvable subgroup
containing an ambient Sylow two-subgroup and lying in either full standard
parabolic normalizes that Sylow subgroup. The carrier is the actual matrix
group `Matrix.symplecticGroup (Fin 2) F`.

Every two-subgroup of a parabolic lies in its determinant-one local factor,
since the field units have no nonidentity element of two-power order. Intersect
the solvable overgroup with that normal factor and project onto SL₂. The
projection has a two-group kernel, hence maps Sylow subgroups to Sylow
subgroups and lifts their normalization. Its solvable image is proper because
nonbinary SL₂ is perfect and nontrivial. The rank-one matrix theorem therefore
gives normalization in the intersection. A normal Sylow subgroup of this
intersection is characteristic, so the entire solvable overgroup normalizes it.

Both the point and plane arguments use their actual surjective matrix quotient
maps and elementary abelian kernels. Normality of each local factor is relative
to its full parabolic throughout.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
`refs/quasithin.pdf`, the characteristic-two paragraph in the proof of
Proposition 1.3.4, printed p.511 (PDF p.528). This supplies the parabolic-to-Borel
step; placement of the original permuting pair is a separate theorem.
-/

@[expose] public section

open Matrix Subgroup
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem normalizes_of_projection {G : Type*} [Group G] [Finite G]
    (hF : 2 < Nat.card F) (f : G →* SpecialLinearGroup (Fin 2) F)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 G) (H : Subgroup G) [Group.IsSolvable H]
    (hSH : (S : Subgroup G) ≤ H) : H ≤ normalizer (S : Set G) := by
  let T := S.mapSurjective hf
  have hsol : Group.IsSolvable (H.map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective H)
  have hproper : H.map f ≠ ⊤ := by
    intro ht
    let _ := hsol
    let _ := NaturalExtension.model_perfect hF
    let _ : Nontrivial (SpecialLinearGroup (Fin 2) F) :=
      Function.Injective.nontrivial (SpecialLinearGroup.upperUnipotentHom_injective F)
    have hSL : Group.IsSolvable (SpecialLinearGroup (Fin 2) F) :=
      Group.isSolvable_of_surjective (f := (H.map f).subtype)
        (by rw [ht]; exact topEquiv.surjective)
    exact Group.IsPerfect.not_isSolvable _ hSL
  have hnorm := SolvableParabolic.proper_sylow_overgroup T (H.map f) hproper
    (map_mono hSH)
  have hker : f.ker ≤ (S : Subgroup G) := hk.le_sylow_of_normal S
  have hpre := (map_le_iff_le_comap.mp hnorm).trans
    ((T : Subgroup (SpecialLinearGroup (Fin 2) F)).le_normalizer_comap f)
  simpa only [T, Sylow.coe_mapSurjective, comap_map_eq_self hker, Sylow.coe_coe] using hpre

private theorem normalizes_of_intermediate {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (L H : Subgroup G) (hTL : (T : Subgroup G) ≤ L)
    (hLN : L ≤ normalizer (T : Set G)) (hHL : H ≤ normalizer (L : Set G)) :
    H ≤ normalizer (T : Set G) := by
  let S := T.subtype hTL
  have hSN : S.Normal := (normal_subgroupOf_iff_le_normalizer hTL).mpr hLN
  have hSC : S.Characteristic := S.characteristic_of_normal hSN
  apply Subgroup.le_normalizer_iff.mpr
  intro h hh t ht
  let a := L.normalizerMonoidHom ⟨h, hHL hh⟩
  have hfix := hSC.fixed a
  have hmem : a ⟨t, hTL ht⟩ ∈ (S : Subgroup L) := by
    change (⟨t, hTL ht⟩ : L) ∈ (S : Subgroup L).comap a.toMonoidHom
    rw [hfix]
    exact ht
  exact hmem

private theorem normalizes_of_local_factor {G : Type*} [Group G] [Finite G]
    (hF : 2 < Nat.card F) (K H : Subgroup G)
    (f : K →* SpecialLinearGroup (Fin 2) F)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (T : Sylow 2 G) [Group.IsSolvable H]
    (hTH : (T : Subgroup G) ≤ H) (hTK : (T : Subgroup G) ≤ K)
    (hHK : H ≤ normalizer (K : Set G)) : H ≤ normalizer (T : Set G) := by
  have hsol : Group.IsSolvable (H.subgroupOf K) := by
    let j : H.subgroupOf K →* H :=
      { toFun := fun x => ⟨x.val.val, x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := j)
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : H => (x : G)) h)))
  let _ := hsol
  have hlocal := normalizes_of_projection hF f hf hk (T.subtype hTK)
    (H.subgroupOf K) (fun _ hx => hTH hx)
  have hLN : H ⊓ K ≤ normalizer (T : Set G) := by
    intro x hx
    have hh := hlocal (show (⟨x, hx.2⟩ : K) ∈ H.subgroupOf K from hx.1)
    change (⟨x, hx.2⟩ : K) ∈ normalizer ((T : Subgroup G).subgroupOf K) at hh
    rw [← subgroupOf_normalizer_eq hTK] at hh
    exact hh
  exact normalizes_of_intermediate T (H ⊓ K) H (le_inf hTH hTK) hLN
    ((le_inf H.le_normalizer hHK).trans inf_normalizer_le_normalizer_inf)

omit [Finite F] in
private theorem two_subgroup_le_determinantKernel
    (W : Submodule F (Vector F)) (T : Sylow 2 (Sp F))
    (hT : (T : Subgroup (Sp F)) ≤ stabilizer W) :
    (T : Subgroup (Sp F)) ≤ determinantKernel W := by
  intro t ht
  let x : stabilizer W := ⟨t, hT ht⟩
  obtain ⟨n, hn⟩ := T.isPGroup'.exists_pow_pow_eq_one ⟨t, ht⟩
  have hx : x ^ (2 ^ n) = 1 := Subtype.ext (congrArg (fun y : T => (y : Sp F)) hn)
  have hp : ((determinantCharacter W x : Fˣ) : F) ^ (2 ^ n) = 1 := by
    have he := congrArg (fun u : Fˣ => (u : F)) (congrArg (determinantCharacter W) hx)
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using he
  have hchar : determinantCharacter W x = 1 := by
    apply Units.ext
    simpa only [pow_one, Units.val_one] using
      (ExpChar.pow_prime_pow_mul_eq_one_iff 2 n 1
      ((determinantCharacter W x : Fˣ) : F)).mp (by simpa using hp)
  exact ⟨x, hchar, rfl⟩

/-- A solvable Sylow overgroup inside the full point parabolic normalizes that Sylow subgroup. -/
theorem solvable_pointParabolic_le_normalizer
    (hF : 2 < Nat.card F) (T : Sylow 2 (Sp F)) (H : Subgroup (Sp F))
    (hsol : Group.IsSolvable H) (hTH : (T : Subgroup (Sp F)) ≤ H)
    (hHP : H ≤ pointParabolic) : H ≤ normalizer (T : Set (Sp F)) := by
  let _ := hsol
  exact normalizes_of_local_factor hF pointLocal H pointQuotient pointQuotient_surjective
    (IsElementaryAbelian.isPGroup 2 (pointRadical (F := F))) T hTH
    (two_subgroup_le_determinantKernel (point F) T (hTH.trans hHP))
    (hHP.trans (le_normalizer_of_normal_subgroupOf pointLocal_le))

/-- A solvable Sylow overgroup inside the full plane parabolic normalizes that Sylow subgroup. -/
theorem solvable_planeParabolic_le_normalizer
    (hF : 2 < Nat.card F) (T : Sylow 2 (Sp F)) (H : Subgroup (Sp F))
    (hsol : Group.IsSolvable H) (hTH : (T : Subgroup (Sp F)) ≤ H)
    (hHP : H ≤ planeParabolic) : H ≤ normalizer (T : Set (Sp F)) := by
  let _ := hsol
  exact normalizes_of_local_factor hF planeLocal H Plane.quotientMap Plane.quotientMap_surjective
    (IsElementaryAbelian.isPGroup 2 (Plane.radical (F := F))) T hTH
    (two_subgroup_le_determinantKernel (plane F) T (hTH.trans hHP))
    (hHP.trans (le_normalizer_of_normal_subgroupOf planeLocal_le))

/-- In either full parabolic of Sp₄(F), a solvable overgroup of a Sylow two-subgroup
normalizes it, for a nonbinary finite field of characteristic two. -/
theorem solvable_parabolic_le_normalizer
    (hF : 2 < Nat.card F) (T : Sylow 2 (Sp F)) (H : Subgroup (Sp F))
    (hsol : Group.IsSolvable H) (hTH : (T : Subgroup (Sp F)) ≤ H)
    (hpar : H ≤ pointParabolic ∨ H ≤ planeParabolic) :
    H ≤ normalizer (T : Set (Sp F)) := by
  rcases hpar with hp | hp
  · exact solvable_pointParabolic_le_normalizer hF T H hsol hTH hp
  · exact solvable_planeParabolic_le_normalizer hF T H hsol hTH hp

end Theory.SpecificGroups.SymplecticFour
