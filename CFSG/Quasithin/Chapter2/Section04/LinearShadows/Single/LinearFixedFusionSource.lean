module
public import Theory.GroupTheory.TIFixedElementaryPair
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFieldKernelSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ElementarySource
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# Excluding fusion to a full-center centralizer

Transport the actual distinguished elementary subgroup into the marked
Sylow centralizer. Strong involution closure places its image in R. The
two elementary factors of R and the fixed-plane order bound force that
image to be one fixed plane. Its nontrivial intersection with Z and the
TI property then force the whole Z to be fixed, contrary to C_S(Z)=R.

The original source data prove the nontrivial and proper fixed-center
conditions. The second fixed-plane bound is transported through the
specified outside element centralizing s. Only the first fixed-plane
bound, earlier involution closure/TI, and the actual Sylow centralizer
remain explicit source inputs. This is the linear outside-involution
case in Aschbacher–Smith, printed p.539.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_not_conj_of_full_center_centralized
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hZ : center (d.block.map d.H.subtype) = ⊥)
    (hTI : ChapterI.Section06To08.IsTISubgroup (distinguishedZ d))
    (s : T) (hsS : (s : G) ∈ (d.S : Subgroup d.H).map d.H.subtype)
    (hsR : (s : G) ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (hclosed : ∀ r t : T, orderOf r = 2 →
      (r : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      IsConj (r : G) (t : G) →
      (t : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (hSylow : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(s : G)} : Set G))
      (centralizer ({(s : G)} : Set G)))
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (hU : Nat.card ((ChapterC.Section05.ConjugateSource.sourceModule
      (d.block.map d.H.subtype)) ⊓ centralizer ({(s : G)} : Set G) : Subgroup G) ≤ 2^n)
    (hxs : x ∈ centralizer ({(s : G)} : Set G))
    (i : G) (hiZ : distinguishedZ d ≤ centralizer ({i} : Set G)) : ¬ IsConj i (s : G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let U := ChapterC.Section05.ConjugateSource.sourceModule (d.block.map d.H.subtype)
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let Z := distinguishedZ d
  have hV : Nat.card (V ⊓ centralizer ({(s : G)} : Set G) : Subgroup G) ≤ 2^n := by
    have hxN : x⁻¹ ∈ normalizer (centralizer ({(s : G)} : Set G) : Set G) :=
      (centralizer ({(s : G)} : Set G)).le_normalizer
        ((centralizer ({(s : G)} : Set G)).inv_mem hxs)
    have hc := mem_normalizer_iff_map_conj_eq.mp hxN
    change (centralizer ({(s : G)} : Set G)).map (MulAut.conj x⁻¹).toMonoidHom =
      centralizer ({(s : G)} : Set G) at hc
    have he : (U ⊓ centralizer ({(s : G)} : Set G)).map (MulAut.conj x⁻¹).toMonoidHom =
        V ⊓ centralizer ({(s : G)} : Set G) := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,hc]
    rw [←he,card_map_of_injective (MulAut.conj x⁻¹).injective]
    exact hU
  have hdata := source_distinguished_elementary d hG T hST hsingle hL hM hTM hu
  let : IsElementaryAbelian 2 Z := hdata.1
  have hZR : Z ≤ R := hdata.2.2.1.trans inf_le_left
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hZT : Z ≤ (T : Subgroup G) := hZR.trans (hRS.trans hST.le)
  have hUV : Z = U ⊓ V := by
    change distinguishedZ d = U ⊓ V
    rw [distinguishedZ_of_centerless d hZ]
    exact (source_absorbed_center_pair d hG T hST hsingle hL hM hTM hu x hxT hxS).symm
  have hZn : Z ≠ ⊥ := by
    intro he
    have hc := hdata.2.1
    change Nat.card Z = 2^n at hc
    rw [he] at hc
    have hc' : 1 = 2^n := by simpa using hc
    have hp : 1 < 2^n := Nat.one_lt_pow (by have := hL.1; omega) (by decide)
    omega
  let : (Z.subgroupOf (T : Subgroup G)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hZT).mpr
      (source_distinguished_normalized_by_sylow d hG T hST hsingle hL hZ)
  have hZTin : Z.subgroupOf (T : Subgroup G) ≠ ⊥ := by
    intro he
    apply hZn
    have hh := congrArg (fun A : Subgroup T => A.map (T : Subgroup G).subtype) he
    simpa only [map_subgroupOf_eq_of_le hZT,Subgroup.map_bot] using hh
  have hfixed : Z ⊓ centralizer ({(s : G)} : Set G) ≠ ⊥ := by
    have hc := center_inf_ne_bot_of_normal T.isPGroup' (Z.subgroupOf (T : Subgroup G)) hZTin
    intro he
    apply hc
    apply eq_bot_iff.mpr
    rintro a ⟨haC,haZ⟩
    apply mem_bot.mpr
    apply Subtype.ext
    have ha : (a : G) ∈ Z ⊓ centralizer ({(s : G)} : Set G) := by
      refine ⟨haZ,mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val ((mem_center_iff.mp haC s).symm)
    exact mem_bot.mp (he ▸ ha)
  have hproper : ¬ Z ≤ centralizer ({(s : G)} : Set G) := by
    intro hh
    apply hsR
    have hsZ : (s : G) ∈ centralizer (Z : Set G) := by
      intro z hz
      exact mem_centralizer_singleton_iff.mp (hh hz)
    have hm : (s : G) ∈ S ⊓ centralizer (Z : Set G) := ⟨hsS,hsZ⟩
    exact (source_distinguished_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hu) ▸ hm
  apply not_conj_of_fixed_ti_elementary_pair T R U V Z (hRS.trans hST.le) hZR
    (hUV ▸ inf_le_left) (hUV ▸ inf_le_right)
    (source_elementary_subgroup_pair d hG T hST hsingle hL hM hTM hu x hxT hxS).2
    hTI.eq_or_disjoint_conjugate hclosed (s : G) i hSylow hiZ
    (hdata.2.1 ▸ hU) (hdata.2.1 ▸ hV) hfixed hproper
end CFSG.Quasithin.Chapter2.LinearShadows.Single
