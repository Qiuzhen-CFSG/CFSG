module
public import Theory.SpecificGroups.Triality.NormalizedRootCentralizers
public import Theory.SpecificGroups.Triality.BinaryParabolicThreeRank
public import Theory.SpecificGroups.Triality.SolvableSylowControl
public import Theory.SpecificGroups.Triality.TwoLocalCover
public import Theory.SpecificGroups.Triality.BinaryCenter
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Three-rank in solvable triality Sylow overgroups fixed by an involution

For a nonbinary field, align the full Sylow with the positive unipotent
subgroup. Solvable Sylow control puts its overgroup in the same Borel.
An inner involution fixing that Sylow belongs to its highest-root center.
Centralizing a nonzero highest-root element kills the base-field torus
coordinate, so the fixed overgroup lies in the arms local factor, of
three-rank at most one. At field size two, both maximal parabolics already
have that rank bound. The actual automorphism and Sylow are preserved.

Source: Aschbacher--Smith 15.2.24, printed p.1117, refs/quasithin.pdf;
the intrinsic torus/root calculations retain their GLS references.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Triality.Standard
open Parabolics ConcreteBruhat ConcreteBruhat.TorusCoordinates RadicalCoordinates
open RadicalCoordinates.Centers NormalizedRootCentralizers

private theorem arms_torus_mem (P : Parameters) (hp : P.prime = 2)
    (x : (ExtensionField P)ˣ) : (torusMulEquiv P hp (x,1)).val ∈ localFactor P .arms := by
  rw [torusMulEquiv_val]
  have hone : foldedTorusElementary P hp .central 1 = 1 := by
    apply LeviCommutators.elementaryInclusion_injective P
    exact (inclusion_foldedTorus_central P hp 1).trans
      ((congrArg (torusWord P 1) (map_one (fixedUnit P))).trans
        ((torusWord_one P hp 1).trans (map_one (elementaryInclusion P)).symm))
  change toCarrier P (foldedTorusElementary P hp .arms x *
    foldedTorusElementary P hp .central 1) ∈ localFactor P .arms
  simp only [hone,mul_one]
  exact levi_le_localFactor P hp .arms (LeviCommutators.torusActor_mem_levi P hp .arms x)

/-- Fixing a nonidentity highest-root element kills the Borel's base-field torus coordinate. -/
theorem borel_highest_centralizer_le_localFactor (P : Parameters) (hp : P.prime = 2)
    (r : Carrier P) (hr : r ∈ highestRoot P) (hne : r ≠ 1) :
    borel P ⊓ centralizer ({r} : Set (Carrier P)) ≤ localFactor P .arms := by
  rw [←highestHom_range P hp] at hr
  obtain ⟨t,rfl⟩ := hr
  have ht : t.toAdd ≠ 0 := by
    intro h
    have he : t = 1 := congrArg Multiplicative.ofAdd h
    exact hne (he ▸ map_one _)
  rintro b ⟨hb,hbc⟩
  have hb' : b ∈ (unipotent P : Set (Carrier P)) * (torus P : Set (Carrier P)) := by
    rw [←borel_eq_mul P hp]
    exact hb
  obtain ⟨u,hu,v,hv,rfl⟩ := hb'
  obtain ⟨⟨x,y⟩,he⟩ := (torusMulEquiv P hp).surjective ⟨v,hv⟩
  have hv' := congrArg Subtype.val he
  have huc : u ∈ centralizer ({highestHom P hp t} : Set (Carrier P)) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := highestRoot_le_center_unipotent P hp
      (show highestHom P hp t ∈ highestRoot P by rw [←highestHom_range P hp]; exact ⟨t,rfl⟩)
    obtain ⟨w,hw,hw'⟩ := hh
    rw [←hw']
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨u,hu⟩)
  have hvc := (centralizer ({highestHom P hp t} : Set (Carrier P))).mul_mem
    ((centralizer _).inv_mem huc) hbc
  simp only [inv_mul_cancel_left] at hvc
  have hconj := torus_conjugate_highestHom P hp (x,y) t.toAdd
  rw [hv'] at hconj
  have hy : y = 1 := by
    have hfix : v * highestHom P hp t * v⁻¹ = highestHom P hp t :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hvc)
    have hs := congrArg Multiplicative.toAdd (highestHom_injective P hp (hconj.symm.trans hfix))
    apply Units.ext
    exact mul_right_cancel₀ ht (hs.trans (one_mul _).symm)
  subst y
  exact (localFactor P .arms).mul_mem
    (unipotent_le_localFactor P .arms (hp.symm ▸ unipotent_isPGroup_binary P hp) hu)
    (by simpa only [he] using arms_torus_mem P hp x)

/-- A solvable Sylow overgroup fixed by a nontrivial inner involution has three-rank at most one. -/
theorem solvable_sylow_fixed_three_rank_le_one (n : ℕ) (hn : 0 < n)
    (a : MulAut (BinaryCarrier n hn)) (ha : orderOf a = 2)
    (hi : a ∈ (MulAut.conj (G := BinaryCarrier n hn)).range)
    (S : Sylow 2 (BinaryCarrier n hn)) (J : Subgroup (BinaryCarrier n hn))
    (hJ : Group.IsSolvable J) (hSJ : (S : Subgroup _) ≤ J) (hfix : J ≤ a.fixedSubgroup) :
    primeRank 3 J ≤ 1 := by
  let P := binaryParameters n hn
  obtain ⟨x,hx,he,hxS,hxcomm⟩ := MulAut.inner_involution_fixing_sylow
    (binaryCarrier_center_eq_bot n hn) S a ha (by obtain ⟨x,hx⟩ := hi; exact ⟨x,hx.symm⟩)
    (fun y hy => (MulAut.mem_fixedSubgroup _ _).mp (hfix (hSJ hy)))
  have hJC : J ≤ centralizer ({x} : Set (Carrier P)) := by
    simpa only [he,MulAut.fixedSubgroup_conj] using hfix
  by_cases hn1 : n = 1
  · subst n
    have hxne : zpowers x ≠ ⊥ := by
      intro h
      have hh := zpowers_eq_bot.mp h
      simp [hh] at hx
    have htwo : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers,hx,pow_one])
    obtain ⟨g,b,hb⟩ := TwoLocalCover.normalizer_cover 1 hn (zpowers x) hxne htwo
    have hCN : centralizer ({x} : Set (BinaryCarrier 1 hn)) ≤ normalizer (zpowers x : Set _) := by
      rw [←centralizer_closure ({x} : Set (BinaryCarrier 1 hn)),←zpowers_eq_closure]
      exact Subgroup.centralizer_le_normalizer _
    have hle := (map_mono (hJC.trans hCN)).trans hb
    rw [primeRank_equiv 3 ((MulAut.conj g).subgroupMap J)]
    exact (primeRank_mono 3 hle).trans
      (parabolic_threeRank_le_one_of_q_eq_two (binaryParameters 1 hn) rfl b)
  · have hn2 : 1 < n := by omega
    obtain ⟨g,e,_,heS⟩ := Theory.GroupTheory.SolvableSylowControl.exists_aligned_equiv
      (MulEquiv.refl (BinaryCarrier n hn)) S (unipotentSylow P rfl)
    have heU : (S : Subgroup (Carrier P)).map e.toMonoidHom = unipotent P := heS
    let J' := J.map e.toMonoidHom
    have hJU : unipotent P ≤ J' := heU ▸ map_mono hSJ
    let : Group.IsSolvable J := hJ
    have hJ's : Group.IsSolvable J' := Group.isSolvable_of_surjective
      (e.toMonoidHom.subgroupMap_surjective J)
    have hJB := SolvableSylowControl.le_borel P rfl
      (show 2 < P.q from lt_of_eq_of_lt (by decide : 2 = 2^1)
        (Nat.pow_lt_pow_right (by decide) hn2)) J' hJ's hJU
    have hxZ : x ∈ (center S).map (S : Subgroup _).subtype :=
      ⟨⟨x,hxS⟩,mem_center_iff.mpr (fun y => Subtype.ext (hxcomm y y.property).eq.symm),rfl⟩
    have heZ : ((center S).map (S : Subgroup _).subtype).map e.toMonoidHom = highestRoot P := by
      rw [map_map,←map_center_image_of_injective (S : Subgroup _) e.toMonoidHom e.injective,heU]
      exact embedded_center_unipotent P rfl
    have heX : e x ∈ highestRoot P := heZ ▸ mem_map_of_mem e.toMonoidHom hxZ
    have hJC' : J' ≤ centralizer ({e x} : Set (Carrier P)) := by
      rintro y ⟨w,hw,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      change e w * e x = e x * e w
      simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp (hJC hw))
    have hle := (le_inf hJB hJC').trans (borel_highest_centralizer_le_localFactor P rfl
      (e x) heX (fun h => by have hh := e.map_eq_one_iff.mp h; simp [hh] at hx))
    rw [primeRank_equiv 3 (e.subgroupMap J)]
    exact (primeRank_mono 3 hle).trans (localFactor_threeRank_le_one P rfl .arms)
end Triality.Standard

