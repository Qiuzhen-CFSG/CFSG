module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks.OrbitFactors.ShortPower
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Short-block factors in an actual component orbit

The multiplication coordinates for the conjugate orbit retain the original
conjugating elements. Two-perfection puts the block inside the orbit, and
the short-power theorem isolates a coordinate. Its evaluation formula then
places the corresponding conjugate of the seed in the original subgroup.

The private coordinates refine the construction in
`Theory.GroupTheory.ComponentLocalDirectPower`; the same refinement is used
in `ComponentLocalOrbitFactors` for perfect seeds. Here the seed may be A₄.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7–8,
printed pp.246–248, using C.1.7 and the component-orbit calculation 2.3.9(7).
-/

open Subgroup Theory.GroupTheory CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks.OrbitFactors
universe u
variable {G : Type u} [Group G]

private theorem orbit_center_eq_bot_of_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hX : center X = ⊥) : center Y = ⊥ := by
  apply eq_bot_iff.mpr
  intro y hy
  have hx : e.symm y ∈ center X := ((centerCongr e).symm ⟨y, hy⟩).property
  have hx1 : e.symm y = 1 := by simpa only [hX, mem_bot] using hx
  apply mem_bot.mpr
  apply e.symm.injective
  simpa using hx1

private theorem orbit_conjugate_conjugate (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem orbit_seed_conjugate_eq {L K A : Subgroup G}
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G)) (a b : A)
    (he : L.map (MulAut.conj (a : G)).toMonoidHom =
      L.map (MulAut.conj (b : G)).toMonoidHom) :
    K.map (MulAut.conj (a : G)).toMonoidHom =
      K.map (MulAut.conj (b : G)).toMonoidHom := by
  have hL : L.map (MulAut.conj ((b⁻¹ * a : A) : G)).toMonoidHom = L := by
    have hh := congrArg (Subgroup.map (MulAut.conj (b : G)⁻¹).toMonoidHom) he
    rw [orbit_conjugate_conjugate, orbit_conjugate_conjugate, inv_mul_cancel, map_one] at hh
    change L.map (MulAut.conj ((b : G)⁻¹ * a)).toMonoidHom = L.map (MonoidHom.id G) at hh
    rw [Subgroup.map_id] at hh
    exact hh
  have hK := mem_normalizer_iff_map_conj_eq.mp
    (hinv ⟨(b⁻¹ * a).property, mem_normalizer_iff_map_conj_eq.mpr hL⟩)
  change K.map (MulAut.conj ((b : G)⁻¹ * a)).toMonoidHom = K at hK
  have hh := congrArg (Subgroup.map (MulAut.conj (b : G)).toMonoidHom) hK
  simpa only [orbit_conjugate_conjugate, Subgroup.coe_mul, Subgroup.coe_inv,
    mul_inv_cancel_left] using hh

private theorem local_orbit_coordinates [Finite G] {L K A : Subgroup G}
    (hL : IsComponent G L) (hZ : center L = ⊥) (hK : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G)) :
    ∃ (I : Type u) (s : I → A) (e : (I → K) ≃* componentOrbit K A),
      letI := Classical.decEq I
      ∀ (i : I) (k : K), (e (Pi.mulSingle i k) : G) =
        MulAut.conj (s i : G) (k : G) := by
  classical
  let I := Set.range (fun a : A => L.map (MulAut.conj (a : G)).toMonoidHom)
  let : DecidableEq I := Classical.decEq I
  let s : I → A := fun i => Classical.choose i.property
  have hs (i : I) : L.map (MulAut.conj (s i : G)).toMonoidHom = i.val :=
    Classical.choose_spec i.property
  let D : I → Subgroup G := fun i => K.map (MulAut.conj (s i : G)).toMonoidHom
  have hDL (i : I) : D i ≤ i.val := hs i ▸ map_mono hK
  have hLi (i : I) : IsComponent G i.val := hs i ▸ hL.map_conj (s i : G)
  have hZi (i : I) : center i.val = ⊥ := by
    rw [← hs i]
    exact orbit_center_eq_bot_of_equiv ((MulAut.conj (s i : G)).subgroupMap L) hZ
  have hcommL (i j : I) (hne : i ≠ j) :
      i.val ≤ centralizer (j.val : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    exact (hLi i).commutator_eq_bot_of_ne (hLi j) (fun hh => hne (Subtype.ext hh))
  have hind : iSupIndep D := by
    rw [iSupIndep_def]
    intro i
    apply Subgroup.disjoint_def.mpr
    intro x hx hi
    have hothers : (⨆ j, ⨆ (_ : j ≠ i), D j) ≤ centralizer (i.val : Set G) := by
      exact iSup_le fun j => iSup_le fun hji => (hDL j).trans (hcommL j i hji)
    have hz : (⟨x, hDL i hx⟩ : i.val) ∈ center i.val := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      exact mem_centralizer_iff.mp (hothers hi) y y.property
    have hx1 : (⟨x, hDL i hx⟩ : i.val) = 1 := by simpa only [hZi i, mem_bot] using hz
    exact congrArg Subtype.val hx1
  have hsup : (⨆ i, D i) = componentOrbit K A := by
    apply le_antisymm
    · exact iSup_le fun i => le_iSup (fun a : A => K.map (MulAut.conj (a : G)).toMonoidHom) (s i)
    · apply iSup_le
      intro a
      let i : I := ⟨L.map (MulAut.conj (a : G)).toMonoidHom, ⟨a, rfl⟩⟩
      have he : D i = K.map (MulAut.conj (a : G)).toMonoidHom :=
        orbit_seed_conjugate_eq hinv (s i) a (hs i)
      exact he ▸ le_iSup D i
  let φ : I → K →* G := fun i => (MulAut.conj (s i : G)).toMonoidHom.comp K.subtype
  have hrφ (i : I) : (φ i).range = D i := by
    dsimp [φ, D]
    rw [MonoidHom.range_comp, K.range_subtype]
  have hcomm : Pairwise fun i j : I => ∀ x y : K, Commute (φ i x) (φ j y) := by
    intro i j hij x y
    exact (mem_centralizer_iff.mp (hcommL i j hij
      (hDL i (mem_map_of_mem _ x.property))) _ (hDL j (mem_map_of_mem _ y.property))).symm
  let : Fintype I := Fintype.ofFinite I
  let f : (I → K) →* G := MonoidHom.noncommPiCoprod φ hcomm
  have hf : Function.Injective f := MonoidHom.injective_noncommPiCoprod_of_iSupIndep φ
    (by simpa only [hrφ] using hind)
    (fun i => (MulAut.conj (s i : G)).injective.comp K.subtype_injective)
  have hr : f.range = componentOrbit K A := by
    rw [MonoidHom.noncommPiCoprod_range, show (fun i => (φ i).range) = D from funext hrφ, hsup]
  let e : (I → K) ≃* componentOrbit K A :=
    (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)
  refine ⟨I, s, e, ?_⟩
  intro i k
  simp only [e, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  exact MonoidHom.noncommPiCoprod_mulSingle φ (hcomm := hcomm) i k

/-- The isolated short-block coordinate is an actual conjugate of the seed. -/
public theorem local_short_factor [Finite G] {L K A : Subgroup G}
    (hL : IsComponent G L) (hZ : center L = ⊥) (hKL : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hA : IsPGroup 2 A) (hK : IsPPerfect 2 K) (hKZ : center K = ⊥)
    (P : Subgroup K) [P.Normal] [IsSimpleGroup (K ⧸ P)]
    (hP : IsPGroup 2 P) (hne : P ≠ ⊥) (hcomm : ⁅P, (⊤ : Subgroup K)⁆ = P)
    {D : Type*} [Group D] (hD : IsShort D)
    (f : D →* (K ⊔ A : Subgroup G)) (hf : Function.Injective f)
    (hs : f.range.IsSubnormal) :
    ∃ a : A, K.map (MulAut.conj (a : G)).toMonoidHom ≤
      f.range.map (K ⊔ A).subtype := by
  classical
  obtain ⟨I, s, e, he⟩ := local_orbit_coordinates hL hZ hKL hinv
  let X := K ⊔ A
  let N := (componentOrbit K A).subgroupOf X
  have hp : IsPPerfect 2 f.range :=
    hD.twoPerfect.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hN : f.range ≤ N := le_local_orbit_of_isPPerfect K A hA f.range hp
  let r : D →* N := f.codRestrict N (fun d => hN ⟨d, rfl⟩)
  have hr : Function.Injective r := fun x y hh => hf (congrArg Subtype.val hh)
  have hrange : r.range = f.range.subgroupOf N := by
    ext x
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨d, rfl⟩
    · rintro ⟨d, hd⟩
      exact ⟨d, Subtype.ext hd⟩
  let eN : N ≃* componentOrbit K A := subgroupOfEquivOfLe (componentOrbit_le_sup K A)
  let t : N ≃* (I → K) := eN.trans e.symm
  let g : D →* (I → K) := t.toMonoidHom.comp r
  have hg : Function.Injective g := t.injective.comp hr
  have hsg : g.range.IsSubnormal := by
    rw [MonoidHom.range_comp, hrange]
    exact hs.subgroupOf.map t.surjective
  obtain ⟨i, hi⟩ := short_factor hK hKZ P hP hne hcomm hD g hg hsg
  refine ⟨s i, ?_⟩
  rintro x ⟨k, hk, rfl⟩
  obtain ⟨d, hd⟩ := hi (⟨k, hk⟩ : K)
  have hval : ((f d : X) : G) = MulAut.conj (s i : G) k := by
    calc
      ((f d : X) : G) = (e (g d) : G) := by
        change ((f d : X) : G) = (e (e.symm (eN (r d))) : G)
        rw [e.apply_symm_apply]
        rfl
      _ = MulAut.conj (s i : G) k := by rw [hd, he]
  exact mem_map.mpr ⟨f d, ⟨d, rfl⟩, hval⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks.OrbitFactors
