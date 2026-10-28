module

public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.GroupTheory.ComponentLocalOrbitFactors.SubnormalProduct
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Local factors in subnormal p-perfect subgroups

Let L be a simple component, K ≤ L a perfect subgroup simple modulo its
p-core, and A a p-subgroup such that N_A(L) normalizes K. Every nontrivial
subnormal p-perfect subgroup of K ⊔ A contains an A-conjugate of K.

The local-orbit quotient is a p-group, so the subgroup lies in the orbit of
K. Simplicity and perfectness make L centerless. Distinct component
conjugates commute and are independent, giving actual multiplication
coordinates for the orbit. The direct-power result then supplies a
coordinate factor, and its evaluation formula identifies the required
conjugate in the original ambient group.

The coordinate construction refines the proof of `IsComponent.local_orbit_equiv_power`
in `ComponentLocalDirectPower`, retaining the embeddings of the factors.
This is a conditional finite-group calculation for the large Ree case of
Aschbacher–Smith, 2.3.9(7), combined manuscript (1 March 2004), printed p.526;
the source's seed construction and classification assembly are separate.
-/

open Subgroup

namespace Theory.GroupTheory
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

/-- A nontrivial subnormal p-perfect subgroup of the local overgroup contains
an actual conjugate of the perfect seed, provided the seed is simple modulo
its p-core and the ambient component is simple. -/
public theorem IsComponent.exists_local_factor_le_of_isSubnormal_isPPerfect
    [Finite G] {p : ℕ} [Fact p.Prime] {L K A : Subgroup G}
    (hL : IsComponent G L) [IsSimpleGroup L] (hK : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hA : IsPGroup p A) [Group.IsPerfect K] [IsSimpleGroup (K ⧸ pCore p K)]
    (B : Subgroup (K ⊔ A : Subgroup G)) (hs : B.IsSubnormal)
    (hp : IsPPerfect p B) (hne : B ≠ ⊥) :
    ∃ a : A, K.map (MulAut.conj (a : G)).toMonoidHom ≤ B.map (K ⊔ A).subtype := by
  classical
  let := hL.2
  have hZ : center L = ⊥ := by
    rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with hz | ht
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp ht)).elim
  obtain ⟨I, s, e, he⟩ := local_orbit_coordinates hL hZ hK hinv
  let X := K ⊔ A
  let D := (componentOrbit K A).subgroupOf X
  have hBD : B ≤ D := le_local_orbit_of_isPPerfect K A hA B hp
  let eD : D ≃* componentOrbit K A := subgroupOfEquivOfLe (componentOrbit_le_sup K A)
  let t : D ≃* (I → K) := eD.trans e.symm
  let C := (B.subgroupOf D).map t.toMonoidHom
  have hsC : C.IsSubnormal := hs.subgroupOf.map t.surjective
  have hpD : IsPPerfect p (B.subgroupOf D) :=
    hp.of_surjective (subgroupOfEquivOfLe hBD).symm.toMonoidHom
      (subgroupOfEquivOfLe hBD).symm.surjective
  have hpC : IsPPerfect p C := hpD.of_surjective
    (t.toMonoidHom.subgroupMap _) (t.toMonoidHom.subgroupMap_surjective _)
  have hneC : C ≠ ⊥ := by
    intro hz
    have hzero := ((B.subgroupOf D).map_eq_bot_iff_of_injective t.injective).mp hz
    apply hne
    have hm := congrArg (Subgroup.map D.subtype) hzero
    simpa only [map_subgroupOf_eq_of_le hBD, Subgroup.map_bot] using hm
  obtain ⟨i, hi⟩ := exists_mulSingle_mem_of_isSubnormal_isPPerfect
    (pCore p K) pCore_isPGroup C hsC hpC hneC
  refine ⟨s i, ?_⟩
  rintro x ⟨k, hk, rfl⟩
  have hmem := hi (⟨k, hk⟩ : K)
  obtain ⟨b, hb, hbe⟩ := mem_map.mp hmem
  change t b = Pi.mulSingle i (⟨k, hk⟩ : K) at hbe
  have hval : (b : G) = MulAut.conj (s i : G) k := by
    calc
      (b : G) = (e (t b) : G) := by
        change (b : G) = (e (e.symm (eD b)) : G)
        rw [e.apply_symm_apply]
        rfl
      _ = MulAut.conj (s i : G) k := by rw [hbe, he]
  exact mem_map.mpr ⟨b.val, hb, hval⟩

end Theory.GroupTheory
