module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Direct powers of local subgroups in centerless component orbits

Let L be a centerless component, K a subgroup of L, and A a subgroup whose
intersection with N(L) normalizes K. The A-conjugates of K in the same
component coincide. Those in distinct components commute and are independent:
an element in one component and in the product of the others is central in
that component. Thus the orbit of K is a finite direct power of K.

Its normality in ⟨K,A⟩ and a p-group assumption on A give a p-group quotient.
Every p-perfect subnormal subgroup of ⟨K,A⟩ therefore embeds subnormally into
the direct power, retaining the original domain group. A need not normalize L.

This is the component-orbit reduction for Aschbacher–Smith 2.3.9(7),
*The Classification of Quasithin Groups*, printed pp.525–526.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

private theorem center_eq_bot_of_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hX : center X = ⊥) : center Y = ⊥ := by
  apply eq_bot_iff.mpr
  intro y hy
  have hx : e.symm y ∈ center X := ((centerCongr e).symm ⟨y, hy⟩).property
  have hx1 : e.symm y = 1 := by simpa only [hX, mem_bot] using hx
  apply mem_bot.mpr
  apply e.symm.injective
  simpa using hx1

private theorem conjugate_conjugate (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem seed_conjugate_eq {L K A : Subgroup G}
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G)) (a b : A)
    (he : L.map (MulAut.conj (a : G)).toMonoidHom =
      L.map (MulAut.conj (b : G)).toMonoidHom) :
    K.map (MulAut.conj (a : G)).toMonoidHom =
      K.map (MulAut.conj (b : G)).toMonoidHom := by
  have hL : L.map (MulAut.conj ((b⁻¹ * a : A) : G)).toMonoidHom = L := by
    have hh := congrArg (Subgroup.map (MulAut.conj (b : G)⁻¹).toMonoidHom) he
    rw [conjugate_conjugate, conjugate_conjugate, inv_mul_cancel, map_one] at hh
    change L.map (MulAut.conj ((b : G)⁻¹ * a)).toMonoidHom = L.map (MonoidHom.id G) at hh
    rw [Subgroup.map_id] at hh
    exact hh
  have hK := mem_normalizer_iff_map_conj_eq.mp
    (hinv ⟨(b⁻¹ * a).property, mem_normalizer_iff_map_conj_eq.mpr hL⟩)
  change K.map (MulAut.conj ((b : G)⁻¹ * a)).toMonoidHom = K at hK
  have hh := congrArg (Subgroup.map (MulAut.conj (b : G)).toMonoidHom) hK
  simpa only [conjugate_conjugate, Subgroup.coe_mul, Subgroup.coe_inv,
    mul_inv_cancel_left] using hh

/-- The conjugate local subgroups in distinct centerless components form a direct power. -/
theorem IsComponent.local_orbit_equiv_power [Finite G] {L K A : Subgroup G}
    (hL : IsComponent G L) (hZ : center L = ⊥) (hK : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G)) :
    ∃ n : ℕ, Nonempty (componentOrbit K A ≃* (Fin n → K)) := by
  classical
  let I := Set.range (fun a : A => L.map (MulAut.conj (a : G)).toMonoidHom)
  let s : I → A := fun i => Classical.choose i.property
  have hs (i : I) : L.map (MulAut.conj (s i : G)).toMonoidHom = i.val :=
    Classical.choose_spec i.property
  let D : I → Subgroup G := fun i => K.map (MulAut.conj (s i : G)).toMonoidHom
  have hDL (i : I) : D i ≤ i.val := hs i ▸ map_mono hK
  have hLi (i : I) : IsComponent G i.val := hs i ▸ hL.map_conj (s i : G)
  have hZi (i : I) : center i.val = ⊥ := by
    rw [← hs i]
    exact center_eq_bot_of_equiv ((MulAut.conj (s i : G)).subgroupMap L) hZ
  have hcommL (i j : I) (hne : i ≠ j) :
      i.val ≤ centralizer (j.val : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    exact (hLi i).commutator_eq_bot_of_ne (hLi j) (fun hh => hne (Subtype.ext hh))
  have hcomm : Pairwise fun i j : I => ∀ x y : G, x ∈ D i → y ∈ D j → Commute x y := by
    intro i j hij x y hx hy
    exact (mem_centralizer_iff.mp (hcommL i j hij (hDL i hx)) y (hDL j hy)).symm
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
        seed_conjugate_eq hinv (s i) a (hs i)
      exact he ▸ le_iSup D i
  let : Fintype I := Fintype.ofFinite I
  let f := Subgroup.noncommPiCoprod hcomm
  have hf : Function.Injective f := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hr : f.range = componentOrbit K A := Subgroup.noncommPiCoprod_range.trans hsup
  let ep : (∀ i, D i) ≃* componentOrbit K A :=
    (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)
  let ei : (I → K) ≃* (∀ i, D i) :=
    MulEquiv.piCongrRight (fun i => (MulAut.conj (s i : G)).subgroupMap K)
  exact ⟨Fintype.card I, ⟨ep.symm.trans (ei.symm.trans
    (MulEquiv.arrowCongr (Fintype.equivFin I) (MulEquiv.refl K)))⟩⟩

/-- Adjoining a p-subgroup gives a normal direct-power layer with p-group quotient. -/
theorem IsComponent.local_adjoin_normal_power [Finite G] {p : ℕ} {L K A : Subgroup G}
    (hL : IsComponent G L) (hZ : center L = ⊥) (hK : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hA : IsPGroup p A) :
    ∃ (N : Subgroup (K ⊔ A : Subgroup G)) (hN : N.Normal),
      letI := hN
      IsPGroup p ((K ⊔ A : Subgroup G) ⧸ N) ∧
        ∃ n : ℕ, Nonempty (N ≃* (Fin n → K)) := by
  let P := K ⊔ A
  let N := (componentOrbit K A).subgroupOf P
  have hn : N.Normal := componentOrbit_normal_subgroupOf_sup K A
  let := hn
  refine ⟨N, hn, ?_, ?_⟩
  · apply isPGroup_quotient_of_sup_eq_top N (A.subgroupOf P) hA.comap_subtype
    change (componentOrbit K A).subgroupOf P ⊔ A.subgroupOf P = ⊤
    rw [← subgroupOf_sup (componentOrbit_le_sup K A) le_sup_right, componentOrbit_sup,
      subgroupOf_self]
  · obtain ⟨n, ⟨e⟩⟩ := hL.local_orbit_equiv_power hZ hK hinv
    exact ⟨n, ⟨(subgroupOfEquivOfLe (componentOrbit_le_sup K A)).trans e⟩⟩

/-- A p-perfect subnormal subgroup of the local overgroup embeds subnormally
in the direct power. The original domain group and its action are retained. -/
theorem IsComponent.local_adjoin_embedding [Finite G] {p : ℕ} [Fact p.Prime]
    {L K A : Subgroup G} (hL : IsComponent G L) (hZ : center L = ⊥) (hK : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hA : IsPGroup p A) {B : Type*} [Group B] (hB : IsPPerfect p B)
    (f : B →* (K ⊔ A : Subgroup G)) (hf : Function.Injective f)
    (hs : f.range.IsSubnormal) :
    ∃ (n : ℕ) (g : B →* (Fin n → K)), Function.Injective g ∧ g.range.IsSubnormal := by
  obtain ⟨N, hN, hq, n, ⟨e⟩⟩ := hL.local_adjoin_normal_power hZ hK hinv hA
  let := hN
  have he := hB.hom_eq_one_of_isPGroup hq ((QuotientGroup.mk' N).comp f)
  have hmem (b : B) : f b ∈ N :=
    (QuotientGroup.eq_one_iff (f b)).mp (DFunLike.congr_fun he b)
  let r : B →* N := f.codRestrict N hmem
  have hr : Function.Injective r := fun x y hxy => hf (congrArg Subtype.val hxy)
  have hrange : r.range = f.range.subgroupOf N := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, hb⟩
      exact ⟨b, Subtype.ext hb⟩
  refine ⟨n, e.toMonoidHom.comp r, e.injective.comp hr, ?_⟩
  rw [MonoidHom.range_comp, hrange]
  exact hs.subgroupOf.map e.surjective

end Theory.GroupTheory

end
