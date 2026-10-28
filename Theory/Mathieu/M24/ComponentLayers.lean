module

public import Theory.Mathieu.M24.TwoLocalExtensions
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Mathieu layers in component orbits

Let B lie in a component L of a finite group H. Suppose a two-subgroup A of H
has its stabilizer of L normalizing B, and B maps onto the concrete M24 with
two-group kernel. Then B ∨ A has a normal series consisting of a two-group,
an actual finite direct power of M24, and a two-group.

The kernel is the orbit of O₂(B). Distinct conjugates of B commute, and the
orbit of their two-cores is a normal two-subgroup N. Its intersection with
each factor is exactly that factor's two-core: it contains the core and is
itself a normal two-subgroup of the factor. The factor images modulo N are
therefore actual copies of M24. Their trivial centers make the commuting
images independent, so the multiplication homomorphism identifies their join
with a direct power. The quotient above this join is the known two-group
quotient by the full local orbit.

The relative theorem applies this argument inside H and transports the normal
series to the ambient group. Neither splitting nor trivial centers of the
original components are assumed. The explicit seed surjection is retained as
an input; construction of that seed belongs to the local geometry argument.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
2.3.9(7), printed p.526; GLS3, Table 5.3i, the subgroup E2048.M24 of J4.
-/

public section

open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu

/-- The normal series and its actual Mathieu factors transport through an isomorphism. -/
theorem HasMathieuTwoLayer.of_equiv {G H : Type*} [Group G] [Group H]
    (h : HasMathieuTwoLayer G) (e : G ≃* H) : HasMathieuTwoLayer H := by
  obtain ⟨N, hN, hp, D, hD, n, ⟨d⟩, hq⟩ := h
  let := hN
  let := hD
  let N' := N.map e.toMonoidHom
  let : N'.Normal := hN.map _ e.surjective
  let q := QuotientGroup.congr N N' e rfl
  let D' := D.map q.toMonoidHom
  let : D'.Normal := hD.map _ q.surjective
  refine ⟨N', inferInstance, hp.map _, D', inferInstance, n,
    ⟨(q.subgroupMap D).symm.trans d⟩, ?_⟩
  exact hq.of_equiv (QuotientGroup.congr D D' q rfl)

private theorem mathieu_center : center M24 = ⊥ := by
  let := m24_isSimpleGroup
  rcases (inferInstance : (center M24).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · let a : M24 := ⟨m24GeneratorA, m24GeneratorA_mem⟩
    let b : M24 := ⟨m24GeneratorB, m24GeneratorB_mem⟩
    have ha : a ∈ center M24 := h ▸ mem_top a
    have hab := mem_center_iff.mp ha b
    have hp := congrArg (fun g : M24 => g.val 1) hab
    have hn : (m24GeneratorB * m24GeneratorA) (1 : Fin 24) ≠
        (m24GeneratorA * m24GeneratorB) (1 : Fin 24) := by decide +kernel
    exact (hn hp).elim

private theorem center_trivial_of_equiv {Y : Type*} [Group Y] (e : Y ≃* M24) :
    center Y = ⊥ := by
  apply eq_bot_iff.mpr
  intro y hy
  have he : e y ∈ center M24 := (centerCongr e ⟨y, hy⟩).property
  rw [mathieu_center, mem_bot] at he
  exact (map_eq_one_iff _ e.injective).mp he

/-- Quotienting by a normal two-subgroup which contains the seed core leaves
exactly its Mathieu quotient, including for nonsplit seed extensions. -/
theorem mathieu_image_equiv {G : Type*} [Group G] [Finite G]
    (K N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hcore : K.pCoreIn 2 ≤ N) (e : K ⧸ pCore 2 K ≃* M24) :
    Nonempty (K.map (QuotientGroup.mk' N) ≃* M24) := by
  let q := QuotientGroup.mk' N
  let r := q.subgroupMap K
  have hk : r.ker = N.comap K.subtype := by
    ext x
    change (⟨q x, _⟩ : K.map q) = 1 ↔ (x : G) ∈ N
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  have hc : r.ker = pCore 2 K := by
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, hk ▸ hN.comap_subtype⟩
    · rw [hk]
      exact map_le_iff_le_comap.mp hcore
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective r (q.subgroupMap_surjective K)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hc).trans e)⟩

/-- A finite commuting family of copies of M24 has independent factors. -/
theorem commuting_mathieu_power {G : Type*} [Group G] {ι : Type*} [Finite ι]
    (K : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → K i ≤ centralizer (K j : Set G))
    (he : ∀ i, Nonempty (K i ≃* M24)) :
    ∃ n : ℕ, Nonempty ((⨆ i, K i : Subgroup G) ≃* (Fin n → M24)) := by
  classical
  let e : ∀ i, K i ≃* M24 := fun i => (he i).some
  have hz (i : ι) : center (K i) = ⊥ := center_trivial_of_equiv (e i)
  have hind : iSupIndep K := by
    rw [iSupIndep_def]
    intro i
    apply Subgroup.disjoint_def.mpr
    intro x hx hi
    have hothers : (⨆ j, ⨆ (_ : j ≠ i), K j) ≤ centralizer (K i : Set G) :=
      iSup_le fun j => iSup_le fun hji => hc j i hji
    have hxZ : (⟨x, hx⟩ : K i) ∈ center (K i) := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      exact mem_centralizer_iff.mp (hothers hi) y y.property
    have hx1 : (⟨x, hx⟩ : K i) = 1 := by simpa only [hz i, mem_bot] using hxZ
    exact congrArg Subtype.val hx1
  have hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ K i → y ∈ K j → Commute x y := by
    intro i j hij x y hx hy
    exact (mem_centralizer_iff.mp (hc i j hij hx) y hy).symm
  let := Fintype.ofFinite ι
  let f := Subgroup.noncommPiCoprod hcomm
  have hf : Function.Injective f := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  let ep : (∀ i, K i) ≃* (⨆ i, K i : Subgroup G) :=
    (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr Subgroup.noncommPiCoprod_range)
  exact ⟨Fintype.card ι, ⟨ep.symm.trans ((MulEquiv.piCongrRight e).trans
    (MulEquiv.arrowCongr (Fintype.equivFin ι) (MulEquiv.refl M24)))⟩⟩

/-- The normal orbit of commuting Mathieu extensions gives an actual Mathieu
layer after killing its normal two-subgroup. -/
theorem commuting_mathieu_layer {G : Type*} [Group G] [Finite G]
    {ι : Type*} [Finite ι] (K : ι → Subgroup G)
    [(⨆ i, K i : Subgroup G).Normal]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hND : N ≤ ⨆ i, K i)
    (hcore : ∀ i, (K i).pCoreIn 2 ≤ N)
    (hc : ∀ i j, i ≠ j → K i ≤ centralizer (K j : Set G))
    (he : ∀ i, Nonempty (K i ⧸ pCore 2 (K i) ≃* M24))
    (htop : IsPGroup 2 (G ⧸ (⨆ i, K i : Subgroup G))) : HasMathieuTwoLayer G := by
  let q := QuotientGroup.mk' N
  have hcq : ∀ i j, i ≠ j → (K i).map q ≤ centralizer ((K j).map q : Set (G ⧸ N)) := by
    intro i j hij x hx y hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    simpa only [map_mul] using congrArg q (hc i j hij hx y hy)
  have heq (i : ι) : Nonempty ((K i).map q ≃* M24) :=
    mathieu_image_equiv (K i) N hN (hcore i) (he i).some
  obtain ⟨n, ⟨e⟩⟩ := commuting_mathieu_power (fun i => (K i).map q) hcq heq
  let D := (⨆ i, K i : Subgroup G).map q
  have hD : D = ⨆ i, (K i).map q := Subgroup.map_iSup _ _
  refine ⟨N, inferInstance, hN, D, inferInstance, n,
    ⟨(MulEquiv.subgroupCongr hD).trans e⟩, ?_⟩
  exact htop.of_equiv (QuotientGroup.quotientQuotientEquivQuotient N (⨆ i, K i) hND).symm

end Sporadic.Mathieu

namespace Theory.GroupTheory
open Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G]

/-- A two-group adjoining a Mathieu seed in a component yields a Mathieu
layer, with no assumption on the center of the component. -/
theorem IsComponent.local_adjoin_hasMathieuTwoLayer {L B A : Subgroup G}
    (hL : IsComponent G L) (hBL : B ≤ L) (hA : IsPGroup 2 A)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (B : Set G))
    (f : B →* M24) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    HasMathieuTwoLayer (B ⊔ A : Subgroup G) := by
  classical
  let X := B ⊔ A
  let Q := componentOrbit (B.pCoreIn 2) A
  let D := componentOrbit B A
  obtain ⟨hQp, hQD, hXQ⟩ := hL.local_core_orbit (p := 2) hBL hinv
  have hDX : D ≤ X := componentOrbit_le_sup B A
  have hQX : Q ≤ X := hQD.trans hDX
  let N := Q.subgroupOf X
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hQX).mpr hXQ
  let D' := D.subgroupOf X
  let : D'.Normal := componentOrbit_normal_subgroupOf_sup B A
  let F := fun a : A => B.map (MulAut.conj (a : G)).toMonoidHom
  let I := {T : Subgroup G // T ∈ Set.range F}
  let T : I → Subgroup G := fun i => i.val
  have hTX (i : I) : T i ≤ X := by
    obtain ⟨a, ha⟩ := i.property
    change i.val ≤ X
    rw [← ha]
    exact (le_iSup F a).trans hDX
  let K : I → Subgroup X := fun i => (T i).subgroupOf X
  have hmap (i : I) : (K i).map X.subtype = T i := map_subgroupOf_eq_of_le (hTX i)
  have hsupT : (⨆ i, T i) = D := by
    apply le_antisymm
    · apply iSup_le
      rintro ⟨T, a, rfl⟩
      exact le_iSup F a
    · exact iSup_le fun a => le_iSup T ⟨F a, a, rfl⟩
  have hsupK : (⨆ i, K i) = D' := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_iSup, map_subgroupOf_eq_of_le hDX]
    simpa only [hmap] using hsupT
  let : (⨆ i, K i : Subgroup X).Normal := hsupK ▸ inferInstance
  have hcoreT (i : I) : (T i).pCoreIn 2 ≤ Q := by
    obtain ⟨a, ha⟩ := i.property
    change (i.val).pCoreIn 2 ≤ Q
    rw [← ha]
    change (B.map (MulAut.conj (a : G)).toMonoidHom).pCoreIn 2 ≤ Q
    rw [← map_pCoreIn_of_injective 2 B _ (MulAut.conj (a : G)).injective]
    exact le_iSup (fun b : A => (B.pCoreIn 2).map (MulAut.conj (b : G)).toMonoidHom) a
  have hcoreK (i : I) : (K i).pCoreIn 2 ≤ N := by
    intro x hx
    apply hcoreT i
    have hm : ((K i).pCoreIn 2).map X.subtype = (T i).pCoreIn 2 := by
      rw [map_pCoreIn_of_injective 2 _ _ X.subtype_injective, hmap]
    rw [← hm]
    exact mem_map_of_mem X.subtype hx
  have hcT (i j : I) (hne : i ≠ j) : T i ≤ centralizer (T j : Set G) := by
    obtain ⟨a, ha⟩ := i.property
    obtain ⟨b, hb⟩ := j.property
    rcases hL.local_conjugates_eq_or_commute hBL hinv b a with he | hc
    · exact (hne (Subtype.ext (ha.symm.trans (he.trans hb)))).elim
    · apply commutator_eq_bot_iff_le_centralizer.mp
      change ⁅i.val, j.val⁆ = ⊥
      rw [← ha, ← hb]
      exact hc
  have hcK (i j : I) (hne : i ≠ j) : K i ≤ centralizer (K j : Set X) := by
    intro x hx y hy
    apply Subtype.ext
    exact hcT i j hne hx y hy
  have eB : Nonempty (B ⧸ pCore 2 B ≃* M24) := by
    have hk := ker_eq_twoCore_of_surjective_m24 f hf hker
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩
  have heK (i : I) : Nonempty (K i ⧸ pCore 2 (K i) ≃* M24) := by
    obtain ⟨a, ha⟩ := i.property
    let ei : T i ≃* B := (MulEquiv.subgroupCongr ha.symm).trans
      ((MulAut.conj (a : G)).subgroupMap B).symm
    let e : K i ≃* B := (subgroupOfEquivOfLe (hTX i)).trans ei
    exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans eB.some⟩
  apply commuting_mathieu_layer K N hQp.comap_subtype
  · rw [hsupK]
    exact subgroupOf_mono X hQD
  · exact hcoreK
  · exact hcK
  · exact heK
  · exact (local_orbit_quotient_isPGroup B A hA).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hsupK.symm)

/-- Apply the orbit construction inside H, where the component is subnormal,
and faithfully transport the resulting normal series into the ambient G. -/
theorem IsComponent.relative_local_adjoin_hasMathieuTwoLayer
    {H L B A : Subgroup G} (hL : IsComponent H (L.subgroupOf H))
    (hLH : L ≤ H) (hBL : B ≤ L) (hAH : A ≤ H) (hA : IsPGroup 2 A)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (B : Set G))
    (f : B →* M24) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    HasMathieuTwoLayer (B ⊔ A : Subgroup G) := by
  let F := B.subgroupOf H
  let C := A.subgroupOf H
  have hBH : B ≤ H := hBL.trans hLH
  have hFL : F ≤ L.subgroupOf H := subgroupOf_mono H hBL
  have hmF : F.map H.subtype = B := map_subgroupOf_eq_of_le hBH
  have hmC : C.map H.subtype = A := map_subgroupOf_eq_of_le hAH
  have hinvH : C ⊓ normalizer (L.subgroupOf H : Set H) ≤ normalizer (F : Set H) := by
    rw [← subgroupOf_normalizer_eq hLH, ← subgroupOf_normalizer_eq hBH]
    intro x hx
    exact hinv hx
  let e : F ≃* B := subgroupOfEquivOfLe hBH
  let g := f.comp e.toMonoidHom
  have hg : Function.Surjective g := hf.comp e.surjective
  have hkg : IsPGroup 2 g.ker := by
    change IsPGroup 2 (f.ker.comap e.toMonoidHom)
    exact hker.comap_of_injective _ e.injective
  have h := hL.local_adjoin_hasMathieuTwoLayer hFL hA.comap_subtype hinvH g hg hkg
  have hmX : (F ⊔ C).map H.subtype = B ⊔ A := by rw [Subgroup.map_sup, hmF, hmC]
  exact h.of_equiv ((equivMapOfInjective (F ⊔ C) H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hmX))

end Theory.GroupTheory

end
