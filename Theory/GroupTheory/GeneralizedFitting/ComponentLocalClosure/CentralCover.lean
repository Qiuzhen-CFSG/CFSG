module

public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Orbit
public import Theory.GroupTheory.ComponentLocalOrbitCore

/-!
# Local component orbits with central covers

Let K lie in a component L, with A ∩ N(L) normalizing K. A surjection
from K to P whose kernel is a p-group extends to a surjection from the
actual A-orbit join of K onto a finite direct power of P, provided it
kills K ∩ Z(L). This permits arbitrary central p-covers of the components.

Index by the distinct conjugates of L. Their pairwise commutation gives
a product map onto the orbit join. The kernel of this product map has
each coordinate in Z(L): commute a kernel element with an element supported
at that coordinate and use injectivity of the component embedding.
Consequently the factor maps descend. The descended kernel is an image
of the product of the factor kernels, hence a p-group.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript of 1 March 2004, 2.3.9(7), printed p.526.
-/

public section

open Subgroup
open scoped commutatorElement

private theorem central_kernel {G D I : Type*} [Group G] [Group D] [Fintype I]
    (f : I → D →* G)
    (hc : Pairwise fun i j => ∀ x y, Commute (f i x) (f j y))
    (hf : ∀ i, Function.Injective (f i)) (x : I → D)
    (hx : MonoidHom.noncommPiCoprod f hc x = 1) (i : I) :
    x i ∈ center D := by
  classical
  apply mem_center_iff.mpr
  intro y
  have he : ⁅x, Pi.mulSingle i y⁆ = (Pi.mulSingle i ⁅x i, y⁆ : I → D) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [commutatorElement_def]
    · simp [commutatorElement_def, Pi.mulSingle_eq_of_ne hj]
  have hm := congrArg (MonoidHom.noncommPiCoprod f hc) he
  rw [map_commutatorElement, hx, commutatorElement_one_left,
    MonoidHom.noncommPiCoprod_mulSingle] at hm
  have he1 : ⁅x i, y⁆ = 1 := hf i (hm.symm.trans (map_one (f i)).symm)
  exact (commutatorElement_eq_one_iff_mul_comm.mp he1).symm


namespace Theory.GroupTheory

variable {G P : Type*} [Group G] [Group P] [Finite G]

/-- The actual orbit of a local subgroup maps onto a finite power of its
central quotient, with a p-group common kernel. Components may be permuted
and may have nontrivial centers. -/
theorem IsComponent.local_orbit_surjection_power {p : ℕ} {L K A : Subgroup G}
    (hL : IsComponent G L) (hKL : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (f : K →* P) (hf : Function.Surjective f) (hk : IsPGroup p f.ker)
    (hz : ∀ x : K, (⟨x.val, hKL x.property⟩ : L) ∈ center L → f x = 1) :
    ∃ (n : ℕ) (F : componentOrbit K A →* (Fin n → P)),
      Function.Surjective F ∧ IsPGroup p F.ker := by
  classical
  let I := Set.range (fun a : A => L.map (MulAut.conj (a : G)).toMonoidHom)
  let s : I → A := fun i => Classical.choose i.property
  have hs (i : I) : L.map (MulAut.conj (s i : G)).toMonoidHom = i.val :=
    Classical.choose_spec i.property
  let φ : I → L →* G := fun i => (MulAut.conj (s i : G)).toMonoidHom.comp L.subtype
  have hφ (i : I) (x : L) : φ i x ∈ i.val := by
    rw [← hs i]
    exact mem_map_of_mem _ x.property
  have hcomm : Pairwise fun i j => ∀ x y, Commute (φ i x) (φ j y) := by
    intro i j hij x y
    have hc := (hL.map_conj (s i : G)).commutator_eq_bot_of_ne
      (hL.map_conj (s j : G)) (by rw [hs, hs]; exact fun h => hij (Subtype.ext h))
    have hc' : i.val ≤ centralizer (j.val : Set G) := by
      rw [← hs i, ← hs j]
      exact commutator_eq_bot_iff_le_centralizer.mp hc
    exact (mem_centralizer_iff.mp (hc' (hφ i x)) _ (hφ j y)).symm
  let inc : K →* L := inclusion hKL
  let ψ : I → K →* G := fun i => (φ i).comp inc
  have hcommK : Pairwise fun i j => ∀ x y, Commute (ψ i x) (ψ j y) :=
    fun i j hij x y => hcomm hij (inc x) (inc y)
  let : Fintype I := Fintype.ofFinite I
  let r₀ : (I → K) →* G := MonoidHom.noncommPiCoprod ψ hcommK
  have hrange : r₀.range = componentOrbit K A := by
    rw [MonoidHom.noncommPiCoprod_range]
    have hr (i : I) : (ψ i).range = K.map (MulAut.conj (s i : G)).toMonoidHom := by
      change ((MulAut.conj (s i : G)).toMonoidHom.comp K.subtype).range = _
      rw [MonoidHom.range_comp, range_subtype]
    simp_rw [hr]
    apply le_antisymm
    · exact iSup_le fun i => le_iSup (fun a : A => K.map (MulAut.conj (a : G)).toMonoidHom) (s i)
    · apply iSup_le
      intro a
      let i : I := ⟨L.map (MulAut.conj (a : G)).toMonoidHom, ⟨a, rfl⟩⟩
      have he := localFactor_conjugate_eq_of_component_conjugate_eq hinv (s i) a (hs i)
      rw [← he]
      exact le_iSup (fun j : I => K.map (MulAut.conj (s j : G)).toMonoidHom) i
  let r : (I → K) →* componentOrbit K A :=
    (MulEquiv.subgroupCongr hrange).toMonoidHom.comp r₀.rangeRestrict
  have hr : Function.Surjective r :=
    (MulEquiv.subgroupCongr hrange).surjective.comp r₀.rangeRestrict_surjective
  let g : (I → K) →* (I → P) := MonoidHom.piMap (fun _ => f)
  have hg : Function.Surjective g := by
    intro y
    choose x hx using fun i => hf (y i)
    exact ⟨x, funext hx⟩
  have hkg : IsPGroup p g.ker := by
    obtain ⟨m, hm⟩ := hk.exists_card_dvd_pow
    intro x
    refine ⟨m, Subtype.ext (funext fun i => ?_)⟩
    let y : f.ker := ⟨x.val i, congrFun x.property i⟩
    exact congrArg Subtype.val
      (orderOf_dvd_iff_pow_eq_one.mp ((_root_.orderOf_dvd_natCard y).trans hm))
  have hkr : r.ker ≤ g.ker := by
    intro x hx
    apply funext
    intro i
    apply hz
    apply central_kernel φ hcomm (fun i => (MulAut.conj (s i : G)).injective.comp L.subtype_injective)
      (fun j => inc (x j))
    exact congrArg (fun y : componentOrbit K A => (y : G)) hx
  let F : componentOrbit K A →* (I → P) := r.liftOfSurjective hr ⟨g, hkr⟩
  have hFr (x : I → K) : F (r x) = g x :=
    r.liftOfRightInverse_comp_apply _ _ ⟨g, hkr⟩ x
  have hF : Function.Surjective F := by
    intro y
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨r x, hFr x⟩
  have hker : F.ker = g.ker.map r := by
    ext y
    obtain ⟨x, rfl⟩ := hr y
    constructor
    · intro hx
      exact ⟨x, (hFr x).symm.trans hx, rfl⟩
    · rintro ⟨z, hz, he⟩
      rw [← he]
      exact (hFr z).trans hz
  let e := MulEquiv.arrowCongr (Fintype.equivFin I) (MulEquiv.refl P)
  refine ⟨Fintype.card I, e.toMonoidHom.comp F, e.surjective.comp hF, ?_⟩
  have heker : (e.toMonoidHom.comp F).ker = F.ker := by
    ext x
    change e (F x) = 1 ↔ F x = 1
    exact e.injective.eq_iff' (map_one e)
  rw [heker, hker]
  exact hkg.map r

/-- The orbit construction for a component subnormal inside H. The orbit
and every map retain their original ambient embedding. -/
theorem IsComponent.local_orbit_surjection_power_in
    {G P : Type*} [Group G] [Group P] [Finite G]
    {p : ℕ} {H L K A : Subgroup G}
    (hLH : L ≤ H) (hAH : A ≤ H)
    (hL : IsComponent H (L.subgroupOf H)) (hKL : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (f : K →* P) (hf : Function.Surjective f) (hk : IsPGroup p f.ker)
    (hz : ∀ x : K, (⟨x.val, hKL x.property⟩ : L) ∈ center L → f x = 1) :
    ∃ (n : ℕ) (F : componentOrbit K A →* (Fin n → P)),
      Function.Surjective F ∧ IsPGroup p F.ker := by
  have hKH := hKL.trans hLH
  let eK : K.subgroupOf H ≃* K := subgroupOfEquivOfLe hKH
  let eL : L.subgroupOf H ≃* L := subgroupOfEquivOfLe hLH
  have hn : A.subgroupOf H ⊓ normalizer (L.subgroupOf H : Set H) ≤
      normalizer (K.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hLH, ← subgroupOf_normalizer_eq hKH]
    intro x hx
    exact hinv hx
  have hfk : IsPGroup p (f.comp eK.toMonoidHom).ker := by
    rw [← MonoidHom.comap_ker]
    exact hk.comap_of_injective _ eK.injective
  have hfz (x : K.subgroupOf H)
      (hx : (⟨x.val, subgroupOf_mono H hKL x.property⟩ : L.subgroupOf H) ∈ center _) :
      (f.comp eK.toMonoidHom) x = 1 := by
    exact hz (eK x) (centerCongr eL ⟨_, hx⟩).property
  obtain ⟨n, F, hF, hkF⟩ := hL.local_orbit_surjection_power
    (subgroupOf_mono H hKL) hn (f.comp eK.toMonoidHom) (hf.comp eK.surjective) hfk hfz
  have he : (componentOrbit (K.subgroupOf H) (A.subgroupOf H)).map H.subtype =
      componentOrbit K A := by
    rw [map_componentOrbit, map_subgroupOf_eq_of_le hKH, map_subgroupOf_eq_of_le hAH]
  let e : componentOrbit (K.subgroupOf H) (A.subgroupOf H) ≃* componentOrbit K A :=
    ((componentOrbit (K.subgroupOf H) (A.subgroupOf H)).equivMapOfInjective H.subtype
      H.subtype_injective).trans (MulEquiv.subgroupCongr he)
  refine ⟨n, F.comp e.symm.toMonoidHom, hF.comp e.symm.surjective, ?_⟩
  rw [← MonoidHom.comap_ker]
  exact hkF.comap_of_injective _ e.symm.injective


end Theory.GroupTheory

end
