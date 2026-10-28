module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Component
public import CFSG.Quasithin.Chapter16.Section01To02.Local
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.SuzukiSimple.Model

/-!
# The center-free Suzuki component torus

A genuine equivalence from L/Z(L) to the Suzuki matrix group, together with
Z(L) = 1, identifies L with that model. Subnormal Sylow intersection and
Sylow conjugacy align the standard root group with the prescribed T ∩ L.
The standard split torus is then embedded in L and hence in the ambient group.

The model calculation supplies the cyclic actor of order 2^(2m+1) − 1,
elementary component omega, trivial fixed subgroup, displacement of order
2^(2m+1), regular literal conjugation, and pointwise coverage of the component
omega normalizer. The center-free condition is the explicit hypothesis of
this branch; the ambient treatment of central covers belongs to its parent.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
16.5.1, printed p.1194, first and third paragraphs.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction
namespace SuzukiSimple

private theorem regular_map {H K : Type*} [Group H] [Group K]
    (U X : Subgroup H) (f : H →* K) (hf : Function.Injective f)
    (hreg : ∀ v ∈ U, v ≠ 1 → ∀ w ∈ U, w ≠ 1 →
      ∃! x : X, MulAut.conj (x : H) v = w) :
    ∀ v ∈ U.map f, v ≠ 1 → ∀ w ∈ U.map f, w ≠ 1 →
      ∃! x : X.map f, MulAut.conj (x : K) v = w := by
  rintro _ ⟨v, hv, rfl⟩ hv1 _ ⟨w, hw, rfl⟩ hw1
  obtain ⟨x, hx, huniq⟩ := hreg v hv (fun h => hv1 (h ▸ f.map_one))
    w hw (fun h => hw1 (h ▸ f.map_one))
  refine ⟨⟨f x, ⟨x, x.property, rfl⟩⟩, ?_, ?_⟩
  · simpa only [MulAut.conj_apply, map_mul, map_inv] using congrArg f hx
  · rintro ⟨_, y, hy, rfl⟩ he
    apply Subtype.ext
    have hyx : (⟨y, hy⟩ : X) = x := huniq _ (hf (by
      simpa only [MulAut.conj_apply, map_mul, map_inv] using he))
    exact congrArg (fun z : X => f z) hyx

private theorem fixed_map {H K : Type*} [Group H] [Group K]
    (U X : Subgroup H) (f : H →* K) (hf : Function.Injective f)
    (hfix : U ⊓ centralizer (X : Set H) = ⊥) :
    U.map f ⊓ centralizer (X.map f : Set K) = ⊥ := by
  apply eq_bot_iff.mpr
  rintro _ ⟨⟨u, hu, rfl⟩, hc⟩
  have hu1 : u = 1 := by
    apply mem_bot.mp
    rw [← hfix]
    refine ⟨hu, mem_centralizer_iff.mpr fun x hx => ?_⟩
    apply hf
    simpa only [map_mul] using mem_centralizer_iff.mp hc (f x) ⟨x, hx, rfl⟩
  simp only [hu1, map_one, one_mem]


private theorem omega_map_injective {H K : Type*} [Group H] [Group K]
    (U : Subgroup H) (f : H →* K) (hf : Function.Injective f) :
    omegaOneAmbient (U.map f) = (omegaOneAmbient U).map f := by
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    rintro _ ⟨u, hu, rfl⟩ hp
    have hu2 : u ^ 2 = 1 := hf (by simpa only [map_pow, map_one] using hp)
    exact mem_map_of_mem f ((omegaOneAmbient_le_iff _ _).mp le_rfl u hu hu2)
  · rw [map_le_iff_le_comap]
    apply (omegaOneAmbient_le_iff _ _).mpr
    intro u hu hp
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl (f u) (mem_map_of_mem _ hu)
      (by simpa only [map_pow, map_one] using congrArg f hp)

private theorem aligned_equiv {H : Type*} [Group H] [Finite H] {m : ℕ}
    (hm : 0 < m) (e : H ≃* SuzukiMatrixGroup m) (S : Sylow 2 H) :
    ∃ f : SuzukiMatrixGroup m ≃* H,
      (SuzukiRootSubgroup m).map f.toMonoidHom = (S : Subgroup H) := by
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  let P' : Sylow 2 H := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P' S
  refine ⟨e.symm.trans (MulAut.conj g), ?_⟩
  have hh := congrArg Sylow.toSubgroup hg
  change ((P : Subgroup (SuzukiMatrixGroup m)).map e.symm.toMonoidHom).map
    (MulAut.conj g).toMonoidHom = (S : Subgroup H) at hh
  change (SuzukiRootSubgroup m).map
    ((MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom) = _
  simpa only [hP, map_map] using hh

end SuzukiSimple

/-- The center-free Suzuki branch of the intrinsic torus calculation in 16.5.1.
The split torus is aligned with the actual component Sylow subgroup before
being embedded in G; its literal conjugation covers the omega normalizer. -/
theorem exists_componentTorus_suzuki {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {z : G} {L : Subgroup G} {m : ℕ}
    (hlocal : CentralComponentSetup T z L) (hZ : center L = ⊥)
    (hm : 1 ≤ m) (e₀ : (L ⧸ center L) ≃* SuzukiMatrixGroup m) :
    ∃ d : ComponentTorus T L (2*m+1), OmegaNormalizerAction T L d.actor := by
  classical
  have hm0 : 0 < m := hm
  let eL : L ≃* SuzukiMatrixGroup m :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e₀
  obtain ⟨S, hS⟩ := hlocal.exists_component_sylow
  obtain ⟨e, he⟩ := SuzukiSimple.aligned_equiv hm0 eL S
  let f : SuzukiMatrixGroup m →* G := L.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.injective
  have hroot : (SuzukiRootSubgroup m).map f = componentSylow T L := by
    rw [show f = L.subtype.comp e.toMonoidHom from rfl, ← map_map, he, hS]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.property⟩
    · intro hx
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  let U := omegaOneAmbient (SuzukiRootSubgroup m)
  let X := SuzukiSplitTorus m
  have homega : omegaOneAmbient (componentSylow T L) = U.map f := by
    rw [← hroot, SuzukiSimple.omega_map_injective _ f hf]
  have hnorm : X.map f ≤ normalizer (componentSylow T L : Set G) := by
    rw [← hroot]
    exact (map_mono (suzukiSplitTorus_le_normalizer_root m)).trans (le_normalizer_map f)
  have hcomm : ⁅omegaOneAmbient (componentSylow T L), X.map f⁆ = U.map f := by
    rw [homega, ← map_commutator, SuzukiSimpleModel.omega_commutator m hm0]
  let d : ComponentTorus T L (2*m+1) := {
    actor := X.map f
    actor_le := le_inf (by
      rintro _ ⟨a, _, rfl⟩
      exact (e a).property) hnorm
    actor_cyclic := by
      let := suzukiSplitTorus_isCyclic m hm0
      exact isCyclic_of_surjective (f.subgroupMap X) (f.subgroupMap_surjective X)
    actor_card := by
      rw [card_map_of_injective hf, suzukiSplitTorus_card m hm0]
    elementary := by
      rw [homega]
      let := SuzukiSimpleModel.omega_elementary m hm0
      exact IsElementaryAbelian.map f
    fixed_le := by
      rw [homega, SuzukiSimple.fixed_map U X f hf (SuzukiSimpleModel.omega_fixed_eq_bot m hm0)]
      exact bot_le
    moved_card := by
      rw [hcomm, card_map_of_injective hf, SuzukiSimpleModel.omega_card m hm0]
    regular := by
      rw [hcomm]
      exact SuzukiSimple.regular_map U X f hf (fun _ hv hv1 _ hw hw1 =>
        SuzukiSimpleModel.torus_regular m hm0 hv hv1 hw hw1)
  }
  refine ⟨d, ?_⟩
  intro l hl hln
  let a : SuzukiMatrixGroup m := e.symm ⟨l, hl⟩
  have hal : f a = l := congrArg Subtype.val (e.apply_symm_apply ⟨l, hl⟩)
  have ha : a ∈ normalizer (U : Set (SuzukiMatrixGroup m)) := by
    apply mem_normalizer_iff.mpr
    intro u
    have hh := mem_normalizer_iff.mp hln (f u)
    rw [homega, ← hal, ← map_inv, ← map_mul, ← map_mul] at hh
    simpa only [mem_map_iff_mem hf] using hh
  obtain ⟨x, hx⟩ := SuzukiSimpleModel.normalizer_coverage m hm0 ha
  refine ⟨⟨f x, ⟨x, x.property, rfl⟩⟩, ?_⟩
  rw [homega]
  rintro _ ⟨u, hu, rfl⟩
  have hh := congrArg f (hx u hu)
  simpa only [MulAut.conj_apply, map_mul, map_inv, hal] using hh

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction
