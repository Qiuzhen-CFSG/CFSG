module

public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Central quotients of component orbits

Index the conjugate local factors by the conjugate components containing them.
The stabilizer hypothesis identifies factors in the same component, while
factors in distinct components commute. A relation in their multiplication
map has every coordinate in the corresponding component center.

A surjection on the seed which kills that center and has central kernel
therefore descends to a surjection from the orbit to a finite direct power.
Its kernel is central. No component center or prime core is discarded beyond
the specified seed kernel, and the actor may permute components.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
E.6.7–8, printed pp.246–248. This module proves the general group calculation.
-/

public section

open Subgroup
namespace Theory.GroupTheory.ComponentLocalTwelveExclusion
variable {G K₀ I : Type*} [Group G] [Group K₀]

private theorem central_coordinate_of_relation [Fintype I]
    (C : I → Subgroup G) (u : I → K₀ →* G)
    (hu : ∀ i x, u i x ∈ C i)
    (hcross : ∀ i j, i ≠ j → C i ≤ centralizer (C j : Set G))
    (hcomm : Pairwise fun i j => ∀ x y, Commute (u i x) (u j y))
    (x : I → K₀) (hx : MonoidHom.noncommPiCoprod u hcomm x = 1) (i : I) :
    u i (x i) ∈ centralizer (C i : Set G) := by
  classical
  let p := MonoidHom.noncommPiCoprod u hcomm
  let r : I → K₀ := Function.update x i 1
  have hprod : Pi.mulSingle i (x i) * r = x := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [r]
    · simp [r, hji]
  have hr : p r ∈ centralizer (C i : Set G) := by
    change Finset.univ.noncommProd (fun j => u j (r j))
      (fun j _ k _ h => hcomm h (r j) (r k)) ∈ _
    apply Subgroup.noncommProd_mem
    intro j _
    by_cases hji : j = i
    · subst j
      simp [r]
    · exact hcross j i hji (hu j (r j))
  have he : u i (x i) * p r = 1 := by
    rw [← MonoidHom.noncommPiCoprod_mulSingle u i (x i), ← map_mul, hprod]
    exact hx
  rw [eq_inv_of_mul_eq_one_left he]
  exact (centralizer (C i : Set G)).inv_mem hr

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

/-- Killing the component centers in a commuting orbit produces a direct power;
the only kernel remaining in the orbit is central. -/
theorem central_power_of_component_orbit [Finite G]
    {L K A : Subgroup G} {B : Type*} [Group B]
    (hL : IsComponent G L) (hKL : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (f : K →* B) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center K)
    (hkill : ∀ k : K, inclusion hKL k ∈ center L → f k = 1) :
    ∃ n : ℕ, ∃ q : componentOrbit K A →* (Fin n → B),
      Function.Surjective q ∧ q.ker ≤ center (componentOrbit K A) := by
  classical
  let J := Set.range (fun a : A => L.map (MulAut.conj (a : G)).toMonoidHom)
  let a : J → A := fun i => Classical.choose i.property
  have ha (i : J) : L.map (MulAut.conj (a i : G)).toMonoidHom = i.val :=
    Classical.choose_spec i.property
  let u : J → K →* G := fun i => (MulAut.conj (a i : G)).toMonoidHom.comp K.subtype
  have hu (i : J) (k : K) : u i k ∈ i.val := by
    rw [← ha i]
    exact mem_map_of_mem _ (hKL k.property)
  have hLi (i : J) : IsComponent G i.val := ha i ▸ hL.map_conj (a i : G)
  have hcross (i j : J) (hne : i ≠ j) : i.val ≤ centralizer (j.val : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      ((hLi i).commutator_eq_bot_of_ne (hLi j) (fun h => hne (Subtype.ext h)))
  have hcomm : Pairwise fun i j : J => ∀ x y : K, Commute (u i x) (u j y) := by
    intro i j hij x y
    exact (mem_centralizer_iff.mp (hcross i j hij (hu i x)) _ (hu j y)).symm
  let : Fintype J := Fintype.ofFinite J
  let p₀ := MonoidHom.noncommPiCoprod u hcomm
  have hur (i : J) : (u i).range = K.map (MulAut.conj (a i : G)).toMonoidHom := by
    rw [MonoidHom.range_comp, K.range_subtype]
  have hr : p₀.range = componentOrbit K A := by
    rw [MonoidHom.noncommPiCoprod_range]
    apply le_antisymm
    · exact iSup_le fun i => (hur i).symm ▸
        le_iSup (fun b : A => K.map (MulAut.conj (b : G)).toMonoidHom) (a i)
    · apply iSup_le
      intro b
      let i : J := ⟨L.map (MulAut.conj (b : G)).toMonoidHom, b, rfl⟩
      have he := seed_conjugate_eq hinv (a i) b (ha i)
      rw [← he, ← hur i]
      exact le_iSup (fun i => (u i).range) i
  let p : (J → K) →* componentOrbit K A :=
    (MulEquiv.subgroupCongr hr).toMonoidHom.comp p₀.rangeRestrict
  have hp : Function.Surjective p :=
    (MulEquiv.subgroupCongr hr).surjective.comp p₀.rangeRestrict_surjective
  let v : (J → K) →* (J → B) := MonoidHom.piMap (fun _ => f)
  have hv : Function.Surjective v := by
    intro b
    choose k hk using fun i => hf (b i)
    exact ⟨k, funext hk⟩
  have hker : p.ker ≤ v.ker := by
    intro x hx
    have hx₀ : p₀ x = 1 := congrArg Subtype.val hx
    apply funext
    intro i
    apply hkill
    have hci := central_coordinate_of_relation (fun i : J => i.val) u hu hcross hcomm x hx₀ i
    apply mem_center_iff.mpr
    intro l
    apply Subtype.ext
    change (l : G) * (x i : G) = (x i : G) * (l : G)
    apply (MulAut.conj (a i : G)).injective
    simpa only [u, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_subtype, map_mul] using
      mem_centralizer_iff.mp hci
      ((MulAut.conj (a i : G)) (l : G)) (by
        rw [← ha i]
        exact mem_map_of_mem _ l.property)
  have hvcentral : v.ker ≤ center (J → K) := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    funext i
    exact mem_center_iff.mp (hcentral (congrFun hx i)) (y i)
  let q := p.liftOfSurjective hp ⟨v, hker⟩
  have hq (x) : q (p x) = v x := p.liftOfRightInverse_comp_apply _ _ _ x
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := hv y
    exact ⟨p x, hq x⟩
  have hqc : q.ker ≤ center (componentOrbit K A) := by
    intro z hz
    obtain ⟨x, rfl⟩ := hp z
    have hx : x ∈ v.ker := by
      change v x = 1
      rw [← hq]
      exact hz
    apply mem_center_iff.mpr
    intro w
    obtain ⟨y, rfl⟩ := hp w
    simpa only [map_mul] using congrArg p (mem_center_iff.mp (hvcentral hx) y)
  let e : (J → B) ≃* (Fin (Fintype.card J) → B) :=
    MulEquiv.arrowCongr (Fintype.equivFin J) (MulEquiv.refl B)
  refine ⟨Fintype.card J, e.toMonoidHom.comp q, e.surjective.comp hqs, ?_⟩
  intro x hx
  apply hqc
  apply e.injective
  exact hx.trans (map_one e).symm
end Theory.GroupTheory.ComponentLocalTwelveExclusion
