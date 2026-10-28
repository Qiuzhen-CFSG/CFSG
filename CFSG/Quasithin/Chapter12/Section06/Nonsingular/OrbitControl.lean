module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.CoreMarking
public import Theory.Representation.BinaryPermutation.EightOrbitPreservation
public import Theory.GroupTheory.ConjugationOrbitSize

/-!
# Normalizer control of the actual A₈ module orbits

For the original chosen module, every element normalizing both L and V
preserves each L-orbit on V. If the fixed space vanishes, the original
quotient marking is an isomorphism and the two natural-module orbits have
distinct sizes. Otherwise the constructed augmentation-core marking and
its orbit-preservation theorem distinguish all five orbits.

Both arguments intertwine the original conjugation and retain the map
V → V/C_V(L). This is the orbit input to the Sylow selection preceding
Theorem 12.6.2 (Aschbacher--Smith, printed pp.823--824).
-/

public section
open Subgroup BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem conjugacyOrbit_image (A : Subgroup G) (x t : G)
    (ht : t ∈ normalizer (A : Set G)) :
    (MulAut.conj t) '' conjugacyOrbit A x = conjugacyOrbit A (t*x*t⁻¹) := by
  ext y
  constructor
  · rintro ⟨_,⟨a,rfl⟩,rfl⟩
    refine ⟨⟨t*a*t⁻¹,(ht a).mp a.property⟩,?_⟩
    simp [MulAut.conj_apply,mul_assoc]
  · rintro ⟨a,rfl⟩
    have ha : t⁻¹ * (a : G) * t ∈ A := by
      simpa using ((normalizer (A : Set G)).inv_mem ht a).mp a.property
    refine ⟨(t⁻¹*a*t)*x*(t⁻¹*a*t)⁻¹,⟨⟨_,ha⟩,rfl⟩,?_⟩
    simp [MulAut.conj_apply,mul_assoc]

omit [Finite G] in
private theorem orbit_control_of_marking
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {A : Type*} [Group A] (ρ : Representation (ZMod 2) A W)
    (E : Additive V ≃ₗ[ZMod 2] W)
    (f : L →* A) (hf : Function.Surjective f)
    (hn : L ≤ normalizer (V : Set G))
    (hE : ∀ l w, E (seedRepresentation L V hn l w) = ρ (f l) (E w))
    (horbit : ∀ e : W ≃+ W,
      (∀ x, e '' (Set.range fun a : A => ρ a x) =
        Set.range fun a : A => ρ a (e x)) →
      ∀ x, ∃ a : A, ρ a x = e x)
    (n : G) (hnL : n ∈ normalizer (L : Set G))
    (hnV : n ∈ normalizer (V : Set G)) (v : V) :
    ∃ l : L, n * (v : G) * n⁻¹ = (l : G) * v * (l : G)⁻¹ := by
  let j : W → G := fun w => ((E.symm w).toMul : G)
  have hseed (l : L) (w : Additive V) :
      ((seedRepresentation L V hn l w).toMul : G) =
        (l : G) * (w.toMul : G) * (l : G)⁻¹ := rfl
  have hj : Function.Injective j :=
    Subtype.val_injective.comp (Additive.toMul.injective.comp E.symm.injective)
  have hmodel (x : W) :
      j '' (Set.range fun a : A => ρ a x) = conjugacyOrbit L (j x) := by
    ext y
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      obtain ⟨l,rfl⟩ := hf a
      refine ⟨l,?_⟩
      have he := hE l (E.symm x)
      rw [E.apply_symm_apply] at he
      have hh := congrArg j he
      simpa only [j,E.symm_apply_apply,hseed] using hh
    · rintro ⟨l,rfl⟩
      refine ⟨_,⟨f l,rfl⟩,?_⟩
      have he := hE l (E.symm x)
      rw [E.apply_symm_apply] at he
      have hh := congrArg j he
      exact (show (l : G) * j x * (l : G)⁻¹ = j (ρ (f l) x) from by
        simpa only [j,E.symm_apply_apply,hseed] using hh).symm
  let c := V.normalizerMonoidHom ⟨n,hnV⟩
  let e : W ≃+ W := E.symm.toAddEquiv.trans (c.toAdditive.trans E.toAddEquiv)
  have he (x : W) : j (e x) = n * j x * n⁻¹ := by
    change ((E.symm (E (c.toAdditive (E.symm x)))).toMul : G) = _
    rw [E.symm_apply_apply]
    rfl
  have ho (x : W) :
      e '' (Set.range fun a : A => ρ a x) = Set.range fun a : A => ρ a (e x) := by
    apply Set.image_injective.mpr hj
    rw [Set.image_image]
    have he' : (fun x => j (e x)) = (fun x => MulAut.conj n (j x)) := funext he
    rw [he', ← Set.image_image]
    change (MulAut.conj n) '' (j '' _) = j '' _
    rw [hmodel,hmodel,conjugacyOrbit_image L _ n hnL]
    exact congrArg (conjugacyOrbit L) (he x).symm
  obtain ⟨a,ha⟩ := horbit e ho (E (Additive.ofMul v))
  have hm : j (e (E (Additive.ofMul v))) ∈
      conjugacyOrbit L (j (E (Additive.ofMul v))) := by
    rw [← hmodel]
    exact ⟨_,⟨a,ha⟩,rfl⟩
  obtain ⟨l,hl⟩ := hm
  refine ⟨l,?_⟩
  rw [he] at hl
  simpa only [j,E.symm_apply_apply, toMul_ofMul] using hl.symm

theorem OrthogonalMarking.normalizer_orbit_control
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (n : G) (hnL : n ∈ normalizer (L : Set G))
    (hnV : n ∈ normalizer (V : Set G)) (v : V) :
    ∃ l : L, n * (v : G) * n⁻¹ = (l : G) * v * (l : G)⁻¹ := by
  by_cases hz : ZV L V = ⊥
  · have hfix : (fixedSeed L V chosen.normalizes).toSubmodule = ⊥ := by
      apply bot_unique
      intro w hw
      have hh := (mem_fixedSeed_iff L V chosen.normalizes w).mp hw
      rw [hz,mem_bot] at hh
      exact (show w = 0 from Additive.toMul.injective (Subtype.ext hh))
    let q := (fixedSeed L V chosen.normalizes).toSubmodule.mkQ
    have hq : Function.Bijective q :=
      ⟨LinearMap.ker_eq_bot.mp (by rw [Submodule.ker_mkQ,hfix]), Submodule.mkQ_surjective _⟩
    let E := (LinearEquiv.ofBijective q hq).trans D.coordinates
    apply orbit_control_of_marking (alternatingNaturalRepresentation (Fin 8))
      E D.actorMap D.actorMap_surjective chosen.normalizes
      (fun l w => D.equivariant l (Submodule.Quotient.mk w))
      eight_natural_orbit_preserved n hnL hnV v
  · obtain ⟨E,hE,_⟩ := D.core_marking_of_fixed_ne_bot chosen hz
    exact orbit_control_of_marking (alternatingCoreRepresentation (Fin 8))
      E D.actorMap D.actorMap_surjective chosen.normalizes hE
      eight_core_orbit_preserved n hnL hnV v

end CFSG.Quasithin.Chapter12.Section06
