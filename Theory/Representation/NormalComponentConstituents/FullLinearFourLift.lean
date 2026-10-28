module
public import Theory.Representation.NormalComponentConstituents.FullLinear
public import Theory.LinearAlgebra.BinaryInvariantAlternating

/-!
# Lifting a full binary constituent image

A full linear constituent is isotropic. A complementary conjugate then gives
an injective cross-pairing and makes its normal actor faithful. Homogeneity
forces the ambient centralizer to preserve that constituent; a trivial full
linear center and ambient irreducibility kill this centralizer as well.

These arguments retain the original action and bilinear form. They support
the exceptional full-four reconstruction at G.10.15 and G.11.6, printed
pp.363 and 366, without using the failed full-four exclusion.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.FullLinearFourLift

theorem isotropic_of_full_constituent
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (B : LinearMap.BilinForm (ZMod 2) V)
    (halt : B.IsAlt) (hp : ∀ g u w, B (ρ g u) (ρ g w) = B u w)
    (H : Subgroup G) (I : Submodule (ZMod 2) V)
    (hH : H ≤ subspaceStabilizer ρ I) (hd : 3 ≤ finrank (ZMod 2) I)
    (hs : Function.Surjective (invariantSubspace ρ H I hH).toRepresentation.asGroupHom) :
    ∀ u ∈ I, ∀ w ∈ I, B u w = 0 := by
  have hz : B.restrict I = 0 := by
    apply LinearMap.BilinForm.eq_zero_of_full_binary_linear_invariance (B.restrict I)
      (fun u => halt (u : V)) _ hd
    intro e u w
    obtain ⟨g,hg⟩ := hs ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).symm e)
    have he (z : I) : e z = (invariantSubspace ρ H I hH).toRepresentation g z :=
      (congrArg (fun a : LinearMap.GeneralLinearGroup (ZMod 2) I => a.val z) hg).symm
    change B (e u) (e w) = B u w
    rw [he,he]
    exact hp g u w
  intro u hu w hw
  exact congrArg (fun C : LinearMap.BilinForm (ZMod 2) I => C ⟨u,hu⟩ ⟨w,hw⟩) hz

theorem centralizer_stabilizes_homogeneous
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (H X : Subgroup G) [H.Normal]
    (I : Submodule (ZMod 2) V) (hI : Homogeneous.IsIrrPlusWith ρ H X I)
    (hfix : fixedSpace ρ H = ⊥) (hgen : Homogeneous.orbitSpan ρ X I = ⊤) :
    centralizer (H : Set G) ≤ subspaceStabilizer ρ I := by
  intro g hg
  let J := I.map (ρ g)
  have hJ : H ≤ subspaceStabilizer ρ J :=
    (hI.isIrrPlus.map_normalizer ρ (H.normalizer_eq_top.symm ▸ mem_top g)).choose
  let R := invariantSubspace ρ H I hI.invariant
  let S := invariantSubspace ρ H J hJ
  let e : I ≃ₗ[ZMod 2] J :=
    Submodule.equivMapOfInjective (ρ g) (ρ.apply_bijective g).injective I
  have he (a : H) (u : I) : e (R.toRepresentation a u) = S.toRepresentation a (e u) := by
    apply Subtype.ext
    change ρ g (ρ (a : G) u) = ρ (a : G) (ρ g u)
    rw [← Module.End.mul_apply,← map_mul,← Module.End.mul_apply,← map_mul,hg a a.property]
  let q := (fixedSpace ρ H).mkQ
  have hq : Function.Injective q := LinearMap.ker_eq_bot.mp
    ((Submodule.ker_mkQ _).trans hfix)
  let qI := Submodule.equivMapOfInjective q hq I
  let qJ := Submodule.equivMapOfInjective q hq J
  let c := (qI.symm.trans e).trans qJ
  have hc : Homogeneous.SameModule (Homogeneous.quotientImage ρ H I hI.invariant)
      (Homogeneous.quotientImage ρ H J hJ) := by
    refine ⟨c,?_⟩
    intro a u
    obtain ⟨w,rfl⟩ := qI.surjective u
    let w' : I := ⟨ρ a w,(hI.invariant a.property w).2 w.property⟩
    have hIq : (Homogeneous.quotientImage ρ H I hI.invariant).toRepresentation a (qI w) =
        qI w' := rfl
    have hJq (z : J) : (Homogeneous.quotientImage ρ H J hJ).toRepresentation a (qJ z) =
        qJ ⟨ρ a z,(hJ a.property z).2 z.property⟩ := rfl
    rw [hIq]
    change qJ (e (qI.symm (qI w'))) =
      (Homogeneous.quotientImage ρ H J hJ).toRepresentation a (qJ (e (qI.symm (qI w))))
    rw [qI.symm_apply_apply,qI.symm_apply_apply,hJq]
    exact congrArg qJ (he a w)
  have hle : J ≤ I := by
    apply (Submodule.map_le_map_iff_of_injective hq J I).mp
    apply hI.contains_isomorphic ρ _ _ hc
    rw [hgen]
    exact Submodule.map_mono le_top
  exact (subspace_map_eq_iff ρ I g).mp
    (Submodule.eq_of_le_of_finrank_eq hle (finrank_map_action ρ I g))

theorem centralizer_eq_bot_of_full_homogeneous
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (H X : Subgroup G) [H.Normal]
    (I : Submodule (ZMod 2) V) (hI : Homogeneous.IsIrrPlusWith ρ H X I)
    (hfix : fixedSpace ρ H = ⊥) (hgen : Homogeneous.orbitSpan ρ X I = ⊤)
    (hd : 0 < finrank (ZMod 2) I)
    (hs : Function.Surjective (invariantSubspace ρ H I hI.invariant).toRepresentation.asGroupHom) :
    centralizer (H : Set G) = ⊥ := by
  let C := centralizer (H : Set G)
  have hCI := centralizer_stabilizes_homogeneous ρ H X I hI hfix hgen
  have hfixed : I ≤ fixedSpace ρ C := by
    intro u hu g
    let y : subspaceStabilizer ρ I := ⟨g,hCI g.property⟩
    have hz : (stabilizerRepresentation ρ I).asGroupHom y ∈
        center (LinearMap.GeneralLinearGroup (ZMod 2) I) := by
      apply mem_center_iff.mpr
      intro b
      obtain ⟨a,rfl⟩ := hs b
      apply Units.ext
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      change ρ (a : G) (ρ (g : G) w) = ρ (g : G) (ρ (a : G) w)
      rw [← Module.End.mul_apply,← map_mul,← Module.End.mul_apply,← map_mul,
        g.property a a.property]
    rw [binary_full_center_eq_bot (V := I) hd,mem_bot] at hz
    exact congrArg (fun a : LinearMap.GeneralLinearGroup (ZMod 2) I => (a.val ⟨u,hu⟩ : V)) hz
  by_contra hne
  have hzero := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi C hne
  exact hI.isIrrPlus.ne_bot ρ (bot_unique (hzero ▸ hfixed))

theorem faithful_isotropic_pair
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (B : LinearMap.BilinForm (ZMod 2) V) (hnd : B.Nondegenerate)
    (hp : ∀ g u w, B (ρ g u) (ρ g w) = B u w)
    (H : Subgroup G) [H.Normal] (I : Submodule (ZMod 2) V)
    (hI : H ≤ subspaceStabilizer ρ I)
    (hi : IsIrreducible (invariantSubspace ρ H I hI).toRepresentation)
    (hiso : ∀ u ∈ I, ∀ w ∈ I, B u w = 0) (x : G)
    (hspan : I ⊔ I.map (ρ x⁻¹) = ⊤) :
    Function.Injective (invariantSubspace ρ H I hI).toRepresentation.asGroupHom := by
  let R := invariantSubspace ρ H I hI
  let J := conjugateSubrepresentation ρ H R x
  have hj : IsIrreducible J.toRepresentation := by
    apply (Subrepresentation.irreducible_iff_isAtom _).mpr
    simpa only [J,conjugateSubrepresentationOrderIso_apply,inv_inv] using
      ((conjugateSubrepresentationOrderIso ρ H x⁻¹).isAtom_iff R).mpr
        ((Subrepresentation.irreducible_iff_isAtom R).mp hi)
  have hisoJ : ∀ u ∈ J.toSubmodule, ∀ w ∈ J.toSubmodule, B u w = 0 := by
    rintro u ⟨u',hu,rfl⟩ w ⟨w',hw,rfl⟩
    exact (hp x⁻¹ u' w').trans (hiso u' hu w' hw)
  have hne : ∃ u ∈ J.toSubmodule, ∃ w ∈ I, B u w ≠ 0 := by
    by_contra! hz
    have hbot : J.toSubmodule = ⊥ := by
      apply bot_unique
      intro u hu
      apply hnd.1 u
      intro w
      have hw : w ∈ I ⊔ I.map (ρ x⁻¹) := hspan.symm ▸ Submodule.mem_top
      obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hw
      rw [map_add,hz u hu a ha,hisoJ u hu b hb,add_zero]
    exact ((Subrepresentation.irreducible_iff_isAtom J).mp hj).ne_bot
      (Subrepresentation.toSubmodule_injective hbot)
  let f := bilinearCrossPairing (ρ.comp H.subtype) B (fun g u w => hp g u w) J R
  have hinj := bilinearCrossPairing_injective (ρ.comp H.subtype) B
    (fun g u w => hp g u w) J R hj hne
  have hdim : finrank (ZMod 2) J.toSubmodule = finrank (ZMod 2) R.toSubmodule :=
    finrank_map_action ρ I x⁻¹
  let e := f.ofBijective ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simpa using hdim)).mp hinj⟩
  exact faithful_of_spanning_dual_pair ρ hf H I hI x hspan e


end Representation.BinaryOffender.FullLinearFourLift
