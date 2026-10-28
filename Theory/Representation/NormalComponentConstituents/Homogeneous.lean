module
public import Theory.Representation.NormalComponentConstituents.Orthogonal
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.Geometry
/-!
# A normal constituent through a common marked point

If every nonzero subspace invariant under H and X contains the same nonzero
vector, an X-stable irreducible H-submodule through that vector determines
the unique occurring simple H-type. Indeed, the X-orbit of any inequivalent
constituent is disjoint from the marked constituent, contradicting containment.

For a faithful ambient irreducible representation, this homogeneity passes
faithfulness to the constituent. A preserved nondegenerate form pairs it with
an ambient conjugate, and the common simple type makes it self-dual.
These are the homogeneous branch of Aschbacher--Smith G.10.15, printed p.361.
-/

public noncomputable section
open Representation Subgroup Module
open scoped MonoidAlgebra
namespace Representation.BinaryOffender
open Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (H X : Subgroup G) [H.Normal]

/-- A common nonzero point in every nonzero HX-submodule forces the type of
an X-stable simple H-submodule to be the only occurring simple type. -/
theorem sameModule_of_common_point (v : V) (hv : v ≠ 0)
    (I : Subrepresentation (ρ.comp H.subtype)) (hI : IsIrreducible I.toRepresentation)
    (hvI : v ∈ I.toSubmodule) (hXI : X ≤ subspaceStabilizer ρ I.toSubmodule)
    (hpoint : ∀ U : Submodule (ZMod 2) V,
      H ≤ subspaceStabilizer ρ U → X ≤ subspaceStabilizer ρ U → U ≠ ⊥ → v ∈ U)
    (J : Subrepresentation (ρ.comp H.subtype)) (hJ : IsIrreducible J.toRepresentation) :
    SameModule I J := by
  classical
  by_contra hn
  let c (x : X) := conjugateSubrepresentationOrderIso ρ H (x : G)
  let N : Subrepresentation (ρ.comp H.subtype) := ⨆ x : X, c x J
  have hfix (x : X) : c x I = I := by
    apply Subrepresentation.toSubmodule_injective
    simpa only [c, conjugateSubrepresentationOrderIso_toSubmodule] using
      (subspace_map_eq_iff ρ I.toSubmodule x).mpr (hXI x.property)
  have hnot (x : X) : ¬ Nonempty (I.asSubmodule ≃ₗ[(ZMod 2)[H]] (c x J).asSubmodule) := by
    intro he
    apply hn
    apply (sameModule_iff_repEquiv I J).mpr
    apply (isaacs_6_5_nonempty_repEquiv_conjugateOrderIso_iff ρ H (x : G) I J).mpr
    rw [show conjugateSubrepresentationOrderIso ρ H (x : G) I = I from hfix x]
    exact (isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv I (c x J)).mpr he
  let := simple_asSubmodule I hI
  have hd := (component_disjoint_sum I.asSubmodule (fun x : X => (c x J).asSubmodule)
    (fun x => simple_asSubmodule _ ((Subrepresentation.irreducible_iff_isAtom _).mpr
      (((c x).isAtom_iff J).mpr ((Subrepresentation.irreducible_iff_isAtom J).mp hJ)))) hnot).mono_left
    I.asSubmodule.le_isotypicComponent
  have hNmod : N.asSubmodule = ⨆ x : X, (c x J).asSubmodule := by
    let e : Subrepresentation (ρ.comp H.subtype) ≃o
        Submodule (ZMod 2)[H] (Representation.asModule (ρ.comp H.subtype)) :=
      Subrepresentation.subrepresentationSubmoduleOrderIso
    exact e.map_iSup _
  have hNH : H ≤ subspaceStabilizer ρ N.toSubmodule := by
    apply le_subspaceStabilizer
    intro a ha w hw
    exact N.apply_mem_toSubmodule ⟨a,ha⟩ hw
  have hNX : X ≤ subspaceStabilizer ρ N.toSubmodule := by
    have he : N.toSubmodule = orbitSpan ρ X J.toSubmodule := by
      change (⨆ x : X, c x J).toSubmodule = _
      rw [toSubmodule_iSup]
      simp only [c, conjugateSubrepresentationOrderIso_toSubmodule, orbitSpan]
    rw [he]
    exact orbitSpan_invariant ρ X J.toSubmodule
  have hN0 : N.toSubmodule ≠ ⊥ := by
    intro hz
    have hle : J ≤ N := by
      simpa only [N, c, OneMemClass.coe_one, conjugateSubrepresentationOrderIso_one] using
        (le_iSup (fun x : X => c x J) 1)
    have hJ0 : J = ⊥ := Subrepresentation.toSubmodule_injective
      (le_bot_iff.mp ((show J.toSubmodule ≤ N.toSubmodule from hle).trans hz.le))
    exact ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).ne_bot hJ0
  have hvN := hpoint N.toSubmodule hNH hNX hN0
  apply hv
  have hm : (Representation.asModuleEquiv (ρ.comp H.subtype)).symm v ∈
      I.asSubmodule ⊓ ⨆ x : X, (c x J).asSubmodule := ⟨hvI,hNmod ▸ hvN⟩
  have hzmem : (Representation.asModuleEquiv (ρ.comp H.subtype)).symm v ∈
      (⊥ : Submodule (ZMod 2)[H] (Representation.asModule (ρ.comp H.subtype))) := hd.eq_bot ▸ hm
  have hz : (Representation.asModuleEquiv (ρ.comp H.subtype)).symm v = 0 := hzmem
  exact congrArg (Representation.asModuleEquiv (ρ.comp H.subtype)) hz

variable [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
/-- In a homogeneous normal restriction, faithfulness on the whole module
passes to each actual irreducible constituent. -/
theorem constituent_faithful_of_sameModule (hf : Function.Injective ρ)
    (hi : IsIrreducible ρ) (I : Subrepresentation (ρ.comp H.subtype))
    (hI : IsIrreducible I.toRepresentation)
    (hhom : ∀ J : Subrepresentation (ρ.comp H.subtype),
      IsIrreducible J.toRepresentation → SameModule I J) :
    Function.Injective I.toRepresentation := by
  intro a b hab
  have heq (J : Subrepresentation (ρ.comp H.subtype))
      (hJ : IsIrreducible J.toRepresentation) (w : V) (hw : w ∈ J.toSubmodule) :
      ρ (a : G) w = ρ (b : G) w := by
    obtain ⟨e⟩ := (sameModule_iff_repEquiv I J).mp (hhom J hJ)
    obtain ⟨u,hu⟩ := e.surjective (⟨w,hw⟩ : J.toSubmodule)
    have ha := LinearMap.congr_fun (e.isIntertwining' a) u
    have hb := LinearMap.congr_fun (e.isIntertwining' b) u
    have h := ha.symm.trans ((congrArg e (congrArg (fun f : Module.End (ZMod 2) I.toSubmodule => f u) hab)).trans hb)
    change J.toRepresentation a (e u) = J.toRepresentation b (e u) at h
    rw [hu] at h
    exact congrArg Subtype.val h
  have hspan : (⨆ g : G, (conjugateSubrepresentation ρ H I g).toSubmodule) = ⊤ := by
    rw [← toSubmodule_iSup]
    exact congrArg (fun J : Subrepresentation (ρ.comp H.subtype) => J.toSubmodule)
      (iSup_conjugateSubrepresentations_eq_top ρ H hi I hI)
  have hk : (⊤ : Submodule (ZMod 2) V) ≤ (ρ (a : G) - ρ (b : G)).ker := by
    rw [← hspan]
    refine iSup_le fun g => ?_
    have hJ : IsIrreducible (conjugateSubrepresentation ρ H I g).toRepresentation := by
      apply (Subrepresentation.irreducible_iff_isAtom _).mpr
      simpa only [conjugateSubrepresentationOrderIso_apply, inv_inv] using
        ((conjugateSubrepresentationOrderIso ρ H g⁻¹).isAtom_iff I).mpr
          ((Subrepresentation.irreducible_iff_isAtom I).mp hI)
    intro w hw
    change ρ (a : G) w - ρ (b : G) w = 0
    exact sub_eq_zero.mpr (heq _ hJ w hw)
  apply Subtype.ext
  apply hf
  ext w
  exact sub_eq_zero.mp (hk (Submodule.mem_top : w ∈ (⊤ : Submodule (ZMod 2) V)))

/-- An invariant nondegenerate form and a single occurring simple type
make the literal constituent self-dual. -/
theorem constituent_selfDual_of_sameModule
    (hi : IsIrreducible ρ) (B : LinearMap.BilinForm (ZMod 2) V)
    (hpres : ∀ g u w, B (ρ g u) (ρ g w) = B u w) (hnd : B.Nondegenerate)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ H I)
    (hhom : ∀ J : Subrepresentation (ρ.comp H.subtype),
      IsIrreducible J.toRepresentation → SameModule (invariantSubspace ρ H I hI.choose) J) :
    Nonempty (Representation.Equiv (invariantSubspace ρ H I hI.choose).toRepresentation
      (invariantSubspace ρ H I hI.choose).toRepresentation.dual) := by
  let R := invariantSubspace ρ H I hI.choose
  have hR : IsIrreducible R.toRepresentation := hI.irreducible_of_normal_restriction ρ hi H
  obtain ⟨g,u,hu,w,hw,hn⟩ := hI.exists_conjugate_nonzero_pairing ρ B hpres hi hnd H
  let J := conjugateSubrepresentation ρ H R g
  have hJ : IsIrreducible J.toRepresentation := by
    apply (Subrepresentation.irreducible_iff_isAtom _).mpr
    simpa only [J, conjugateSubrepresentationOrderIso_apply, inv_inv] using
      ((conjugateSubrepresentationOrderIso ρ H g⁻¹).isAtom_iff R).mpr
        ((Subrepresentation.irreducible_iff_isAtom R).mp hR)
  obtain ⟨e⟩ := (sameModule_iff_repEquiv R J).mp (hhom J hJ)
  let f := bilinearCrossPairing (ρ.comp H.subtype) B (fun a u w => hpres a u w) R J
  have hinj : Function.Injective f := bilinearCrossPairing_injective (ρ.comp H.subtype) B
    (fun a u w => hpres a u w) R J hR ⟨u,hu,w,hw,hn⟩
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa using e.toLinearEquiv.finrank_eq)).mp hinj
  let ed : Representation.Equiv J.toRepresentation.dual R.toRepresentation.dual :=
    .mk e.toLinearEquiv.dualMap (by
      intro a
      ext f u
      exact congrArg f (LinearMap.congr_fun (e.isIntertwining' a⁻¹) u).symm)
  exact ⟨(f.ofBijective ⟨hinj,hsurj⟩).trans ed⟩

end Representation.BinaryOffender
