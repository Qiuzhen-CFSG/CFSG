module
public import CFSG.Quasithin.ChapterD.Section03.SeedFitting
public import Theory.Representation.BinaryOffender.Homogeneous.AutomorphismTwist
public import Theory.Representation.BinaryOffender.Homogeneous.Existence
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter

/-!
# Homogeneous seeds for the component-orbit action

The two-core of K₀T centralizes every component in K₀ and is contained
in T. Homogeneity therefore makes it stabilize the chosen Irr⁺ seed.
For a faithful action with trivial ambient two-core, both K and K₀
have trivial two-core, and the literal restricted action satisfies
Hypothesis D.3.2. The source application is in `SourceModels.Source`.

Source: Aschbacher–Smith, F.9.18(1), printed p.325, and D.3.2, p.193.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
variable {D E : Type*} [Group D] [Finite D] [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) D E)

omit [Finite D] in
private theorem homogeneous_centralizer_stabilizes {X T : Subgroup D}
    {I : Submodule (ZMod 2) E} (hI : IsIrrPlusWith ρ X T I) :
    T ⊓ centralizer (X : Set D) ≤ subspaceStabilizer ρ I := by
  intro t ht
  apply (subspace_map_eq_iff ρ I t).mp
  apply hI.map_eq_of_central_twist ρ ⟨t, ht.1⟩ (LinearEquiv.refl _ _)
  intro x v
  have he : X.normalizerMonoidHom
      ⟨t⁻¹, hI.normalizes (T.inv_mem ht.1)⟩ x = x := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
    have hc := mem_centralizer_iff.mp ht.2 (x : D) x.property
    calc
      t⁻¹ * (x : D) * t = t⁻¹ * ((x : D) * t) := mul_assoc _ _ _
      _ = t⁻¹ * (t * x) := by rw [hc]
      _ = x := inv_mul_cancel_left _ _
  simp only [he, LinearEquiv.refl_apply]

private theorem orbit_core_centralizes (K T : Subgroup D) (hK : IsComponent D K) :
    (componentOrbit K T ⊔ T).pCoreIn 2 ≤ centralizer (componentOrbit K T : Set D) := by
  let J := componentOrbit K T ⊔ T
  have hCJ : ∀ C : Subgroup D, IsComponent D C → C ≤ J →
      C ≤ centralizer (J.pCoreIn 2 : Set D) := by
    intro C hC hCJ
    let : Group.IsNilpotent (pCore 2 J) := pCore_isNilpotent
    have hc := (hC.subgroupOf hCJ).le_centralizer_of_solvable_normal (pCore 2 J)
    intro c hcC
    apply mem_centralizer_iff.mpr
    rintro p ⟨p, hp, rfl⟩
    have hh := mem_centralizer_iff.mp (hc (show (⟨c, hCJ hcC⟩ : J) ∈ C.subgroupOf J from hcC)) p hp
    exact congrArg Subtype.val hh
  apply le_centralizer_iff.mpr
  apply iSup_le
  intro t
  exact hCJ _ (hK.map_conj t) ((le_iSup (fun t : T => K.map (MulAut.conj (t : D)).toMonoidHom) t).trans le_sup_left)

theorem homogeneous_orbit_core_invariant (K : Subgroup D) (T : Sylow 2 D)
    (hK : IsComponent D K) {I : Submodule (ZMod 2) E}
    (hI : IsIrrPlusWith ρ (componentOrbit K T) T I) :
    (componentOrbit K T ⊔ (T : Subgroup D)).pCoreIn 2 ≤ subspaceStabilizer ρ I := by
  have hTJ : (T : Subgroup D) ≤ componentOrbit K T ⊔ (T : Subgroup D) := le_sup_right
  have hPT : (componentOrbit K T ⊔ (T : Subgroup D)).pCoreIn 2 ≤ T := by
    have hc := pCoreIn_le_sylow _ (T.subtype hTJ)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTJ] using hc
  exact (le_inf hPT (orbit_core_centralizes K T hK)).trans
    (homogeneous_centralizer_stabilizes ρ hI)

private theorem subnormal_twoCore_eq_bot (X : Subgroup D) (hX : X.IsSubnormal)
    (hcore : pCore 2 D = ⊥) : pCore 2 X = ⊥ := by
  have hh := pCoreAmbient_mono_of_isSubnormalIn X ⊤ 2 le_top
    (hX.comap (⊤ : Subgroup D).subtype)
  have he : (pCore 2 (⊤ : Subgroup D)).map (⊤ : Subgroup D).subtype = pCore 2 D :=
    pCore_map_iso 2 Subgroup.topEquiv
  rw [he, hcore] at hh
  apply map_injective X.subtype_injective
  rw [Subgroup.map_bot]
  exact bot_unique hh

theorem internal_module_of_component_orbit [Module.Finite (ZMod 2) E]
    {κ : GroupClass} (hsq : IsSQTK κ D) (hf : Function.Injective ρ)
    (hcore : pCore 2 D = ⊥) (K : Subgroup D) (T : Sylow 2 D)
    (hK : IsComponent D K) (hn : (componentOrbit K T).Normal)
    {I : Submodule (ZMod 2) E} (hI : IsIrrPlusWith ρ (componentOrbit K T) T I) :
    ChapterD.Section03.InternalModuleHypotheses κ
      ρ T (componentOrbit K T) I := by
  let X := componentOrbit K T
  let : X.Normal := hn
  let : Group.IsPerfect X := hK.orbit_isPerfect T
  let : IsQuasisimple K := hK.2
  have hXcore := subnormal_twoCore_eq_bot X hn.isSubnormal hcore
  have hKcore := subnormal_twoCore_eq_bot K hK.1 hcore
  let eK : (K ⧸ pCore 2 K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hKcore).trans (QuotientGroup.quotientBot)
  let τ : Representation (ZMod 2) X E := ρ.comp X.subtype
  let eX : X ≃* actionImage τ := MulEquiv.ofBijective (actionHom τ)
    ⟨fun x y he => Subtype.ext (hf (congrArg (imageRepresentation τ) he)),
      (Representation.asGroupHom τ).rangeRestrict_surjective⟩
  have hp : IsPPerfect 2 X := by
    intro N hN hQ
    let := hN
    let : Group.IsNilpotent (X ⧸ N) := hQ.isNilpotent
    let : Group.IsPerfect (X ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    have he : Subsingleton (X ⧸ N) := by
      by_contra! hne
      exact Group.IsPerfect.not_isSolvable (X ⧸ N) inferInstance
    apply top_unique
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  refine ⟨hsq, inferInstance, hn, (pResidual_eq_top_iff 2 X).mpr hp,
    Or.inl ⟨K, hK.isCComponent, IsQuasisimple.of_mulEquiv eK.symm, rfl⟩, ?_,
    hI.isIrrPlus, homogeneous_orbit_core_invariant ρ K T hK hI⟩
  rw [← pCore_map_iso 2 eX, hXcore, Subgroup.map_bot]
end CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
