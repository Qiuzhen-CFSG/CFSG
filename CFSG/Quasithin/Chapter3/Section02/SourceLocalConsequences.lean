module
public import CFSG.Quasithin.Chapter3.Section02.SourceLocalInput
public import Theory.GroupTheory.ReducedNormal.OrbitReduced
public import Theory.GroupTheory.PCoreResidualFrattiniKernel

/-!
# The local source module under both actor alternatives

The original seed in R₂(XT) satisfies the internal D.3.2 hypotheses in XT.
Since X preserves the seed, its full XT-orbit is exactly its T-orbit V.
The faithful D.3.3–4 action proves V is reduced. The actor kernel lies in
O₂,Φ(X), and X=O²(XT); the Sylow Frattini-kernel theorem therefore gives
C_T(V)=O₂(XT). Every subgroup and action remains the original one in G.

Source: Aschbacher–Smith, Lemma 3.2.2(8), combined manuscript
of 1 March 2004, printed p.579.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  (T : Sylow 2 G) (X M : Subgroup G) (hXM : X ≤ M) (hTM : (T : Subgroup G) ≤ M)
  [(X.subgroupOf M).Normal]
  (hG : IsSimpleQTKE K G) (hM : IsMaximalTwoLocal M)
  (hX : pResidual 2 (X.subgroupOf M) = ⊤)
  (hc : InternalActorCases (T.subtype hTM) (X.subgroupOf M)
    le_normalizer_of_normal)
  (I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G)))))
  (hI : IsIrrPlus (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
    (X.subgroupOf (X ⊔ (T : Subgroup G))) I)

local notation "V₀" => ReducedNormal.subspaceImage (X ⊔ (T : Subgroup G)) I
local notation "V_T" => componentOrbit V₀ (T : Subgroup G)

include hXM hTM hG hM hX hc hI

theorem source_reduced_seed_local_orbitSpan :
    orbitSpan (ReducedNormal.representation (X ⊔ (T : Subgroup G))) ⊤ I =
      orbitSpan (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
        ((T : Subgroup G).subgroupOf (X ⊔ (T : Subgroup G))) I := by
  let H := X ⊔ (T : Subgroup G)
  let ρ := ReducedNormal.representation H
  let A := X.subgroupOf H
  let S := (T : Subgroup G).subgroupOf H
  have hi := source_reduced_seed_local_internal T X M hXM hTM hG hM hX hc I hI
  let := hi.normal
  have hj : A ⊔ S = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hnorm : S ≤ normalizer (A : Set H) := by rw [normalizer_eq_top]; exact le_top
  have hs : (⊤ : Subgroup H) ≤ subspaceStabilizer ρ (orbitSpan ρ S I) := by
    rw [← hj]
    exact sup_le (orbitSpan_component_invariant ρ hnorm hI) (orbitSpan_invariant ρ S I)
  exact le_antisymm (orbitSpan_le ρ (le_orbitSpan ρ S I) hs)
    (orbitSpan_le ρ (le_orbitSpan ρ ⊤ I)
      (le_top.trans (orbitSpan_invariant ρ ⊤ I)))

theorem source_reduced_seed_local_orbitImage :
    ReducedNormal.subspaceImage (X ⊔ (T : Subgroup G))
      (orbitSpan (ReducedNormal.representation (X ⊔ (T : Subgroup G))) ⊤ I) = V_T := by
  rw [source_reduced_seed_local_orbitSpan T X M hXM hTM hG hM hX hc I hI]
  exact ReducedNormal.subspaceImage_orbitSpan (X ⊔ (T : Subgroup G)) T le_sup_right I

theorem source_reduced_seed_local_elementary : IsElementaryAbelian 2 V_T := by
  rw [← source_reduced_seed_local_orbitImage T X M hXM hTM hG hM hX hc I hI]
  exact ReducedNormal.subspaceImage_elementary _ _

theorem source_reduced_seed_local_le_core : V_T ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  rw [← source_reduced_seed_local_orbitImage T X M hXM hTM hG hM hX hc I hI]
  exact ReducedNormal.subspaceImage_le_core _ _

theorem source_reduced_seed_local_normalizes :
    X ⊔ (T : Subgroup G) ≤ normalizer (V_T : Set G) := by
  rw [← source_reduced_seed_local_orbitImage T X M hXM hTM hG hM hX hc I hI]
  apply ReducedNormal.subspaceImage_normalizes _ _ le_rfl
  rw [subgroupOf_self]
  exact orbitSpan_invariant _ ⊤ I

theorem source_reduced_seed_local_reduced :
    IsPReduced 2 ((V_T).subgroupOf (X ⊔ (T : Subgroup G))) := by
  have hi := source_reduced_seed_local_internal T X M hXM hTM hG hM hX hc I hI
  have hr := ReducedNormal.subspaceImage_isPReduced_of_action_core (X ⊔ (T : Subgroup G))
    (orbitSpan (ReducedNormal.representation (X ⊔ (T : Subgroup G))) ⊤ I)
    (orbitSpan_invariant _ ⊤ I) hi.faithfulOrbit_twoCore_eq_bot
  rwa [source_reduced_seed_local_orbitImage T X M hXM hTM hG hM hX hc I hI] at hr

theorem source_reduced_seed_local_centralizer :
    (T : Subgroup G) ⊓ centralizer (V_T : Set G) =
      (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let H := X ⊔ (T : Subgroup G)
  let A := X.subgroupOf H
  let S : Sylow 2 H := T.subtype le_sup_right
  let ρ := ReducedNormal.representation H
  let W := orbitSpan ρ ⊤ I
  let f := invariantActionHom ρ W (orbitSpan_invariant ρ ⊤ I)
  have hi := source_reduced_seed_local_internal T X M hXM hTM hG hM hX hc I hI
  let := hi.normal
  have hgen : A ⊔ (S : Subgroup H) = ⊤ := by
    change X.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hR : pResidual 2 H = A := pResidual_eq_of_isPPerfect_sup A S
    ((pResidual_eq_top_iff 2 A).mp hi.residual) S.isPGroup' hgen
  have hcore : pCore 2 H ≤ (actionHom ρ).ker := by
    rw [ReducedNormal.representation_action_kernel]
    exact le_centralizer_iff.mp (reducedPSubgroup_le_centralizer_pCore 2 H)
  have hkill : pCore 2 H ≤ f.ker := by
    rw [invariantActionHom_ker]
    intro g hg
    exact ⟨mem_top _, fun v _ => (actionHom_eq_one_iff ρ g).mp (hcore hg) v⟩
  have hkX : A ⊓ f.ker ≤ (coreFrattiniIn A).map A.subtype := by
    intro x hx
    apply hi.orbit_actorKernel_le_coreFrattini
    rw [invariantActionHom_ker] at hx
    exact ⟨hx.1, hx.2.2⟩
  have hk : pResidual 2 H ⊓ f.ker ≤
      (coreFrattiniIn (pResidual 2 H)).map (pResidual 2 H).subtype := by
    rw [hR]
    exact hkX
  have he := f.sylow_inf_ker_eq_pCore_of_residual_frattini_kernel
    (invariantActionHom_surjective ρ W _) S hkill hk
  have hmap : ((S : Subgroup H) ⊓ f.ker).map H.subtype =
      (T : Subgroup G) ⊓ centralizer (V_T : Set G) := by
    ext g
    constructor
    · rintro ⟨x, ⟨hxS, hxf⟩, rfl⟩
      refine ⟨hxS, mem_centralizer_iff.mpr ?_⟩
      intro v hv
      rw [← source_reduced_seed_local_orbitImage T X M hXM hTM hG hM hX hc I hI] at hv
      obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hv
      have hfix : ∀ z ∈ W, ρ x z = z := by
        rw [invariantActionHom_ker] at hxf
        exact hxf.2
      have hh := congrArg (fun z : Additive (ReducedNormal.ModuleGroup H) => z.toMul.val.val)
        (hfix (Additive.ofMul w) hw)
      change (x : G) * w.val.val * (x : G)⁻¹ = w.val.val at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · rintro ⟨hgT, hgC⟩
      let x : H := ⟨g, (show (T : Subgroup G) ≤ H from le_sup_right) hgT⟩
      refine ⟨x, ⟨hgT, ?_⟩, rfl⟩
      rw [invariantActionHom_ker]
      refine ⟨mem_top _, ?_⟩
      intro v hv
      apply ReducedNormal.representation_fixes_of_centralizes_subspaceImage H W x
        (by rwa [source_reduced_seed_local_orbitImage T X M hXM hTM hG hM hX hc I hI]) v hv
  have hm := congrArg (map H.subtype) he
  rw [hmap] at hm
  exact hm

theorem source_reduced_seed_local_consequences :
    IsPReduced 2 ((V_T).subgroupOf (X ⊔ (T : Subgroup G))) ∧
      (T : Subgroup G) ⊓ centralizer (V_T : Set G) =
        (X ⊔ (T : Subgroup G)).pCoreIn 2 :=
  ⟨source_reduced_seed_local_reduced T X M hXM hTM hG hM hX hc I hI,
    source_reduced_seed_local_centralizer T X M hXM hTM hG hM hX hc I hI⟩

end CFSG.Quasithin.Chapter3.Section02
