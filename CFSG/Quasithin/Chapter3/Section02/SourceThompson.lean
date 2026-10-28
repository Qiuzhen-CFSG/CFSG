module
public import CFSG.Quasithin.Chapter3.Section02.SourceModuleConsequences
public import CFSG.Quasithin.Chapter3.Section02.SourceQrcInput
public import CFSG.Quasithin.Chapter3.Section02.ThompsonCommutator

/-!
# The original Thompson commutator and center obstruction in both FSU alternatives

The full orbit module lies in T. Nonzero fixed vectors for the original
actor therefore force Z(XT) nontrivial, excluding the central omega-center
branch under source uniqueness. When J(T) moves the original local module,
the faithful actor commutator dichotomy lifts through its core–Frattini
kernel and proves X=[X,J(T)]; the literal action on V is an FF-module.

These are the algebraic and central implications in 3.2.2(6), with both
source actor alternatives retained. E.2.3 and C.5.8 are still needed to
force J(T) movement on V from the nonzero fixed-space hypothesis.
Source: Aschbacher–Smith, Lemmas 3.1.7–8 and 3.2.2(6),
combined manuscript of 1 March 2004, printed pp.575–579.
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
local notation "V_M" => componentOrbit V₀ M
local notation "V_T" => componentOrbit V₀ (T : Subgroup G)

include hXM hTM hG hM hX hc hI

open Stellmacher

theorem source_reduced_seed_orbit_le_sylow : V_M ≤ (T : Subgroup G) := by
  obtain ⟨J, hJ, hi⟩ := source_reduced_seed_internal T X M hXM hTM hG hM hX hc I hI
  have he := ReducedNormal.subspaceImage_orbitSpan M M le_rfl J
  rw [subgroupOf_self, hJ] at he
  have hcore := ReducedNormal.subspaceImage_le_core M
    (orbitSpan (ReducedNormal.representation M) ⊤ J)
  rw [he] at hcore
  apply hcore.trans
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] using
    pCoreIn_le_sylow M (T.subtype hTM)

theorem source_reduced_seed_center_ne_bot
    (hfix : V_M ⊓ centralizer (X : Set G) ≠ ⊥) : center (X ⊔ (T : Subgroup G) : Subgroup G) ≠ ⊥ := by
  intro hcenter
  let H := X ⊔ (T : Subgroup G)
  let A := X.subgroupOf H
  let Q := (V_M).subgroupOf H
  let S : Sylow 2 H := T.subtype le_sup_right
  have hVH : V_M ≤ H :=
    (source_reduced_seed_orbit_le_sylow T X M hXM hTM hG hM hX hc I hI).trans le_sup_right
  have hi := source_reduced_seed_local_internal T X M hXM hTM hG hM hX hc I hI
  let := hi.normal
  let : Q.Normal := normal_subgroupOf_of_le_normalizer
    ((sup_le hXM hTM).trans (le_normalizer_componentOrbit V₀ M))
  let := source_reduced_seed_orbit_elementary T X M hXM hTM hG hM hX hc I hI
  have hp : IsPGroup 2 Q := (IsElementaryAbelian.isPGroup 2 V_M).comap_of_injective
    H.subtype H.subtype_injective
  have hgen : A ⊔ (S : Subgroup H) = ⊤ := by
    change X.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have he : Q ⊓ centralizer (A : Set H) = ⊥ :=
    inf_centralizer_eq_bot_of_centerfree_sylow_supplement S A Q hgen hp hcenter
  apply hfix
  apply le_bot_iff.mp
  intro x hx
  let xH : H := ⟨x, hVH hx.1⟩
  have hxH : xH ∈ Q ⊓ centralizer (A : Set H) :=
    ⟨hx.1, fun y hy => Subtype.ext (hx.2 y hy)⟩
  have hx1 : xH = 1 := mem_bot.mp (he ▸ hxH)
  exact congrArg H.subtype hx1

theorem source_reduced_seed_thompson_commutator
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V_T : Set G)) :
    X = ⁅X, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  let H := X ⊔ (T : Subgroup G)
  let A := X.subgroupOf H
  let S : Sylow 2 H := T.subtype le_sup_right
  let J := elementaryAbelianMaxJ (S : Subgroup H)
  let ρ := ReducedNormal.representation H
  let W := orbitSpan ρ ⊤ I
  let f := invariantActionHom ρ W (orbitSpan_invariant ρ ⊤ I)
  have hjmap : J.map H.subtype = elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le le_sup_right
  have hJT : J ≤ (S : Subgroup H) := sSup_le fun _ hA => hA.1
  have hTJ : (S : Subgroup H) ≤ normalizer (J : Set H) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change (elementaryAbelianMaxJ (S : Subgroup H)).map (MulAut.conj t).toMonoidHom = _
    have hs : (S : Subgroup H).map (MulAut.conj t).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp ((S : Subgroup H).le_normalizer ht)
    rw [← elementaryAbelianMaxJ_map_equiv, hs]
  have hjker : ¬ J ≤ f.ker := by
    intro hj
    apply hJ
    rw [← hjmap]
    rintro _ ⟨g, hg, rfl⟩ v hv
    have hfix := hj hg
    rw [invariantActionHom_ker] at hfix
    rw [← source_reduced_seed_local_orbitImage T X M hXM hTM hG hM hX hc I hI] at hv
    obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hv
    have he := congrArg (fun z : Additive (ReducedNormal.ModuleGroup H) => z.toMul.val.val)
      (hfix.2 (Additive.ofMul w) hw)
    change (g : G) * w.val.val * (g : G)⁻¹ = w.val.val at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hgen : A ⊔ (S : Subgroup H) = ⊤ := by
    change X.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hi := source_reduced_seed_local_internal T X M hXM hTM hG hM hX hc I hI
  have he := hi.actor_eq_commutator_of_moving_twoGroup hgen hJT hTJ hjker
  have hm := congrArg (map H.subtype) he
  change A.map H.subtype = (⁅A, J⁆).map H.subtype at hm
  have hAM : A.map H.subtype = X := map_subgroupOf_eq_of_le le_sup_left
  rw [map_commutator, hAM, hjmap] at hm
  exact hm

theorem source_reduced_seed_module_isFF
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V_T : Set G)) :
    letI := source_reduced_seed_local_elementary T X M hXM hTM hG hM hX hc I hI
    Representation.BinaryOffender.IsFFModule
      (ChapterD.UniqueFactor.imageRepresentation (X ⊔ (T : Subgroup G)) V_T
        (source_reduced_seed_local_normalizes T X M hXM hTM hG hM hX hc I hI)) := by
  let := source_reduced_seed_local_elementary T X M hXM hTM hG hM hX hc I hI
  have hVT : V_T ≤ (T : Subgroup G) := by
    apply (source_reduced_seed_local_le_core T X M hXM hTM hG hM hX hc I hI).trans
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (X ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  exact Chapter3.internalActionImage_isFFModule_of_thompson_not_le T _ _ le_sup_right hVT
    (source_reduced_seed_local_normalizes T X M hXM hTM hG hM hX hc I hI) hJ

theorem source_reduced_seed_omega_center_not_central
    (hfix : V_M ⊓ centralizer (X : Set G) ≠ ⊥)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center Y).map Y.subtype := by
  intro hz
  apply source_reduced_seed_center_ne_bot T X M hXM hTM hG hM hX hc I hI hfix
  have hq := source_reduced_seed_qrc_hypotheses T X M hXM hTM hG hM hX hc I hI hY
  exact hq.center_eq_bot_of_omega_center_centralizes (hG.evenCharacteristic T) hM hu hz

end CFSG.Quasithin.Chapter3.Section02
