module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.LocalGeometry.Action
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The two local actions and a sufficient submodule geometry

Both N_L(V) and N_{L′}(V) embed in the actual overgroup M. Their actions
are restrictions of ambient conjugation, and the kernels are their relative
centralizers of V. Thus their faithful quotients have the intended meaning.

For the double-cover case, a nonzero invariant subspace for the first local
action must contain z; a proper invariant subspace for the second must lie
in Q⟨r⟩, which excludes z. These two local bounds imply irreducibility of
M on V. They remain explicit premises here: abstract indecomposability is
not used as a substitute for these subspace calculations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 16.4.7, printed pp.1186–1187.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow
variable {G : Type*} [Group G]

/-- The actual relative normalizer N_L(V). -/
def firstLocal (L : Subgroup G) (r z : G) : Subgroup G :=
  L ⊓ normalizer (shadowSpace L r z : Set G)

/-- The actual relative normalizer N_{L′}(V). -/
def secondLocal (L : Subgroup G) (g r z : G) : Subgroup G :=
  L.conjBy g ⊓ normalizer (shadowSpace L r z : Set G)

theorem firstLocal_le_shadowOvergroup (L : Subgroup G) (g r z : G) :
    firstLocal L r z ≤ shadowOvergroup L g r z :=
  (inf_le_inf_right _ L.le_normalizer).trans le_sup_left

theorem secondLocal_le_shadowOvergroup (L : Subgroup G) (g r z : G) :
    secondLocal L g r z ≤ shadowOvergroup L g r z := by
  have hLK : L ≤ normalizer (centralizer (L : Set G) : Set G) :=
    (le_centralizer_iff.mpr le_rfl).trans (centralizer_le_normalizer _)
  have hc : L.conjBy g ≤ normalizer ((centralizer (L : Set G)).conjBy g : Set G) := by
    change L.map (MulAut.conj g).toMonoidHom ≤
      normalizer ((centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom : Set G)
    rw [← map_equiv_normalizer_eq]
    exact map_mono hLK
  exact (inf_le_inf_right _ hc).trans le_sup_right

noncomputable def firstLocalAction (L : Subgroup G) (g r z : G) :
    firstLocal L r z →* MulAut (shadowSpace L r z) :=
  (shadowAction L g r z).comp (inclusion (firstLocal_le_shadowOvergroup L g r z))

noncomputable def secondLocalAction (L : Subgroup G) (g r z : G) :
    secondLocal L g r z →* MulAut (shadowSpace L r z) :=
  (shadowAction L g r z).comp (inclusion (secondLocal_le_shadowOvergroup L g r z))

abbrev firstLocalActionQuotient (L : Subgroup G) (g r z : G) :=
  firstLocal L r z ⧸ (firstLocalAction L g r z).ker

abbrev secondLocalActionQuotient (L : Subgroup G) (g r z : G) :=
  secondLocal L g r z ⧸ (secondLocalAction L g r z).ker

theorem firstLocalAction_apply (L : Subgroup G) (g r z : G)
    (a : firstLocal L r z) (v : shadowSpace L r z) :
    (firstLocalAction L g r z a v : G) = a * v * (a : G)⁻¹ := rfl

theorem secondLocalAction_apply (L : Subgroup G) (g r z : G)
    (a : secondLocal L g r z) (v : shadowSpace L r z) :
    (secondLocalAction L g r z a v : G) = a * v * (a : G)⁻¹ := rfl

theorem firstLocalAction_ker (L : Subgroup G) (g r z : G) :
    (firstLocalAction L g r z).ker =
      (centralizer (shadowSpace L r z : Set G)).subgroupOf (firstLocal L r z) := by
  rw [firstLocalAction, ← MonoidHom.comap_ker, shadowAction_ker]
  rfl

theorem secondLocalAction_ker (L : Subgroup G) (g r z : G) :
    (secondLocalAction L g r z).ker =
      (centralizer (shadowSpace L r z : Set G)).subgroupOf (secondLocal L g r z) := by
  rw [secondLocalAction, ← MonoidHom.comap_ker, shadowAction_ker]
  rfl

def markedZ (L : Subgroup G) (r z : G) : shadowSpace L r z :=
  ⟨z, (show zpowers z ≤ shadowSpace L r z from le_sup_right.trans le_sup_right)
    (mem_zpowers z)⟩

def markedR (L : Subgroup G) (r z : G) : shadowSpace L r z :=
  ⟨r, (show zpowers r ≤ shadowSpace L r z from le_sup_left.trans le_sup_right)
    (mem_zpowers r)⟩

noncomputable def shadowSubspace (L : Subgroup G) (r z : G)
    [IsElementaryAbelian 2 (shadowSpace L r z)] (A : Subgroup G) :
    Submodule (ZMod 2) (Additive (shadowSpace L r z)) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (A.subgroupOf (shadowSpace L r z)))

theorem mem_shadowSubspace (L A : Subgroup G) (r z : G)
    [IsElementaryAbelian 2 (shadowSpace L r z)] (v : Additive (shadowSpace L r z)) :
    v ∈ shadowSubspace L r z A ↔ (v.toMul : G) ∈ A := Iff.rfl

/-- Crossed socle and radical bounds give actual irreducibility. The
local bounds must be supplied by the two model-action calculations. -/
theorem shadowRepresentation_irreducible_of_local_geometry
    (L : Subgroup G) (g r z : G) [IsElementaryAbelian 2 (shadowSpace L r z)]
    (hz : z ≠ 1) (hzQr : z ∉ residualCore L r ⊔ zpowers r)
    (hsocle : ∀ W : Submodule (ZMod 2) (Additive (shadowSpace L r z)),
      (∀ a : firstLocal L r z, ∀ v ∈ W,
        shadowRepresentation L g r z
          (inclusion (firstLocal_le_shadowOvergroup L g r z) a) v ∈ W) →
      W ≠ ⊥ → Additive.ofMul (markedZ L r z) ∈ W)
    (hradical : ∀ W : Submodule (ZMod 2) (Additive (shadowSpace L r z)),
      (∀ a : secondLocal L g r z, ∀ v ∈ W,
        shadowRepresentation L g r z
          (inclusion (secondLocal_le_shadowOvergroup L g r z) a) v ∈ W) →
      W ≠ ⊤ → W ≤ shadowSubspace L r z (residualCore L r ⊔ zpowers r)) :
    Representation.IsIrreducible (shadowRepresentation L g r z) := by
  let : Nontrivial (Additive (shadowSpace L r z)) :=
    nontrivial_iff.mpr ⟨Additive.ofMul (markedZ L r z), 0, fun he =>
      hz (congrArg (fun v : Additive (shadowSpace L r z) => (v.toMul : G)) he)⟩
  let : Nontrivial (Subrepresentation (shadowRepresentation L g r z)) :=
    nontrivial_iff.mpr ⟨⊥, ⊤, fun he =>
      (bot_ne_top : (⊥ : Submodule (ZMod 2) (Additive (shadowSpace L r z))) ≠ ⊤)
        (congrArg Subrepresentation.toSubmodule he)⟩
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, ?_⟩
  intro W
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  by_contra ht
  have hb' : W.toSubmodule ≠ ⊥ := fun he => hb
    (Subrepresentation.toSubmodule_injective he)
  have ht' : W.toSubmodule ≠ ⊤ := fun he => ht
    (Subrepresentation.toSubmodule_injective he)
  have hZ := hsocle W.toSubmodule
    (fun a v hv => W.apply_mem_toSubmodule _ hv) hb'
  have hle := hradical W.toSubmodule
    (fun a v hv => W.apply_mem_toSubmodule _ hv) ht'
  exact hzQr (hle hZ)

theorem shadowSpace_finrank [Finite G] (L : Subgroup G) (r z : G)
    [IsElementaryAbelian 2 (shadowSpace L r z)]
    (hc : Nat.card (shadowSpace L r z) = 64) :
    Module.finrank (ZMod 2) (Additive (shadowSpace L r z)) = 6 := by
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (shadowSpace L r z))
  rw [← Nat.card_congr Additive.ofMul, hc, Nat.card_zmod] at he
  exact (Nat.pow_right_injective (by decide : 1 < 2)) he.symm

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow
