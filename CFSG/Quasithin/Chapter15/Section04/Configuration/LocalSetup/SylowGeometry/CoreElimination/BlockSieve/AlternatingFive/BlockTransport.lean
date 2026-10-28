module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.SourceComparison
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.ModelTransport
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Transport and exclusion of an actual alternating-five block

Let V be normal elementary abelian in H, with C_H(V) = O₂(H). A subnormal
block L embeds modulo O₂(L) into H/O₂(H), by restriction of the ambient
core. The block model therefore gives an actual embedding of its acting group.

Inside Additive V take W = V ∩ U(L), with U(L) mapped into H. Restrict the
block's quotient map U(L) → U(L)/C_U(L)(L) to W, then compose with its module
isomorphism. Its kernel is fixed by L. Subnormality and O²(L) = L give
[V,L] ≤ U(L), so L acts trivially on V/W. These constructions give the
central section required by the alternating-five fixed-space obstruction;
neither extension is assumed to split, and the restricted map need not be onto.

The final corollary transports the block through `subgroupOfEquivOfLe` and
uses the source's existing module and Sylow seed. Subnormality is relative
to the local overgroup throughout.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7 and
C.1.12, printed pp.123–124; C.2.7(3), printed p.145; the characteristic-two
argument of 15.4.20, printed p.1164.
-/

@[expose] public section

open Subgroup Representation CFSG.Quasithin.ChapterC
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.AlternatingFiveTransport
variable {H : Type*} [Group H] [Finite H]
variable (L : Subgroup H) (hL : L.IsSubnormal)

/-- Inclusion descends through the two-cores of a subnormal subgroup. -/
noncomputable def coreEmbedding : (L ⧸ pCore 2 L) →* (H ⧸ pCore 2 H) :=
  QuotientGroup.map _ _ L.subtype (pCore_subnormal_eq_comap 2 hL).le

/-- Subnormal core restriction identifies the entire kernel. -/
theorem coreEmbedding_injective : Function.Injective (coreEmbedding L hL) := by
  apply (coreEmbedding L hL).ker_eq_bot_iff.mp
  rw [coreEmbedding, QuotientGroup.ker_map, ← pCore_subnormal_eq_comap 2 hL]
  exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])

variable {A M : Type*} [Group A] [AddCommGroup M]
variable {ρ : A →* MulAut (Multiplicative M)} (m : BlockModuleModel L ρ)

/-- Embed the model actor using its actual block quotient isomorphism. -/
noncomputable def embedding : A →* (H ⧸ pCore 2 H) :=
  (coreEmbedding L hL).comp m.quotientIso.symm.toMonoidHom

/-- The model actor embeds faithfully in the ambient core quotient. -/
theorem embedding_injective : Function.Injective (embedding L hL m) :=
  (coreEmbedding_injective L hL).comp m.quotientIso.symm.injective

/-- An element of L represents the same ambient quotient element after transport. -/
@[simp] theorem embedding_mk (l : L) :
    embedding L hL m (m.quotientIso (QuotientGroup.mk' _ l)) =
      QuotientGroup.mk' (pCore 2 H) (l : H) := by
  simp [embedding, coreEmbedding]

variable (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
variable (hc : centralizer (V : Set H) = pCore 2 H)

/-- The invariant subspace V ∩ U(L), with U(L) included in the ambient group. -/
noncomputable def intersection : Subrepresentation ((coreAction V hc).comp (embedding L hL m)) where
  toSubmodule := AddSubgroup.toZModSubmodule 2
    (((blockU L).map L.subtype).comap V.subtype).toAddSubgroup
  apply_mem_toSubmodule g v hv := by
    obtain ⟨l, rfl⟩ := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _) g
    change ((coreAction V hc
      (embedding L hL m (m.quotientIso (QuotientGroup.mk' _ l))) v).toMul : H) ∈
        (blockU L).map L.subtype
    rw [embedding_mk, coreAction_apply]
    obtain ⟨u, hu, he⟩ := hv
    exact ⟨l * u * l⁻¹, (blockU_normal L).conj_mem u hu l, by
      change (u : H) = (v.toMul : H) at he
      change (l : H) * (u : H) * (l : H)⁻¹ = _
      rw [he]⟩

/-- Regard an element of the intersection as an element of the intrinsic U(L). -/
noncomputable def intersectionLift (w : (intersection L hL m V hc).toSubmodule) : blockU L :=
  ⟨⟨w.val.toMul, map_subtype_le _ w.property⟩, by
    obtain ⟨u, hu, he⟩ := w.property
    have he' : u = (⟨w.val.toMul, map_subtype_le _ w.property⟩ : L) := Subtype.ext he
    exact he' ▸ hu⟩

/-- The intersection inclusion preserves the underlying ambient element. -/
@[simp] theorem intersectionLift_val (w : (intersection L hL m V hc).toSubmodule) :
    ((intersectionLift L hL m V hc w : L) : H) = w.val.toMul := rfl

variable [Module (ZMod 2) M]

/-- Restrict the actual block quotient map and then apply its module isomorphism. -/
noncomputable def sectionMap : (intersection L hL m V hc).toSubmodule →ₗ[ZMod 2] M :=
  AddMonoidHom.toZModLinearMap 2 {
    toFun w := Multiplicative.toAdd (m.moduleIso (QuotientGroup.mk' _
      (intersectionLift L hL m V hc w)))
    map_zero' := by
      have he : intersectionLift L hL m V hc 0 = 1 := rfl
      simp only [he, map_one]
      rfl
    map_add' a b := by
      have he : intersectionLift L hL m V hc (a + b) =
          intersectionLift L hL m V hc a * intersectionLift L hL m V hc b := rfl
      simp only [he, map_mul]
      rfl }

omit [Module (ZMod 2) M] in
/-- The inclusion intertwines the quotient action with literal conjugation in L. -/
theorem intersectionLift_action (l : L) (w : (intersection L hL m V hc).toSubmodule) :
    intersectionLift L hL m V hc ((intersection L hL m V hc).toRepresentation
      (m.quotientIso (QuotientGroup.mk' _ l)) w) =
      blockConjugate L l (intersectionLift L hL m V hc w) := by
  apply Subtype.ext
  apply Subtype.ext
  change ((coreAction V hc
    (embedding L hL m (m.quotientIso (QuotientGroup.mk' _ l))) w.val).toMul : H) = _
  rw [embedding_mk, coreAction_apply]
  rfl

/-- Equivariance is inherited from the defining intertwining of the block model. -/
theorem sectionMap_equivariant (π : Representation (ZMod 2) A M)
    (hρ : ∀ g v, Multiplicative.toAdd (ρ g v) = π g (Multiplicative.toAdd v))
    (g : A) (w : (intersection L hL m V hc).toSubmodule) :
    sectionMap L hL m V hc ((intersection L hL m V hc).toRepresentation g w) =
      π g (sectionMap L hL m V hc w) := by
  obtain ⟨l, rfl⟩ := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _) g
  change Multiplicative.toAdd (m.moduleIso (QuotientGroup.mk' _
    (intersectionLift L hL m V hc ((intersection L hL m V hc).toRepresentation _ w)))) = _
  dsimp only [Function.comp_apply]
  rw [intersectionLift_action, m.intertwining, hρ]
  rfl

/-- The restricted quotient kernel lies in C_U(L)(L), so it is fixed. -/
theorem sectionMap_kernel_fixed (g : A) (w : (intersection L hL m V hc).toSubmodule)
    (hw : sectionMap L hL m V hc w = 0) :
    (intersection L hL m V hc).toRepresentation g w = w := by
  have hq : QuotientGroup.mk' (blockFixed L) (intersectionLift L hL m V hc w) = 1 := by
    apply m.moduleIso.injective
    apply Multiplicative.toAdd.injective
    rw [map_one]
    exact hw
  have hz : (intersectionLift L hL m V hc w : L) ∈ center L :=
    (QuotientGroup.eq_one_iff (N := blockFixed L) (intersectionLift L hL m V hc w)).mp hq
  obtain ⟨l, rfl⟩ := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _) g
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((coreAction V hc
    (embedding L hL m (m.quotientIso (QuotientGroup.mk' _ l))) w.val).toMul : H) = _
  rw [embedding_mk, coreAction_apply]
  have he := congrArg (fun x : L => (x : H)) (mem_center_iff.mp hz l)
  change (l : H) * (w.val.toMul : H) = (w.val.toMul : H) * (l : H) at he
  rw [he, mul_inv_cancel_right]

omit [Module (ZMod 2) M] in
/-- Subnormal two-perfectness puts every displacement in V ∩ U(L). -/
theorem quotient_trivial (hp : IsPPerfect 2 L) (g : A) (v : Additive V) :
    coreAction V hc (embedding L hL m g) v - v ∈ intersection L hL m V hc := by
  obtain ⟨l, rfl⟩ := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _) g
  change (((coreAction V hc
    (embedding L hL m (m.quotientIso (QuotientGroup.mk' _ l))) v - v).toMul) : H) ∈
      (blockU L).map L.subtype
  simp only [toMul_sub, div_eq_mul_inv]
  change ((coreAction V hc
    (embedding L hL m (m.quotientIso (QuotientGroup.mk' _ l))) v).toMul : H) *
      (v.toMul : H)⁻¹ ∈ (blockU L).map L.subtype
  rw [embedding_mk, coreAction_apply]
  have hn : L ≤ normalizer (V : Set H) := by rw [normalizer_eq_top]; exact le_top
  have hh := commutator_le_core_commutator_of_isSubnormal L V hL hp
    (IsElementaryAbelian.isPGroup 2 V) hn
  apply hh
  rw [commutator_comm V L]
  exact commutator_mem_commutator l.property v.toMul.property

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.AlternatingFiveTransport

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve
open AlternatingFiveTransport
variable {H : Type*} [Group H] [Finite H]

/-- The actual block model, restricted to its intersection with V, gives the
central section excluded by the Sylow seed centralizer. -/
theorem not_alternatingFive_model
    (V Z : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (hc : centralizer (V : Set H) = pCore 2 H) (hZV : Z ≤ V)
    (P : Sylow 2 H) (hCZ : centralizer (Z : Set H) = (P : Subgroup H))
    (L : Subgroup H) (hL : L.IsSubnormal) (hp : IsPPerfect 2 L)
    (hm : IsLinearBlockModel L ((BinaryPermutation.naturalRepresentation (Fin 5)).comp
      (alternatingGroup (Fin 5)).subtype)) : False := by
  obtain ⟨ρ, ⟨m⟩, hρ⟩ := hm
  exact not_alternatingFive_centralSection V Z hc hZV P hCZ
    (embedding L hL m) (embedding_injective L hL m)
    (intersection L hL m V hc) (sectionMap L hL m V hc)
    (sectionMap_equivariant L hL m V hc _ hρ)
    (sectionMap_kernel_fixed L hL m V hc) (quotient_trivial L hL m V hc hp)

/-- A subnormal alternating-five block cannot occur with the given faithful
core-quotient module and actual Sylow seed centralizer. -/
theorem not_alternatingFive_block
    (V Z : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (hc : centralizer (V : Set H) = pCore 2 H) (hZV : Z ≤ V)
    (P : Sylow 2 H) (hCZ : centralizer (Z : Set H) = (P : Subgroup H))
    (L : Subgroup H) (hL : L.IsSubnormal) (hb : IsAlternatingBlock L 5) : False :=
  not_alternatingFive_model V Z hc hZV P hCZ L hL hb.2.1.twoPerfect hb.2.2

variable {G : Type*} [Group G] [Finite G]

/-- Relative subnormality is sufficient. Transport the intrinsic block model
along the actual equivalence from K₁ to its subgroup inside H. -/
theorem not_alternatingFive_relativeBlock (H K₁ : Subgroup G) (hKH : K₁ ≤ H)
    (V Z : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (hc : centralizer (V : Set H) = pCore 2 H) (hZV : Z ≤ V)
    (P : Sylow 2 H) (hCZ : centralizer (Z : Set H) = (P : Subgroup H))
    (hsub : (K₁.subgroupOf H).IsSubnormal) (hb : IsAlternatingBlock K₁ 5) : False := by
  let e := (subgroupOfEquivOfLe hKH).symm
  have hp : IsPPerfect 2 (K₁.subgroupOf H) :=
    hb.2.1.twoPerfect.of_surjective e.toMonoidHom e.surjective
  obtain ⟨ρ, ⟨m⟩, hρ⟩ := hb.2.2
  exact not_alternatingFive_model V Z hc hZV P hCZ (K₁.subgroupOf H) hsub hp
    ⟨ρ, ⟨BlockEndgame.transportModel e m⟩, hρ⟩

/-- The A₅-block branch on printed p.1164 is excluded using the module and
seed already constructed from the source geometry. -/
theorem Input.not_alternatingFive_block
    {d : Source.Geometry G} {i j : Bool} {H U K : Subgroup G}
    (h : Input d i j H U K) (K₁ : Subgroup G) (hKH : K₁ ≤ H)
    (hsub : (K₁.subgroupOf H).IsSubnormal) (hb : IsAlternatingBlock K₁ 5) : False := by
  let V := TwoFactors.FFBranch.moduleClosure (d.Z.subgroupOf H)
  let := h.module_properties.1
  exact not_alternatingFive_relativeBlock H K₁ hKH V (d.Z.subgroupOf H)
    h.module_properties.2.2.2 (fun _ hz => le_normalClosure hz)
    h.placed.sylow h.seed_inputs.2.2.1 hsub hb

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve
