module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.ClassificationModels.Families
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!+# Inputs and local reductions for the sporadic exclusions

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.1.5(3)(f), printed p.502, and the proof of 2.3.9(7), printed p.526.

The source input identifies the quotient by the actual two-core and specifies
the literal inner action on the component. No trivial-center or splitting
assumption is imposed. The component's Sylow subgroup is obtained by restriction
of the supplied Sylow subgroup along relative subnormality. In particular the
involution action fixes this Sylow subgroup pointwise; an additional assumption
to this effect is unnecessary.

For the local calculation, subgroups of C_G(z) are already inside M. Thus a
family of local overgroups, together with C_G(z), suffices for generation. Each
member still needs an actual block obstruction. `CentralizerBlockCover` is a
contract for these missing calculations, not a sporadic classification theorem.
No inhabitant for any of the seven excluded models is asserted in this module.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement

open Subgroup ChapterC Theory.GroupTheory ClassificationModels

variable {G : Type*} [Group G]

/-- The seven sporadic cases discarded on p.526. This predicate is used only
with the actual quotient isomorphism in `SporadicQuotientInput`. -/
def IsDiscardedSporadic : SporadicName → Prop
  | .m12 | .m24 | .j2 | .j4 | .hs | .he | .ru => True
  | .m11 | .m22 | .m23 | .j3 => False

/-- The quotient and action in 1.1.5(3)(f). Quasisimplicity, nontriviality and
order two of the action, and its fixation of a component Sylow subgroup follow
from `LocalSetup`. In particular `action` is not an unrelated family label. -/
structure SporadicQuotientInput (L : Subgroup G) (z : G) (name : SporadicName) where
  quotientIso : (L ⧸ pCore 2 L) ≃* name.Carrier
  action : MulAut L
  conjugation : ∀ x : L, (action x : G) = z * (x : G) * z⁻¹
  inner : action ∈ (MulAut.conj (G := L)).range

/-- Relative component quasisimplicity gives intrinsic quasisimplicity of L. -/
theorem LocalSetup.quasisimple {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) : IsQuasisimple L := by
  let := h.component.2
  exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.component_le)

/-- Restrict the actual supplied Sylow subgroup to the subnormal component. -/
theorem LocalSetup.exists_component_sylow {H L M : Subgroup G}
    {S : Sylow 2 H} {z : G} (h : LocalSetup H L M S z) :
    ∃ R : Sylow 2 L, (R : Subgroup L).map L.subtype =
      L ⊓ (S : Subgroup H).map H.subtype := by
  let := h.finite
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_subnormal (L.subgroupOf H) h.component.1
  let e := subgroupOfEquivOfLe h.component_le
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((R : Subgroup (L.subgroupOf H)).map e.toMonoidHom).map L.subtype = _
  rw [hR]
  ext x
  constructor
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w.property, ⟨(w : H), hw, rfl⟩⟩
  · rintro ⟨hx, y, hy, rfl⟩
    exact ⟨⟨y, hx⟩, ⟨⟨y, hx⟩, hy, rfl⟩, rfl⟩

/-- The actual conjugation action fixes the component Sylow subgroup
pointwise, including its central two-kernel. -/
theorem LocalSetup.exists_fixed_component_sylow {H L M : Subgroup G}
    {S : Sylow 2 H} {z : G} (h : LocalSetup H L M S z) (α : MulAut L)
    (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹) :
    ∃ R : Sylow 2 L, (R : Subgroup L).map L.subtype =
      L ⊓ (S : Subgroup H).map H.subtype ∧ ∀ r ∈ (R : Subgroup L), α r = r := by
  obtain ⟨R, hR⟩ := h.exists_component_sylow
  refine ⟨R, hR, ?_⟩
  intro r hr
  have hm : (r : G) ∈ (R : Subgroup L).map L.subtype := ⟨r, hr, rfl⟩
  rw [hR] at hm
  apply Subtype.ext
  rw [hα, ← h.central (r : G) hm.2, mul_inv_cancel_right]

/-- Nontriviality comes from L not contained in M, rather than an extra
assumption about the inner automorphism. -/
theorem LocalSetup.action_order {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (α : MulAut L)
    (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹) : orderOf α = 2 :=
  orderOf_eq_prime (h.action_sq α hα) (h.action_ne_one α hα)

/-- The inner action fixes the whole center of L, so its embedded center
lies in M. This does not discard that center from any local calculation. -/
theorem LocalSetup.center_le_of_inner_action {H L M : Subgroup G}
    {S : Sylow 2 H} {z : G} (h : LocalSetup H L M S z) (α : MulAut L)
    (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    (center L).map L.subtype ≤ M := by
  obtain ⟨t, ht⟩ := hinner
  rintro x ⟨c, hc, rfl⟩
  apply h.centralizer_le
  apply mem_centralizer_singleton_iff.mpr
  have hfix : α c = c := by
    rw [← ht]
    change t * c * t⁻¹ = c
    rw [mem_center_iff.mp hc t, mul_inv_cancel_right]
  have he := hα c
  rw [hfix] at he
  exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm

/-- A suitable local overgroup with no escaping allowed block is inside M. -/
theorem le_of_local_blockObstruction {L M S K : Subgroup G}
    (hblocks : LocalBlockGeneration L M S) (hK : K ≤ L ⊔ S)
    (he : K ∈ Chapter1.HeOver G (S : Set G))
    (ho : BlockObstruction M S K) : K ≤ M := by
  by_contra hn
  obtain ⟨d⟩ := hblocks K hK he hn
  obtain ⟨B, hb, hm, hc⟩ := d.exists_escapingBlock hn
  exact hm (ho B hb hc)

/-- Model-local calculations still to be constructed. Each member contains
the given S, has nontrivial self-centralizing two-core, and lies in LS.
The family may have one, two, or more members. -/
structure CentralizerBlockCover (L M S : Subgroup G) (z : G) where
  locals : Set (Subgroup G)
  generated : L ≤ centralizer ({z} : Set G) ⊔ sSup locals
  within : ∀ K ∈ locals, K ≤ L ⊔ S
  even : ∀ K ∈ locals, K ∈ Chapter1.HeOver G (S : Set G)
  obstruction : ∀ K ∈ locals, BlockObstruction M S K

/-- The centralizer requires no additional block calculation. -/
theorem CentralizerBlockCover.le {L M S : Subgroup G} {z : G}
    (c : CentralizerBlockCover L M S z) (hblocks : LocalBlockGeneration L M S)
    (hc : centralizer ({z} : Set G) ≤ M) : L ≤ M := by
  apply c.generated.trans
  refine sup_le hc (sSup_le ?_)
  intro K hK
  exact le_of_local_blockObstruction hblocks (c.within K hK) (c.even K hK)
    (c.obstruction K hK)

/-- Conditional assembly only: the model-specific cover must first be
constructed from the actual quotient and action. -/
theorem LocalSetup.false_of_centralizerBlockCover {H L M : Subgroup G}
    {S : Sylow 2 H} {z : G} (h : LocalSetup H L M S z)
    (c : CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z) : False :=
  h.outside (c.le h.blocks h.centralizer_le)

/-- One possible concrete subgroup/module calculation: every subnormal
short subgroup moved by J(S) either centralizes z, has central two-core, or
has an odd-dimensional block module. The last two cases cannot be chi-zero
blocks. The subnormality is in K, never in the ambient group. -/
theorem blockObstruction_of_core_or_module {M S K : Subgroup G} {z : G}
    (hc : centralizer ({z} : Set G) ≤ M)
    (hcalc : ∀ B : Subgroup K, B.IsSubnormal → IsShort B →
      B.map K.subtype = ⁅B.map K.subtype, Stellmacher.elementaryAbelianMaxJ S⁆ →
      B.map K.subtype ≤ centralizer ({z} : Set G) ∨
        pCore 2 B ≤ center B ∨
          ∃ d : ℕ, Nat.card (BlockModule B) = 2 ^ (2 * d + 1)) :
    BlockObstruction M S K := by
  intro B hb hm
  rcases hcalc B hb.1.subnormal hb.1.short hm with hfix | hcore | ⟨d, hd⟩
  · exact hfix.trans hc
  · exact (hb.1.short.blockU_ne_bot
      (commutator_top_right_eq_bot_iff_le_center.mpr hcore)).elim
  · exact (not_chiZero_of_odd_module_card d hd hb.2).elim

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
