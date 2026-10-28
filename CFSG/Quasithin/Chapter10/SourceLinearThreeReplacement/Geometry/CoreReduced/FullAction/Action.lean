module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction.Orbit
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.BinaryTransvectionGroups.Basic

/-!
# The literal full action and its moved-factor roots

Linearize conjugation by G_z on Additive V_z. Its kernel is exactly the
centralizer in G_z, so the original reducedness premise transports to its
full image. The natural section gives a moved factor of order at least eight.
With kernel the involution line, its image has order at least four.
The original commutator bound places that image
in the root group centered at a, including the actual displacement formula.

These are conditional calculations, not an assertion of the outstanding
natural-module fixed-subgroup calculation in 10.2.11(3).
Source: Aschbacher--Smith, printed p.754.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory BinaryLinear BinaryTransvectionGroups
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G}

variable (c : Configuration s a b)
variable [IsElementaryAbelian 2 (centralizerModule a b)]

noncomputable def action (_c : Configuration s a b) : centralizer ({a*b} : Set G) →*
    BinaryLinear.GL (Additive (centralizerModule a b)) :=
  let lin : MulAut (centralizerModule a b) →* BinaryLinear.GL (Additive (centralizerModule a b)) :=
    { toFun := fun e => { e.toAdditive with map_smul' := ZMod.map_smul e.toAdditive }
      map_one' := by ext; rfl
      map_mul' := by intros; ext; rfl }
  lin.comp ((centralizerModule a b).normalizerMonoidHom.comp
    (inclusion (le_normalizer_conjugateSpanBy _ _)))

theorem action_apply (g : centralizer ({a*b} : Set G))
    (w : Additive (centralizerModule a b)) :
    ((action c g w).toMul : G) = (g:G) * (w.toMul:G) * (g:G)⁻¹ := rfl

theorem action_ker : (action c).ker =
    centralizer (((centralizerModule a b).subgroupOf (centralizer ({a*b} : Set G))) :
      Set (centralizer ({a*b} : Set G))) := by
  ext g
  change action c g = 1 ↔ _
  constructor
  · intro hg w hw
    have hh := congrArg (fun e => ((e (Additive.ofMul ⟨w.val,hw⟩)).toMul:G)) hg
    change (g:G)*(w:G)*(g:G)⁻¹ = (w:G) at hh
    exact Subtype.ext ((mul_inv_eq_iff_eq_mul.mp hh).symm)
  · intro hg
    ext w
    have hh := congrArg Subtype.val (hg ⟨w.toMul,c.span_le w.toMul.property⟩ w.toMul.property)
    change (w.toMul:G)*(g:G) = (g:G)*(w.toMul:G) at hh
    change (g:G)*(w.toMul:G)*(g:G)⁻¹ = (w.toMul:G)
    rw [← hh,mul_inv_cancel_right]

theorem action_twoCore
    (hr : IsPReduced 2 ((centralizerModule a b).subgroupOf (centralizer ({a*b} : Set G)))) :
    pCore 2 (action c).range = ⊥ := by
  let := hr.normal
  let e := (QuotientGroup.quotientMulEquivOfEq (action_ker c).symm).trans
    (QuotientGroup.quotientKerEquivRange (action c))
  rw [← pCore_map_iso 2 e, hr.quotient_pCore_eq_bot, Subgroup.map_bot]

noncomputable def firstVector : Additive (centralizerModule a b) :=
  Additive.ofMul ⟨a,le_conjugateSpanBy _ _ (mem_sup_left (mem_zpowers a))⟩

noncomputable def movedAction : (⁅D.fullModule,L⁆ : Subgroup G) →*
    BinaryLinear.GL (Additive (centralizerModule a b)) :=
  (action c).comp (inclusion ((survivor_moved_le s).trans c.full_le))

include c in
omit [IsElementaryAbelian 2 (centralizerModule a b)] in
theorem first_order : orderOf a = 2 := by
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  exact orderOf_eq_prime_iff.mpr
    ⟨elemPow_eq_one_of_isElementaryAbelian a (survivor_moved_le s c.first_mem),c.first_ne⟩

theorem movedAction_card_ge_four
    (hk : ⁅D.fullModule,L⁆ ⊓ centralizer (centralizerModule a b : Set G) = zpowers a) :
    4 ≤ Nat.card (movedAction c).range := by
  have hc := s.natural.card_section
  simp only [Nat.card_fun, Nat.card_fin, Nat.card_zmod] at hc
  norm_num at hc
  change Nat.card (⁅D.fullModule,L⁆ : Subgroup G) =
    8 * Nat.card (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) : Subgroup G) at hc
  have hn : 0 < Nat.card (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) : Subgroup G) :=
    Nat.card_pos
  have hker : (movedAction c).ker = (zpowers a).subgroupOf ⁅D.fullModule,L⁆ := by
    ext v
    change action c (inclusion ((survivor_moved_le s).trans c.full_le) v) = 1 ↔ _
    rw [← MonoidHom.mem_ker, action_ker c]
    change (∀ w : centralizer ({a*b} : Set G), (w:G) ∈ centralizerModule a b →
      w * inclusion ((survivor_moved_le s).trans c.full_le) v =
        inclusion ((survivor_moved_le s).trans c.full_le) v * w) ↔ _
    constructor
    · intro hv
      have hh : (v:G) ∈ ⁅D.fullModule,L⁆ ⊓ centralizer (centralizerModule a b : Set G) := by
        refine ⟨v.property,?_⟩
        intro w hw
        exact congrArg Subtype.val (hv ⟨w,c.span_le hw⟩ hw)
      exact hk ▸ hh
    · intro hv w hw
      have hh : (v:G) ∈ ⁅D.fullModule,L⁆ ⊓ centralizer (centralizerModule a b : Set G) :=
        hk.symm ▸ hv
      exact Subtype.ext (hh.2 w hw)
  have hcount := (movedAction c).ker.card_mul_index
  rw [index_ker, hker, Nat.card_congr
    (subgroupOfEquivOfLe (zpowers_le.mpr c.first_mem)).toEquiv,
    Nat.card_zpowers, first_order c] at hcount
  omega

theorem movedAction_le_roots
    (hd : ⁅⁅D.fullModule,L⁆,centralizerModule a b⁆ ≤ zpowers a) :
    (movedAction c).range ≤ rootGroup (action c).range (firstVector (a := a) (b := b)) := by
  rintro f ⟨v,rfl⟩
  refine ⟨⟨inclusion ((survivor_moved_le s).trans c.full_le) v,rfl⟩,?_,?_⟩
  · intro w hw
    rcases (mem_centerLine_iff _ _).mp hw with rfl | rfl
    · exact map_zero _
    · apply Subtype.ext
      let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
      have hh := congrArg Subtype.val (mul_comm
        (⟨v,survivor_moved_le s v.property⟩ : D.fullModule)
        ⟨a,survivor_moved_le s c.first_mem⟩)
      change (v:G)*a = a*(v:G) at hh
      change (v:G)*a*(v:G)⁻¹=a
      rw [hh,mul_inv_cancel_right]
  · intro w
    have hh := hd (commutator_mem_commutator v.property w.toMul.property)
    have hp : ⁅(v:G),(w.toMul:G)⁆ = 1 ∨ ⁅(v:G),(w.toMul:G)⁆ = a := by
      classical
      rw [mem_zpowers_iff_mem_range_orderOf, first_order c] at hh
      obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hh
      have hn2 : n < 2 := Finset.mem_range.mp hn
      interval_cases n <;> simp_all
    apply (mem_centerLine_iff _ _).mpr
    rcases hp with hp | hp
    · apply Or.inl
      apply Subtype.ext
      change ((v:G)*(w.toMul:G)*(v:G)⁻¹) / (w.toMul:G) = 1
      simpa only [commutatorElement_def,div_eq_mul_inv] using hp
    · apply Or.inr
      apply Subtype.ext
      change ((v:G)*(w.toMul:G)*(v:G)⁻¹) / (w.toMul:G) = a
      simpa only [commutatorElement_def,div_eq_mul_inv] using hp

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction
