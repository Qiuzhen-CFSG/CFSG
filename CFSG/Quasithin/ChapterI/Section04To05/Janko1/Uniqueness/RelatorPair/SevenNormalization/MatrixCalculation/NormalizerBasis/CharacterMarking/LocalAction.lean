module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.NormalizerBasis.CharacterFrame
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.LocalCentralizers
public import Mathlib.GroupTheory.FiniteAbelian.Duality

/-!
# The dual action of the marked Sylow normalizer

The source Sylow eight is self-centralizing, so its disjoint complement acts
faithfully. Finite abelian duality over F₁₁ transfers this faithfulness to the
characters. Inverse-conjugation pullback preserves the literal relation
`u * y * u⁻¹ = y²`, including either orientation of y. Evaluation at the marked
involution has kernel of order four.

These are the finite-group inputs to the basis normalization in Gorenstein,
*Finite Groups*, §16.6, pp.482–483, preceding (6.1)–(6.2). No representation,
recognition theorem, or ambient order calculation enters this argument.
-/

open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation.CharacterMarking

variable {G : Type*} [Group G] [Finite G] {h : Janko1CentralizerData G}

/-- Characters of the literal source Sylow subgroup over F₁₁. -/
public abbrev Character (h : Janko1CentralizerData G) := h.sylow →* (ZMod 11)ˣ

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private instance enoughTwoRoots : HasEnoughRootsOfUnity (ZMod 11) 2 where
  prim := ⟨-1, IsPrimitiveRoot.neg_one 11 (by decide)⟩
  cyc := rootsOfUnity.isCyclic (ZMod 11) 2

/-- Finite abelian duality supplies exactly eight F₁₁-valued characters. -/
public theorem character_card (h : Janko1CentralizerData G) : Nat.card (Character h) = 8 := by
  let := h.sylow_elementaryAbelian
  let : HasEnoughRootsOfUnity (ZMod 11) (Monoid.exponent h.sylow) :=
    HasEnoughRootsOfUnity.of_dvd (ZMod 11) (IsElementaryAbelian.exponent_dvd_p 2 h.sylow)
  exact (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity h.sylow (ZMod 11)).trans h.sylow_card

private theorem characters_separate (s t : h.sylow) (hst : ∀ χ : Character h, χ s = χ t) : s = t := by
  let := h.sylow_elementaryAbelian
  let : HasEnoughRootsOfUnity (ZMod 11) (Monoid.exponent h.sylow) :=
    HasEnoughRootsOfUnity.of_dvd (ZMod 11) (IsElementaryAbelian.exponent_dvd_p 2 h.sylow)
  exact (CommGroup.forall_apply_eq_apply_iff h.sylow).mp hst

private def dualAction : MulAut h.sylow →* MulAut (Character h) where
  toFun e := e.monoidHomCongrLeft
  map_one' := by ext χ s; rfl
  map_mul' a b := by ext χ s; rfl

private theorem dualAction_injective : Function.Injective (dualAction (h := h)) := by
  intro a b hab
  have he : a.symm = b.symm := by
    apply MulEquiv.ext
    intro s
    apply characters_separate
    intro χ
    exact congrArg (fun e : MulAut (Character h) => e χ s) hab
  exact congrArg MulEquiv.symm he

/-- Pullback by inverse conjugation by the chosen orientation of y. -/
public def characterY (D : NormalizerFrame h) (reverse : Bool) : MulAut (Character h) :=
  dualAction (sylowY D reverse)

/-- Pullback by inverse conjugation by the marked cubic element. -/
public def characterU (D : NormalizerFrame h) : MulAut (Character h) := dualAction (sylowU D)

public theorem characterY_apply (D : NormalizerFrame h) (reverse : Bool)
    (χ : Character h) (s : h.sylow) :
    characterY D reverse χ s = χ ((sylowY D reverse).symm s) := by rfl

public theorem characterU_apply (D : NormalizerFrame h) (χ : Character h) (s : h.sylow) :
    characterU D χ s = χ ((sylowU D).symm s) := by rfl

private theorem sylowY_pow (D : NormalizerFrame h) (reverse : Bool) : sylowY D reverse ^ 7 = 1 := by
  rw [sylowY, ← map_pow]
  have hh : (⟨orientedY D reverse, D.H_le (orientedY_mem D reverse)⟩ :
      (Subgroup.normalizer (h.sylow : Set G))) ^ 7 = 1 := Subtype.ext (orientedY_pow_seven D reverse)
  rw [hh, map_one]

private theorem sylowY_ne_one (D : NormalizerFrame h) (reverse : Bool) : sylowY D reverse ≠ 1 := by
  intro he
  have hk : (⟨orientedY D reverse, D.H_le (orientedY_mem D reverse)⟩ :
      (Subgroup.normalizer (h.sylow : Set G))) ∈ (h.sylow : Subgroup G).normalizerMonoidHom.ker := he
  rw [Subgroup.normalizerMonoidHom_ker] at hk
  have hs : orientedY D reverse ∈ (h.sylow : Subgroup G) := by
    have hc : orientedY D reverse ∈ Subgroup.centralizer (h.sylow : Set G) := hk
    rwa [h.sylow_centralizer_eq] at hc
  have hy1 : orientedY D reverse = 1 :=
    Subgroup.disjoint_def.mp D.disjoint (orientedY_mem D reverse) hs
  have hy : D.y ≠ 1 := by
    intro hh
    have hy := D.order_y
    rw [hh, orderOf_one] at hy
    omega
  cases reverse <;> simp_all [orientedY]

public theorem characterY_pow (D : NormalizerFrame h) (reverse : Bool) : characterY D reverse ^ 7 = 1 := by
  rw [characterY, ← map_pow, sylowY_pow, map_one]

/-- The seven-element cannot act trivially: its complement meets the
self-centralizing Sylow subgroup trivially. Characters detect this action. -/
public theorem characterY_ne_one (D : NormalizerFrame h) (reverse : Bool) : characterY D reverse ≠ 1 := by
  intro he
  apply sylowY_ne_one D reverse
  apply dualAction_injective
  simpa [characterY] using he

public theorem characterU_pow (D : NormalizerFrame h) : characterU D ^ 3 = 1 := by
  have hu : D.u ^ 3 = 1 := D.order_u ▸ pow_orderOf_eq_one D.u
  have hs : sylowU D ^ 3 = 1 := by
    rw [sylowU, ← map_pow]
    rw [show (⟨D.u, D.H_le D.u_mem⟩ : (Subgroup.normalizer (h.sylow : Set G))) ^ 3 = 1 from
      Subtype.ext hu, map_one]
  rw [characterU, ← map_pow, hs, map_one]

/-- Inverse pullback is a left action and retains the source squaring relation. -/
public theorem character_action (D : NormalizerFrame h) (reverse : Bool) :
    characterU D * characterY D reverse = characterY D reverse ^ 2 * characterU D := by
  have hs : sylowU D * sylowY D reverse = sylowY D reverse ^ 2 * sylowU D := by
    dsimp [sylowU, sylowY]
    rw [← map_mul, ← map_pow, ← map_mul]
    congr 1
    apply Subtype.ext
    change D.u * orientedY D reverse = orientedY D reverse ^ 2 * D.u
    exact (mul_inv_eq_iff_eq_mul).mp (orientedY_action D reverse)
  simpa only [characterU, characterY, map_mul, map_pow] using congrArg dualAction hs

public theorem characterY_reverse (D : NormalizerFrame h) : characterY D true = (characterY D false)⁻¹ := by
  have hs : sylowY D true = (sylowY D false)⁻¹ := by
    dsimp [sylowY, orientedY]
    rw [← map_inv]
    rfl
  rw [characterY, hs, map_inv, characterY]

/-- The literal fixed-subgroup identity makes evaluation at x cubic-invariant. -/
public theorem characterU_x (D : NormalizerFrame h) (χ : Character h) :
    characterU D χ ⟨D.x, D.x_mem⟩ = χ ⟨D.x, D.x_mem⟩ := by
  have hx : D.x ∈ Subgroup.centralizer (Subgroup.zpowers D.u : Set G) := by
    have : D.x ∈ (h.sylow : Subgroup G) ⊓ Subgroup.centralizer (Subgroup.zpowers D.u : Set G) := by
      rw [D.fixed]
      exact Subgroup.mem_zpowers D.x
    exact this.2
  have hux : D.u * D.x = D.x * D.u :=
    (Subgroup.mem_centralizer_iff.mp hx) D.u (Subgroup.mem_zpowers D.u)
  have hfix : sylowU D ⟨D.x, D.x_mem⟩ = ⟨D.x, D.x_mem⟩ := by
    apply Subtype.ext
    change D.u * D.x * D.u⁻¹ = D.x
    rw [hux, mul_inv_cancel_right]
  change χ ((sylowU D).symm ⟨D.x, D.x_mem⟩) = χ ⟨D.x, D.x_mem⟩
  rw [(sylowU D).symm_apply_eq.mpr hfix.symm]

/-- Evaluation at the marked involution has four characters in its kernel,
including the trivial character. Its image has order two by dual separation. -/
public theorem evaluation_ker_card (D : NormalizerFrame h) :
    Nat.card (MonoidHom.eval ⟨D.x, D.x_mem⟩ : Character h →* (ZMod 11)ˣ).ker = 4 := by
  let e : Character h →* (ZMod 11)ˣ := MonoidHom.eval ⟨D.x, D.x_mem⟩
  have hd8 : Nat.card e.range ∣ 8 := character_card h ▸ Subgroup.card_range_dvd e
  have hd10 : Nat.card e.range ∣ 10 := by
    have hc : Nat.card (ZMod 11)ˣ = 10 := by rw [Nat.card_units, Nat.card_zmod]
    simpa only [hc] using e.range.card_subgroup_dvd_card
  have hd2 : Nat.card e.range ∣ 2 := Nat.dvd_gcd hd8 hd10
  have hn : Nat.card e.range ≠ 1 := by
    intro hh
    have ht : e.range = ⊥ := Subgroup.card_eq_one.mp hh
    have hx1 : (⟨D.x, D.x_mem⟩ : h.sylow) = 1 := by
      apply characters_separate
      intro χ
      rw [map_one]
      have hm : e χ ∈ e.range := ⟨χ, rfl⟩
      rwa [ht] at hm
    have hhx : D.x = 1 := congrArg Subtype.val hx1
    have ho := D.order_x
    rw [hhx, orderOf_one] at ho
    omega
  have he2 : Nat.card e.range = 2 := ((Nat.dvd_prime Nat.prime_two).mp hd2).resolve_left hn
  have hc := e.ker.card_mul_index
  rw [Subgroup.index_ker, he2, character_card] at hc
  change Nat.card e.ker = 4
  omega

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation.CharacterMarking
