module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.Residual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.SourceCases.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.Intrinsic
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# A natural quotient suffices for the original residual argument

The actual quotient Q/C_Q(L) carries one or two natural modules. Its
residual conjugation action commutes with L because [Y_C,L] lies in Q.
An order-four fixed subgroup survives the kernel of order at most two,
so the natural multiplicity calculation kills this quotient action.
The residual fixes the small kernel, and two-perfectness then kills the
inverse-displacement homomorphisms into that kernel. Thus Y_C centralizes
Q and L without requiring the central-omega clause of source case five.

Source: Aschbacher–Smith C.1.34(1),(2),(5), pp.136–137, and 15.3.23,
p.1129. The natural-quotient and fixed-kernel producers belong to Chapter C.
-/

public section
open Subgroup Representation
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.AbelianQuotient
open CoreActions Extension.SourceCases
variable {G : Type*} [Group G]
local notation "SL" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
variable {a : ℕ}
local notation "D" => Fin a → Fin 3 → ZMod 2

variable {L : Subgroup G} {e : (L ⧸ pCore 2 L) ≃* SL}
variable (n : LayerModel L (commutatorCore L) (coreFixed L) e (NaturalCopies (ZMod 2) a))

/-- The genuine quotient map followed by the supplied natural-quotient marking. -/
noncomputable def coordinates : commutatorCore L →* Multiplicative D :=
  let _ := n.lower_normal
  n.quotientIso.toMonoidHom.comp (QuotientGroup.mk' _)

/-- Every vector represents an element of the actual commutator core. -/
theorem coordinates_surjective : Function.Surjective (coordinates n) :=
  let _ := n.lower_normal
  n.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The coordinate kernel is precisely the actual fixed subgroup. -/
theorem coordinates_eq_one (q : commutatorCore L) :
    coordinates n q = 1 ↔ (q : G) ∈ coreFixed L := by
  let _ := n.lower_normal
  change n.quotientIso (QuotientGroup.mk' _ q) = 1 ↔ _
  rw [← n.quotientIso.map_one, n.quotientIso.injective.eq_iff]
  exact QuotientGroup.eq_one_iff q

private theorem normalizer_fixed : normalizer (L : Set G) ≤
    normalizer (coreFixed L : Set G) :=
  (le_inf (normalizer_le_normalizer_commutatorCore L)
    (normalizer_le_normalizer_centralizer L)).trans inf_normalizer_le_normalizer_inf

/-- The normalizer acts on the genuine fixed quotient by ambient conjugation. -/
noncomputable def quotientConjugation :
    let _ := n.lower_normal
    normalizer (L : Set G) →*
      MulAut (commutatorCore L ⧸ (coreFixed L).subgroupOf (commutatorCore L)) :=
  Classical.choose (exists_quotient_conjugation_action _ _ _
    (normalizer_le_normalizer_commutatorCore L) normalizer_fixed n.lower_normal)

/-- Conjugation on the fixed quotient, transported to the marked natural copies. -/
noncomputable def quotientAut :
    normalizer (L : Set G) →* MulAut (Multiplicative D) :=
  let _ := n.lower_normal
  (MulAut.congr n.quotientIso).toMonoidHom.comp (quotientConjugation n)

/-- The transported automorphism agrees with conjugation on every representative. -/
theorem quotientAut_apply (x : normalizer (L : Set G))
    (q : commutatorCore L) :
    quotientAut n x (coordinates n q) =
      coordinates n (layerConjugate _ _ (normalizer_le_normalizer_commutatorCore L) x q) := by
  let _ := n.lower_normal
  change n.quotientIso (quotientConjugation n x
    (n.quotientIso.symm (n.quotientIso (QuotientGroup.mk' _ q)))) = _
  rw [n.quotientIso.symm_apply_apply]
  exact congrArg n.quotientIso
    (Classical.choose_spec (exists_quotient_conjugation_action _ _ _
      (normalizer_le_normalizer_commutatorCore L) normalizer_fixed n.lower_normal) x q)

private theorem quotientAut_core (x : normalizer (L : Set G))
    (hx : (x : G) ∈ commutatorCore L) : quotientAut n x = 1 := by
  apply MulEquiv.ext
  intro v
  obtain ⟨q, rfl⟩ := coordinates_surjective n v
  rw [quotientAut_apply]
  let xQ : commutatorCore L := ⟨x, hx⟩
  change coordinates n (xQ * q * xQ⁻¹) = coordinates n q
  simp only [map_mul, map_inv, mul_comm, mul_inv_cancel_right]

/-- Displacement in Q makes the two automorphisms commute on Q/C_Q(L). -/
theorem quotientAut_commute (x y : normalizer (L : Set G))
    (hxy : ⁅(x : G), (y : G)⁆ ∈ commutatorCore L) :
    Commute (quotientAut n x) (quotientAut n y) := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← map_commutatorElement]
  exact quotientAut_core n ⁅x,y⁆ hxy

variable {d : LocalData G} {I : Subgroup G} (c : ComponentWitness d I)
variable {e : (c.L ⧸ pCore 2 c.L) ≃* SL}
variable (n : LayerModel c.L (commutatorCore c.L) (coreFixed c.L) e (NaturalCopies (ZMod 2) a))

/-- The actual section residual normalizes the component. -/
theorem residual_normalizes : YC d c.L ≤ normalizer (c.L : Set G) :=
  (YC_section_action d c.L).1

/-- The binary linear action of the actual residual on the marked quotient. -/
noncomputable def residualAction : Representation (ZMod 2) (YC d c.L) D where
  toFun y := (AddMonoidHom.toMultiplicative.symm
    (quotientAut n (inclusion (residual_normalizes c) y)).toMonoidHom).toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change quotientAut n (inclusion (residual_normalizes c) 1) (Multiplicative.ofAdd v) = _
    rw [map_one, map_one]
    rfl
  map_mul' y z := by
    apply LinearMap.ext
    intro v
    change quotientAut n (inclusion (residual_normalizes c) (y*z)) (Multiplicative.ofAdd v) = _
    rw [map_mul, map_mul]
    rfl

/-- The linear action is the genuine quotient conjugation action. -/
theorem residualAction_apply (y : YC d c.L) (q : commutatorCore c.L) :
    residualAction c n y (coordinates n q).toAdd =
      (coordinates n (layerConjugate _ _ ((residual_normalizes c).trans (normalizer_le_normalizer_commutatorCore c.L)) y q)).toAdd := by
  exact congrArg Multiplicative.toAdd (quotientAut_apply n (inclusion (residual_normalizes c) y) q)

/-- The residual action commutes with the full SL₃(2) action under the given marking. -/
theorem residualAction_commutes (y : YC d c.L) (g : SL) (v : D) :
    residualAction c n y (NaturalCopies (ZMod 2) a g v) =
      NaturalCopies (ZMod 2) a g (residualAction c n y v) := by
  obtain ⟨l, hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 c.L))) g
  change e (QuotientGroup.mk' (pCore 2 c.L) l) = g at hl
  let ny : normalizer (c.L : Set G) := inclusion (residual_normalizes c) y
  let nl : normalizer (c.L : Set G) := ⟨l, c.L.le_normalizer l.property⟩
  have hh := quotientAut_commute n ny nl
    (YC_commutator_le d c (commutator_mem_commutator y.property l.property))
  have ht (w : D) : quotientAut n nl (Multiplicative.ofAdd w) =
      Multiplicative.ofAdd (NaturalCopies (ZMod 2) a g w) := by
    obtain ⟨q, hq⟩ := coordinates_surjective n (Multiplicative.ofAdd w)
    have hq' : (coordinates n q).toAdd = w := congrArg Multiplicative.toAdd hq
    calc
      _ = coordinates n (layerConjugate _ _ (normalizer_le_normalizer_commutatorCore c.L) nl q) := by
        rw [← hq]
        exact quotientAut_apply n nl q
      _ = _ := by
        have hi := n.intertwining l q
        change (coordinates n (layerConjugate _ _ n.normalized l q)).toAdd =
          NaturalCopies (ZMod 2) a (e (QuotientGroup.mk' _ l)) (coordinates n q).toAdd at hi
        rw [hl, hq'] at hi
        exact congrArg Multiplicative.ofAdd hi
  have h := congrArg (fun f : MulAut (Multiplicative D) => f (Multiplicative.ofAdd v)) hh.eq
  change quotientAut n ny (quotientAut n nl (Multiplicative.ofAdd v)) =
    quotientAut n nl (quotientAut n ny (Multiplicative.ofAdd v)) at h
  rw [ht v] at h
  change quotientAut n ny (Multiplicative.ofAdd (NaturalCopies (ZMod 2) a g v)) =
    quotientAut n nl (Multiplicative.ofAdd (residualAction c n y v)) at h
  rw [ht] at h
  exact congrArg Multiplicative.toAdd h

/-- Trivial marked quotient action puts the displacement in the fixed kernel. -/
theorem displacement_le_fixed_of_trivial
    (htriv : ∀ y, residualAction c n y = 1) :
    ⁅YC d c.L, commutatorCore c.L⁆ ≤ coreFixed c.L := by
  apply commutator_le.mpr
  intro y hy q hq
  let yY : YC d c.L := ⟨y, hy⟩
  let qQ : commutatorCore c.L := ⟨q, hq⟩
  let q' := layerConjugate _ _ ((residual_normalizes c).trans (normalizer_le_normalizer_commutatorCore c.L)) yY qQ
  have he := LinearMap.congr_fun (htriv yY) (coordinates n qQ).toAdd
  rw [residualAction_apply] at he
  have he' : coordinates n q' = coordinates n qQ := congrArg Multiplicative.ofAdd he
  have hk : coordinates n (q' * qQ⁻¹) = 1 := by
    rw [map_mul, map_inv, he', mul_inv_cancel]
  exact (coordinates_eq_one n (q' * qQ⁻¹)).mp hk

/-- Fixing the kernel and its quotient fixes Q: inverse displacement maps
into the two-group kernel are homomorphisms killed by two-perfectness. -/
theorem core_fixed_of_displacement_le_fixed [Finite G]
    (hfix : YC d c.L ≤ centralizer (coreFixed c.L : Set G))
    (hcomm : ⁅YC d c.L, commutatorCore c.L⁆ ≤ coreFixed c.L) :
    YC d c.L ≤ centralizer (commutatorCore c.L : Set G) := by
  have hZ : IsPGroup 2 (coreFixed c.L) :=
    ((c.L.isPGroup_pCoreIn 2).to_le (commutatorCore_le c.L)).to_le inf_le_left
  have hp := ComponentIntersection.centralizerResidual_isPPerfect d.Yplus c.L
  intro y hy q hq
  let f : YC d c.L →* coreFixed c.L :=
    { toFun x := ⟨⁅(x : G), q⁆⁻¹,
        (coreFixed c.L).inv_mem (hcomm (commutator_mem_commutator x.property hq))⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' x z := by
        apply Subtype.ext
        change ⁅(x : G) * (z : G), q⁆⁻¹ = ⁅(x : G), q⁆⁻¹ * ⁅(z : G), q⁆⁻¹
        have hc := hfix x.property _ (hcomm (commutator_mem_commutator z.property hq))
        rw [commutatorElement_mul_left_eq_conj_mul, ← hc, mul_inv_cancel_right, mul_inv_rev] }
  have hf := hp.hom_eq_one_of_isPGroup hZ f
  have he := congrArg (fun k : YC d c.L →* coreFixed c.L => (k ⟨y, hy⟩ : G)) hf
  change ⁅y, q⁆⁻¹ = 1 at he
  exact (commutatorElement_eq_one_iff_mul_comm.mp (inv_eq_one.mp he)).symm

private theorem normalizer_fixes_small [Finite G] (F : Subgroup G)
    (hF : Nat.card F ≤ 2) : normalizer (F : Set G) ≤ centralizer (F : Set G) := by
  have hp : 0 < Nat.card F := Nat.card_pos
  have hc : Nat.card F = 1 ∨ Nat.card F = 2 := by omega
  rcases hc with hc | hc
  · rw [Subgroup.card_eq_one.mp hc]
    intro g _ x hx
    have hx' : x = 1 := hx
    subst x
    simp
  · exact normalizer_le_centralizer_of_card_two F hc

/-- A fixed subgroup of order four survives the small fixed kernel, so the
actual residual centralizes both Q and L. No splitting or central-omega
assertion is required. -/
theorem YC_centralizes_natural_quotient [Finite G]
    {e' : (c.L ⧸ pCore 2 c.L) ≃* SL}
    (m : LayerModel c.L (commutatorCore c.L) (coreFixed c.L) e' (NaturalCopies (ZMod 2) a))
    (ha : a = 1 ∨ a = 2) (hF : Nat.card (coreFixed c.L) ≤ 2)
    (U : Subgroup G) (hU : Nat.card U = 4) (hUQ : U ≤ commutatorCore c.L)
    (hfix : YC d c.L ≤ centralizer (U : Set G)) :
    YC d c.L ≤ centralizer (commutatorCore c.L : Set G) ∧
      YC d c.L ≤ centralizer (c.L : Set G) := by
  have hnot : ¬ U ≤ coreFixed c.L := by
    intro h
    have hc := (Nat.card_le_card_of_injective (inclusion h) (inclusion_injective h)).trans hF
    rw [hU] at hc
    omega
  obtain ⟨u, hu, hun⟩ := SetLike.not_le_iff_exists.mp hnot
  let q : commutatorCore c.L := ⟨u, hUQ hu⟩
  let w : D := (coordinates m q).toAdd
  have hw : w ≠ 0 := by
    intro h
    exact hun ((coordinates_eq_one m q).mp (congrArg Multiplicative.ofAdd h))
  have hfw (y : YC d c.L) : residualAction c m y w = w := by
    rw [residualAction_apply]
    have he : layerConjugate _ _
        ((residual_normalizes c).trans (normalizer_le_normalizer_commutatorCore c.L)) y q = q := by
      apply Subtype.ext
      change (y : G) * u * (y : G)⁻¹ = u
      rw [← hfix y.property u hu, mul_inv_cancel_right]
    rw [he]
  have ht := NaturalActions.twoPerfect_copies_fixed ha (residualAction c m)
    (ComponentIntersection.centralizerResidual_isPPerfect d.Yplus c.L)
    (residualAction_commutes c m) w hw hfw
  have hfixF : YC d c.L ≤ centralizer (coreFixed c.L : Set G) :=
    ((residual_normalizes c).trans normalizer_fixed).trans (normalizer_fixes_small _ hF)
  have hc := core_fixed_of_displacement_le_fixed c hfixF
    (displacement_le_fixed_of_trivial c m ht)
  exact ⟨hc, YC_centralizes_of_core_fixed d c hc⟩

section BinaryInput
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}}
  {K R : Subgroup J} (b : ChapterC.BinaryMS.Input κ K R)

/-- The Chapter C natural quotient gives a literal local layer model. -/
noncomputable def localNaturalLayer {m : ℕ}
    (q : ChapterC.BinaryMS.AbelianCore.NaturalQuotient b m) :
    LayerModel K (sourceQ K) (sourceFixed K) q.quotientEquiv (NaturalCopies (ZMod 2) m) := by
  have hker : q.projection.ker = (sourceFixed K).subgroupOf (sourceQ K) := by
    rw [q.kernel]
    ext x
    exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩
  have hn : ((sourceFixed K).subgroupOf (sourceQ K)).Normal := hker ▸ inferInstance
  let _ := hn
  let eQ := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q.projection q.surjective)
  refine {
    lower_le := inf_le_left
    normalized := normalizer_commutator_ge_right _ _
    lower_normal := hn
    quotientIso := eQ
    intertwining := ?_ }
  intro k x
  change (q.projection (layerConjugate K (sourceQ K)
    (normalizer_commutator_ge_right _ _) k x)).toAdd =
      NaturalCopies (ZMod 2) m (q.quotientEquiv (QuotientGroup.mk' _ k)) (q.projection x).toAdd
  have he : layerConjugate K (sourceQ K) (normalizer_commutator_ge_right _ _) k x =
      b.coreConjugate k x := by
    apply Subtype.ext
    exact (b.coreConjugate_val k x).symm
  rw [he]
  funext i
  exact q.equivariant k x i

include b in
/-- The proved abelian MS quotient and kernel bound give all the local
module data used by the residual argument. -/
theorem local_natural_layer_of_abelian
    (hc : IsMulCommutative (sourceQ K)) :
    ∃ (m : ℕ) (e' : (K ⧸ pCore 2 K) ≃* SL),
      (m = 1 ∨ m = 2) ∧ Nat.card (sourceFixed K) ≤ 2 ∧
      Nonempty (LayerModel K (sourceQ K) (sourceFixed K) e' (NaturalCopies (ZMod 2) m)) := by
  obtain ⟨m, hm, ⟨q⟩⟩ :=
    ChapterC.BinaryMS.AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient
      (h := b) hc
  have hbound := (b.abelianCore_fixedKernel_bounds hc hm q).1
  have hmap : (ChapterC.BinaryMS.coreFixed K).map (sourceQ K).subtype = sourceFixed K := by
    change ((centralizer (K : Set J)).subgroupOf (sourceQ K)).map (sourceQ K).subtype = _
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.property, hq⟩
    · rintro ⟨hx, hc⟩
      exact ⟨⟨x, hx⟩, hc, rfl⟩
  have hcard : Nat.card (sourceFixed K) ≤ 2 := by
    rw [← hmap, card_map_of_injective (sourceQ K).subtype_injective]
    exact hbound
  exact ⟨m, q.quotientEquiv, hm, hcard, ⟨localNaturalLayer b q⟩⟩
end BinaryInput

/-- Apply the actual binary MS input on LS to the ambient residuals. The
literal subgroup inclusion transports both the quotient and its kernel. -/
theorem YC_centralizes_of_binary_sylow_input [Finite G]
    {κ : GroupClass} (b : ChapterC.BinaryMS.Input κ
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (hc : IsMulCommutative (sourceQ (c.L.subgroupOf (c.L ⊔ d.S))))
    (U : Subgroup G) (hU : Nat.card U = 4) (hUQ : U ≤ commutatorCore c.L)
    (hfix : YC d c.L ≤ centralizer (U : Set G)) :
    YC d c.L ≤ centralizer (commutatorCore c.L : Set G) ∧
      YC d c.L ≤ centralizer (c.L : Set G) := by
  obtain ⟨m, e', hm, hF, ⟨q⟩⟩ := local_natural_layer_of_abelian b hc
  have q' := ambientLayer (show c.L ≤ c.L ⊔ d.S from le_sup_left) q
  rw [sourceQ_map_subtype le_sup_left b.component, sourceFixed_map le_sup_left b.component] at q'
  have hF' : Nat.card (coreFixed c.L) ≤ 2 := by
    rw [← sourceFixed_map (show c.L ≤ c.L ⊔ d.S from le_sup_left) b.component,
      card_map_of_injective (c.L ⊔ d.S).subtype_injective]
    exact hF
  exact YC_centralizes_natural_quotient c q' hm hF' U hU hUQ hfix

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.AbelianQuotient
