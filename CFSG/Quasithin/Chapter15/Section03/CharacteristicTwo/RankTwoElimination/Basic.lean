module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# The component span and plus action in the rank-two branch

For the orthogonal local data of Section 15.3, we construct
`W_L = ⟨V^L⟩` and `(LRY₊)⁺ = LRY₊/C_{LRY₊}(W_L)`. The relative
normality of the denominator follows from normalization of both `V` and `L`.
The action is actual conjugation, and its binary representation, when the span
is elementary abelian, has the same vectors and a proved trivial kernel.

The equality `R = C_T(V)` gives `V ≤ Z(R)`. Together with `O₂(L) ≤ R`,
it makes the action factor through `L/O₂(L)`. Noncentrality then transfers
quasisimplicity to `L⁺`. A two-group center of `L/O₂(L)` gives an actual
multiplicative equivalence with `L⁺`, for the later multiplier argument.
We also transport the proved central-omega bound of 15.3.8 to prime rank.

The preliminary conclusions are explicit inputs. In particular, no block
classification or elementarity of `W_L` is asserted here. `Y_C` uses the genuine
section centralizer and its two-residual; `|Y_C|₃ = 3` must not be replaced by
`|Y_C| = 3`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.14(1), 15.3.16(1), and the covering step of 15.3.22,
printed pp.1125–1128 (PDF pp.1142–1145).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination

variable {G : Type*} [Group G]

private theorem normalizes_span {A V L : Subgroup G}
    (hL : A ≤ normalizer (L : Set G))
    (hV : A ≤ normalizer (V : Set G)) :
    A ≤ normalizer (localSpan V L : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro a ha x ⟨l, hl, v, hv, rfl⟩
  refine subset_closure ⟨a * l * a⁻¹, (hL ha l).mp hl,
    a * v * a⁻¹, (hV ha v).mp hv, ?_⟩
  group

/-- A component chosen in the intrinsic Thompson subgroup still lies in `I`. -/
theorem component_le {d : LocalData G} {I : Subgroup G}
    (c : ComponentWitness d I) : c.L ≤ I := by
  apply c.le_thompson.trans
  exact sSup_le fun A hA => hA.1

variable (d : LocalData G)

/-- The source group `LRY₊`, with products expressed by their generated subgroup. -/
abbrev overgroup (L : Subgroup G) : Subgroup G := L ⊔ d.R ⊔ d.Yplus

/-- The two-residual of `Y₊ ∩ L`; this is not its two-core. -/
noncomputable abbrev YL (L : Subgroup G) : Subgroup G :=
  ComponentIntersection.intersectionResidual d.Yplus L

/-- The two-residual of the actual action kernel on `L/O₂(L)`. No order-three assertion is made. -/
noncomputable abbrev YC (L : Subgroup G) : Subgroup G :=
  ComponentIntersection.centralizerResidual d.Yplus L

/-- The rank-two module `U_L = [W_L,L]`, distinct from the rank-one `[U_I,L]`. -/
abbrev spanCommutator (L : Subgroup G) : Subgroup G := ⁅d.componentSpan L, L⁆

/-- The precise earlier input 15.3.15(3), to be supplied by the characteristic-two assembly. -/
def SolvableInvariantControl (I : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≤ I → Group.IsSolvable X →
    d.Yplus ⊔ d.S ≤ normalizer (X : Set G) → X ≤ d.MI I

/-- The orthogonal module is contained in `R = C_T(V)`. -/
theorem V_le_R [Finite G]
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    d.V ≤ d.R := by
  have hVT : d.V ≤ (d.T : Subgroup G) :=
    d.action.le_sylow d.T d.sylow_le (localModule_le d.T d.sylow_le)
  have hVV : d.V ≤ centralizer (d.V : Set G) := by
    let _ := d.action.elementary
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact (le_inf hVT hVV).trans hR.ge

/-- Source 15.3.14(1), in ambient subgroup notation, from 15.3.11(5i). -/
theorem V_le_center_R [Finite G]
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    d.V ≤ d.R ⊓ centralizer (d.R : Set G) :=
  le_inf (V_le_R d hR) (le_centralizer_iff.mp (hR.le.trans inf_le_right))

/-- The span `W_L` lies in the actual overgroup `LRY₊`. -/
theorem span_le_overgroup [Finite G] (L : Subgroup G)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    d.componentSpan L ≤ overgroup d L := by
  have hVH : d.V ≤ overgroup d L :=
    (V_le_R d hR).trans (le_sup_right.trans le_sup_left)
  have hLH : L ≤ overgroup d L := le_sup_left.trans le_sup_left
  exact conjugateSpanBy_le hVH (hLH.trans (overgroup d L).le_normalizer)

/-- All three factors of `LRY₊` lie in the chosen outside overgroup. -/
theorem overgroup_le {I L : Subgroup G} (hI : I ∈ d.Hplus) (hL : L ≤ I) :
    overgroup d L ≤ I :=
  sup_le (sup_le hL (((d.Yplus ⊔ d.S).pCoreIn_le 2).trans hI.1.2))
    (le_sup_left.trans hI.1.2)

/-- The earlier residual and component normalizations make `W_L` invariant under `LRY₊`. -/
theorem overgroup_normalizes_span {I L : Subgroup G}
    (hθ : theta (d.M ⊓ I) = d.Yplus)
    (hR : d.R ≤ centralizer (d.V : Set G))
    (hRL : d.R ≤ normalizer (L : Set G))
    (hYL : d.Yplus ≤ normalizer (L : Set G)) :
    overgroup d L ≤ normalizer (d.componentSpan L : Set G) := by
  have hYM : d.Yplus ≤ d.M := by
    calc d.Yplus = theta (d.M ⊓ I) := hθ.symm
         _ ≤ d.M := (theta_le _).trans inf_le_left
  exact sup_le (sup_le (le_normalizer_conjugateSpanBy d.V L)
    (normalizes_span hRL (hR.trans (Subgroup.centralizer_le_normalizer _))))
    (normalizes_span hYL (hYM.trans d.action.normalizes))

/-- The preliminary bound `O₂(L) ≤ R ≤ C_G(V)` kills the two-core action on the whole span. -/
theorem core_centralizes_span (L : Subgroup G)
    (hcore : L.pCoreIn 2 ≤ d.R)
    (hR : d.R ≤ centralizer (d.V : Set G)) :
    L.pCoreIn 2 ≤ centralizer (d.componentSpan L : Set G) := by
  apply le_centralizer_iff.mpr
  exact conjugateSpanBy_le (le_centralizer_iff.mp (hcore.trans hR))
    ((L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L
      (pCore 2 L))).trans (normalizer_le_normalizer_centralizer _))

/-- The centralizer `C_{LRY₊}(W_L)`, formed intrinsically inside `LRY₊`. -/
def actionKernel (L : Subgroup G) : Subgroup (overgroup d L) :=
  (centralizer (d.componentSpan L : Set G)).subgroupOf (overgroup d L)

/-- Normalization of the span proves the relative normality needed for the quotient. -/
theorem actionKernel_normal {L : Subgroup G}
    (hN : overgroup d L ≤ normalizer (d.componentSpan L : Set G)) :
    (actionKernel d L).Normal :=
  normal_subgroupOf_of_le_normalizer (hN.trans (normalizer_le_normalizer_centralizer _))

/-- The source plus quotient `(LRY₊)/C_{LRY₊}(W_L)`. -/
abbrev Plus (L : Subgroup G) [(actionKernel d L).Normal] :=
  overgroup d L ⧸ actionKernel d L

/-- The natural projection onto the plus quotient. -/
def plusMap (L : Subgroup G) [(actionKernel d L).Normal] :
    overgroup d L →* Plus d L := QuotientGroup.mk' (actionKernel d L)

/-- The plus image of the intersection with `LRY₊`. -/
def plusImage (L X : Subgroup G) [(actionKernel d L).Normal] :
    Subgroup (Plus d L) := (X.subgroupOf (overgroup d L)).map (plusMap d L)

/-- Conjugation on the actual span, restricted from its normalizer. -/
def conjugation {L : Subgroup G}
    (hN : overgroup d L ≤ normalizer (d.componentSpan L : Set G)) :
    overgroup d L →* MulAut (d.componentSpan L) :=
  (d.componentSpan L).normalizerMonoidHom.comp (inclusion hN)

/-- The kernel of conjugation is exactly the specified relative centralizer. -/
theorem conjugation_ker {L : Subgroup G}
    (hN : overgroup d L ≤ normalizer (d.componentSpan L : Set G)) :
    (conjugation d hN).ker = actionKernel d L := by
  rw [conjugation, ← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  rfl

/-- The action of the plus quotient on `W_L`. -/
def action {L : Subgroup G} [(actionKernel d L).Normal]
    (hN : overgroup d L ≤ normalizer (d.componentSpan L : Set G)) :
    Plus d L →* MulAut (d.componentSpan L) :=
  QuotientGroup.lift (actionKernel d L) (conjugation d hN)
    (conjugation_ker d hN).ge

/-- The centralizer quotient acts faithfully. -/
theorem action_injective {L : Subgroup G} [(actionKernel d L).Normal]
    (hN : overgroup d L ≤ normalizer (d.componentSpan L : Set G)) :
    Function.Injective (action d hN) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (conjugation_ker d hN).symm

/-- The descended action retains the ambient conjugation formula. -/
theorem action_apply {L : Subgroup G} [(actionKernel d L).Normal]
    (hN : overgroup d L ≤ normalizer (d.componentSpan L : Set G))
    (g : overgroup d L) (w : d.componentSpan L) :
    (action d hN (plusMap d L g) w : G) = (g : G) * w * (g : G)⁻¹ := rfl

/-- An outside component cannot act trivially, since `C_G(V) ≤ M`. -/
theorem component_image_ne_bot {I : Subgroup G} (c : ComponentWitness d I)
    [(actionKernel d c.L).Normal]
    (hC : centralizer (d.V : Set G) ≤ d.M) :
    plusImage d c.L c.L ≠ ⊥ := by
  intro h
  have hker := (map_eq_bot_iff (c.L.subgroupOf (overgroup d c.L))).mp h
  rw [show (plusMap d c.L).ker = actionKernel d c.L from QuotientGroup.ker_mk' _] at hker
  apply c.outside
  intro l hl
  have hL : c.L ≤ overgroup d c.L := le_sup_left.trans le_sup_left
  have hc := hker (show (⟨l, hL hl⟩ : overgroup d c.L) ∈
    c.L.subgroupOf (overgroup d c.L) from hl)
  exact hC (centralizer_le (le_conjugateSpanBy d.V c.L) hc)

/-- The surjection from `L` onto its actual plus image. -/
def componentMap (L : Subgroup G) [(actionKernel d L).Normal] :
    L →* plusImage d L L where
  toFun l := ⟨plusMap d L ⟨l, (le_sup_left.trans le_sup_left : L ≤ overgroup d L) l.property⟩,
    mem_map.mpr ⟨⟨l, (le_sup_left.trans le_sup_left : L ≤ overgroup d L) l.property⟩,
      l.property, rfl⟩⟩
  map_one' := Subtype.ext ((plusMap d L).map_one)
  map_mul' x y := Subtype.ext ((plusMap d L).map_mul
    (⟨x, (le_sup_left.trans le_sup_left : L ≤ overgroup d L) x.property⟩ : overgroup d L)
    (⟨y, (le_sup_left.trans le_sup_left : L ≤ overgroup d L) y.property⟩ : overgroup d L))

/-- Every element of `L⁺` lifts to an element of `L`. -/
theorem componentMap_surjective (L : Subgroup G) [(actionKernel d L).Normal] :
    Function.Surjective (componentMap d L) := by
  rintro ⟨q, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- Centralization of the span makes the component action factor through its two-core quotient. -/
theorem core_le_componentMap_ker (L : Subgroup G) [(actionKernel d L).Normal]
    (hcore : L.pCoreIn 2 ≤ centralizer (d.componentSpan L : Set G)) :
    pCore 2 L ≤ (componentMap d L).ker := by
  intro x hx
  apply Subtype.ext
  change plusMap d L ⟨x, _⟩ = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  exact hcore (mem_map.mpr ⟨x, hx, rfl⟩)

/-- The induced map `L/O₂(L) → L⁺`. -/
def coreQuotientMap (L : Subgroup G) [(actionKernel d L).Normal]
    (hcore : L.pCoreIn 2 ≤ centralizer (d.componentSpan L : Set G)) :
    (L ⧸ pCore 2 L) →* plusImage d L L :=
  QuotientGroup.lift (pCore 2 L) (componentMap d L) (core_le_componentMap_ker d L hcore)

/-- The induced map from the two-core quotient is surjective. -/
theorem coreQuotientMap_surjective (L : Subgroup G) [(actionKernel d L).Normal]
    (hcore : L.pCoreIn 2 ≤ centralizer (d.componentSpan L : Set G)) :
    Function.Surjective (coreQuotientMap d L hcore) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (componentMap_surjective d L) _

/-- The quasisimplicity clause of 15.3.16(1), from the earlier component witness and core bound. -/
theorem component_image_quasisimple {I : Subgroup G} (c : ComponentWitness d I)
    [(actionKernel d c.L).Normal]
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R ≤ centralizer (d.V : Set G))
    (hC : centralizer (d.V : Set G) ≤ d.M) :
    Theory.GroupTheory.IsQuasisimple (plusImage d c.L c.L) := by
  let _ := c.core_quotient_quasisimple
  let _ : Nontrivial (plusImage d c.L c.L) :=
    (nontrivial_iff_ne_bot _).mpr (component_image_ne_bot d c hC)
  exact Theory.GroupTheory.IsQuasisimple.of_surjective
    (coreQuotientMap d c.L (core_centralizes_span d c.L hcore hR))
    (coreQuotientMap_surjective d c.L _)

/-- The already proved 15.3.8 bound excludes the rank-three central omega case in C.1.34. -/
theorem centralOmega_rank_le_two [Finite G]
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4) :
    primeRank 2 (centralOmegaIn d.S) ≤ 2 := by
  let _ := d.action.elementary_fixedPlane d.S
  have heq := fixedPlane_eq_centralOmegaIn d.T d.V d.S inf_le_left hindex hZ
    (d.action.fixedPlane_le_stabilizer d.T d.sylow_le
      (localModule_le d.T d.sylow_le) 1) hZS
  rw [← heq]
  exact IsElementaryAbelian.primeRank_le_of_card_le (fixedPlane d.V d.S) (by
    change Nat.card d.ZS ≤ 2 ^ 2
    rw [hZS]
    decide)

/-- The actual plus action as a binary representation.
Elementarity of the span is an explicit obligation. -/
noncomputable def representation {L : Subgroup G} [(actionKernel d L).Normal]
    [IsElementaryAbelian 2 (d.componentSpan L)]
    (hN : overgroup d L ≤ normalizer (d.componentSpan L : Set G)) :
    Representation (ZMod 2) (Plus d L) (Additive (d.componentSpan L)) where
  toFun g := (action d hN g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro w
    change Additive.ofMul (action d hN 1 w.toMul) = w
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro w
    change Additive.ofMul (action d hN (g * h) w.toMul) = _
    rw [map_mul]
    rfl

/-- The binary representation agrees with ambient conjugation on every vector. -/
theorem representation_apply {L : Subgroup G} [(actionKernel d L).Normal]
    [IsElementaryAbelian 2 (d.componentSpan L)]
    (hN : overgroup d L ≤ normalizer (d.componentSpan L : Set G))
    (g : overgroup d L) (w : Additive (d.componentSpan L)) :
    ((representation d hN (plusMap d L g) w).toMul : G) =
      (g : G) * w.toMul * (g : G)⁻¹ := rfl

/-- The binary representation is faithful, by the exact centralizer kernel. -/
theorem representation_injective {L : Subgroup G} [(actionKernel d L).Normal]
    [IsElementaryAbelian 2 (d.componentSpan L)]
    (hN : overgroup d L ≤ normalizer (d.componentSpan L : Set G)) :
    Function.Injective (representation d hN) := by
  intro a b hab
  apply action_injective d hN
  apply MulEquiv.ext
  intro w
  exact congrArg (fun f : Module.End (ZMod 2) (Additive (d.componentSpan L)) =>
    (f (Additive.ofMul w)).toMul) hab

/-- The covering step of 15.3.22: a two-group center makes the core quotient
isomorphic to its plus image. The center hypothesis must come from the
multiplier calculation. -/
theorem core_quotient_equiv_of_center_isTwoGroup [Finite G]
    {I : Subgroup G} (c : ComponentWitness d I) [(actionKernel d c.L).Normal]
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R ≤ centralizer (d.V : Set G))
    (hC : centralizer (d.V : Set G) ≤ d.M)
    (hcenter : IsPGroup 2 (center (c.L ⧸ pCore 2 c.L))) :
    Nonempty ((c.L ⧸ pCore 2 c.L) ≃* plusImage d c.L c.L) := by
  let _ := c.core_quotient_quasisimple
  let _ := component_image_quasisimple d c hcore hR hC
  have hc := core_centralizes_span d c.L hcore hR
  let f : Theory.GroupTheory.Covering (c.L ⧸ pCore 2 c.L) (plusImage d c.L c.L) :=
    { toMonoidHom := coreQuotientMap d c.L hc
      surjective := coreQuotientMap_surjective d c.L hc }
  have hk : IsPGroup 2 f.toMonoidHom.ker := hcenter.to_le f.ker_le_center
  let q := QuotientGroup.mk' (pCore 2 c.L)
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hk' : IsPGroup 2 (componentMap d c.L).ker := by
    have h := hk.comap_of_ker_isPGroup q hq
    rw [MonoidHom.comap_ker] at h
    change IsPGroup 2
      ((QuotientGroup.lift (pCore 2 c.L) (componentMap d c.L)
        (core_le_componentMap_ker d c.L hc)).comp q).ker at h
    rwa [QuotientGroup.lift_comp_mk'] at h
  have heq : (componentMap d c.L).ker = pCore 2 c.L :=
    le_antisymm (le_sSup ⟨inferInstance, hk'⟩) (core_le_componentMap_ker d c.L hc)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (componentMap d c.L)
      (componentMap_surjective d c.L))⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination

end
