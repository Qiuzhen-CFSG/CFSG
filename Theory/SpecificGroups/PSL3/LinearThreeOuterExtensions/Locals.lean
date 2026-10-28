module

public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Model
public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.GroupTheory.PCoreQuotientJoinAction

/-!
# Literal local embeddings and quotient actions in degree-three extensions

The two local factors are embedded into an actual subgroup of Aut(PSL₃)
using the faithful inner action. The core and SL₂ quotient identifications
retain this inclusion and the original quotient map. The local Borel is
N_{Lᵢ}(S ∩ Lᵢ), computed inside Lᵢ and then mapped back to the extension.

Conjugation by the local normalizer descends through the characteristic
two-core. Centerlessness of the concrete SL₂ quotient identifies the
kernel of the action of LᵢS with O₂(LᵢS). Equality with the embedded
O₂(Lᵢ) still requires the family-specific semilinear kernel calculation.
The definition `PreservesPointType` records the intrinsic parabolic-type
condition for the separate identification of the diagram kernel.

Source: Aschbacher–Smith F.1.12, printed pp.263–264, especially the
relative local actions and two-core equalities on p.264.
-/

@[expose] public section
open scoped MatrixGroups
open Matrix Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
namespace Matrix.PSL3.LinearThree.OuterExtensions
variable (F : Type*) [Field F]

open Theory.GroupTheory.AutomorphismExtensionBorel

variable [Finite F]

/-- Intrinsic preservation of the point-parabolic conjugacy class.
Identifying this geometric condition with the linear-field subgroup is a separate theorem. -/
def PreservesPointType (a : MulAut PSL(3,F)) : Prop :=
  ∃ g : PSL(3,F), (pointParabolic F).map a.toMonoidHom =
    (pointParabolic F).map (MulAut.conj g).toMonoidHom

/-- The two actual projective local factors; `true` denotes the point factor. -/
def localFactor (point : Bool) : Subgroup PSL(3,F) :=
  if point then pointLocal F else lineLocal F

/-- The local factor embedded in the chosen actual automorphism overgroup. -/
def localIn (E : Subgroup (MulAut PSL(3,F)))
    (hE : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool) : Subgroup E :=
  (localFactor F point).map (innerEmbedding E hE)

omit [Finite F] in
/-- The literal component inclusion is injective. -/
theorem componentEmbedding_injective (E : Subgroup (MulAut PSL(3,F)))
    (hE : MulAut.innerSubgroup PSL(3,F) ≤ E) :
    Function.Injective (innerEmbedding E hE) :=
  innerEmbedding_injective E hE (inner_injective F)

/-- The local copy is identified using the same component inclusion. -/
noncomputable def localEquiv (E : Subgroup (MulAut PSL(3,F)))
    (hE : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool) :
    localFactor F point ≃* localIn F E hE point :=
  (localFactor F point).equivMapOfInjective (innerEmbedding E hE)
    (componentEmbedding_injective F E hE)

omit [Finite F] in
theorem localEquiv_apply (E : Subgroup (MulAut PSL(3,F)))
    (hE : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool)
    (x : localFactor F point) :
    (localEquiv F E hE point x).val = innerEmbedding E hE x.val := rfl

omit [Finite F] in
/-- Both intrinsic cores are compared in the same ambient extension. -/
theorem local_core_map (E : Subgroup (MulAut PSL(3,F)))
    (hE : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool) :
    (pCore 2 (localIn F E hE point)).map (localIn F E hE point).subtype =
      ((pCore 2 (localFactor F point)).map (localFactor F point).subtype).map
        (innerEmbedding E hE) := by
  rw [← pCore_map_iso 2 (localEquiv F E hE point), Subgroup.map_map, Subgroup.map_map]
  rfl

/-- The local Sylow intersection, regarded as a subgroup of the local factor. -/
def localIntersection (E : Subgroup (MulAut PSL(3,F)))
    (hE : MulAut.innerSubgroup PSL(3,F) ≤ E) (S : Subgroup E) (point : Bool) :
    Subgroup (localIn F E hE point) := S.subgroupOf (localIn F E hE point)

/-- The source Bⱼ = N_{Lⱼ}(S ∩ Lⱼ), embedded back into E. -/
def localBorel (E : Subgroup (MulAut PSL(3,F)))
    (hE : MulAut.innerSubgroup PSL(3,F) ≤ E) (S : Subgroup E) (point : Bool) :
    Subgroup E :=
  (Subgroup.normalizer (localIntersection F E hE S point : Set _)).map
    (localIn F E hE point).subtype

omit [Finite F] in
theorem localIntersection_map (E : Subgroup (MulAut PSL(3,F)))
    (hE : MulAut.innerSubgroup PSL(3,F) ≤ E) (S : Subgroup E) (point : Bool) :
    (localIntersection F E hE S point).map (localIn F E hE point).subtype =
      S ⊓ localIn F E hE point := Subgroup.subgroupOf_map_subtype _ _

variable [CharP F 2]

/-- The identified local quotient is the actual determinant-one two-by-two block. -/
noncomputable def localFactorQuotientEquiv (point : Bool) :
    (localFactor F point ⧸ pCore 2 (localFactor F point)) ≃* SL(2,F) := by
  cases point
  · exact lineLocalCoreQuotientEquiv F
  · exact pointLocalCoreQuotientEquiv F

/-- The same quotient identification in the chosen automorphism extension. -/
noncomputable def localQuotientEquiv (E : Subgroup (MulAut PSL(3,F)))
    (hE : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool) :
    (localIn F E hE point ⧸ pCore 2 (localIn F E hE point)) ≃* SL(2,F) :=
  (QuotientGroup.congr _ _ (localEquiv F E hE point)
    (pCore_map_iso 2 (localEquiv F E hE point))).symm.trans
      (localFactorQuotientEquiv F point)

/-- Compatibility with the original local quotient map, not merely a group isomorphism. -/
theorem localQuotientEquiv_mk (E : Subgroup (MulAut PSL(3,F)))
    (hE : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool)
    (x : localFactor F point) :
    localQuotientEquiv F E hE point
      (QuotientGroup.mk' _ (localEquiv F E hE point x)) =
    localFactorQuotientEquiv F point (QuotientGroup.mk' _ x) := by
  change localFactorQuotientEquiv F point
    (QuotientGroup.mk' _ ((localEquiv F E hE point).symm (localEquiv F E hE point x))) = _
  rw [MulEquiv.symm_apply_apply]

/-- Conjugation by the actual local normalizer, descended to the characteristic two-core. -/
def localQuotientAction (E : Subgroup (MulAut PSL(3,F)))
    (hE : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool) :
    Subgroup.normalizer (localIn F E hE point : Set E) →*
      MulAut (localIn F E hE point ⧸ pCore 2 (localIn F E hE point)) :=
  (Subgroup.quotientAut (pCore 2 (localIn F E hE point))).comp
    (localIn F E hE point).normalizerMonoidHom

omit [Finite F] [CharP F 2] in
/-- The action formula keeps the same conjugation and quotient maps. -/
theorem localQuotientAction_mk (E : Subgroup (MulAut PSL(3,F)))
    (hE : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool)
    (a : Subgroup.normalizer (localIn F E hE point : Set E))
    (x : localIn F E hE point) :
    localQuotientAction F E hE point a (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ ((localIn F E hE point).normalizerMonoidHom a x) :=
  Subgroup.quotientAut_apply_mk _ _ _

/-- The action on the rank-one block using the proved local quotient identification. -/
noncomputable def localBlockAction (E : Subgroup (MulAut PSL(3,F)))
    (hE : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool) :
    Subgroup.normalizer (localIn F E hE point : Set E) →* MulAut SL(2,F) :=
  (MulAut.congr (localQuotientEquiv F E hE point)).toMonoidHom.comp
    (localQuotientAction F E hE point)

/-- Centerlessness is supplied by the concrete SL₂ quotient in characteristic two. -/
theorem localQuotient_center_eq_bot (E : Subgroup (MulAut PSL(3,F)))
    (hE : MulAut.innerSubgroup PSL(3,F) ≤ E) (point : Bool) :
    Subgroup.center (localIn F E hE point ⧸ pCore 2 (localIn F E hE point)) = ⊥ := by
  apply (Subgroup.center _).eq_bot_iff_forall.mpr
  intro x hx
  apply (localQuotientEquiv F E hE point).injective
  have hz := (Subgroup.centerCongr (localQuotientEquiv F E hE point) ⟨x, hx⟩).property
  change localQuotientEquiv F E hE point x ∈ Subgroup.center SL(2,F) at hz
  rw [Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot] at hz
  simpa only [Subgroup.mem_bot, map_one] using hz

/-- The two-core of LᵢS is the kernel of its literal quotient action.
The further equality with the embedded core of Lᵢ needs the matrix kernel calculation. -/
theorem localJoinAction_kernel (E : Subgroup (MulAut PSL(3,F)))
    (hE : MulAut.innerSubgroup PSL(3,F) ≤ E) (S : Subgroup E) (point : Bool)
    (hSL : S ≤ Subgroup.normalizer (localIn F E hE point)) (hS : IsPGroup 2 S) :
    (Subgroup.pCoreJoinAction 2 hSL).ker =
      pCore 2 (localIn F E hE point ⊔ S : Subgroup E) :=
  Subgroup.pCoreJoinAction_kernel 2 hSL hS (localQuotient_center_eq_bot F E hE point)

end Matrix.PSL3.LinearThree.OuterExtensions
