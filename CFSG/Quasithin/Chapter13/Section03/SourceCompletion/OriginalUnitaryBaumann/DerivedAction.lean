module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.Normalizer
public import Theory.Representation.G2BinaryThompson

/-!
# The derived-action branch of the original unitary Baumann bound

Restrict the original chosen module to LT and use its specified natural
coordinates. If the LT image lies in the component image, every elementary
Thompson generator centralizes the module by the binary derived G₂
calculation. B.2.10 and the original maximal-local uniqueness then give
the ambient normalizer bound for the same radical. No point-parabolic
identification or block recognition is needed in this branch.

Source: Aschbacher--Smith C.1.37 and13.3.10(2), pp.141,887.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Atlas.G2.Natural.BinaryNormalizer
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original derived-action branch controls the Baumann normalizer
for any overgroup of T inside LT, including the original point residual LT. -/
theorem unitary_baumann_normalizer_of_component_action
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (h : Hypothesis1331 T L) (chosen : ChosenModule T L V)
    (hmax : L ∈ Chapter1.LStar G (T : Subgroup G))
    (eL : (L ⧸ pCore 2 L) ≃* Derived)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (e : inducedAutomizer V L ≃* Derived)
    (E0 : Additive V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2))
    (he0 : ∀ (l : inducedAutomizer V L) v,
      E0 (automizerRepresentation V l v) =
        Atlas.G2.Natural.derivedAction (ZMod 2) (e l) (E0 v))
    (hsmall : inducedAutomizer V (L ⊔ (T : Subgroup G)) ≤ inducedAutomizer V L)
    (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P)
    (hPX : P ≤ L ⊔ (T : Subgroup G)) :
    normalizer (ChapterB.baumann (P.pCoreIn 2) : Set G) ≤ normalizer (L : Set G) := by
  let X := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf X
  let R := (P.pCoreIn 2).subgroupOf X
  have hVX : V ≤ X := chosen.le_sylow.trans le_sup_right
  have hRX : P.pCoreIn 2 ≤ X := (map_subtype_le _).trans hPX
  have hXN : X ≤ normalizer (V : Set G) := sup_le chosen.normalizes hTV
  let : U.Normal := normal_subgroupOf_of_le_normalizer hXN
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVX (p := 2)
  let a : X →* Automizer V := V.normalizerMonoidHom.rangeRestrict.comp (inclusion hXN)
  have ha (x : X) : a x ∈ inducedAutomizer V L :=
    hsmall (mem_map_of_mem V.normalizerMonoidHom.rangeRestrict x.property)
  let f : X →* inducedAutomizer V L := a.codRestrict _ ha
  let q : X →* Full := Derived.subtype.comp (e.toMonoidHom.comp f)
  let aU : Additive U ≃+ Additive V := (subgroupOfEquivOfLe hVX).toAdditive
  let EU : Additive U ≃ₗ[ZMod 2] Additive V := { aU with map_smul' := ZMod.map_smul aU }
  let E := EU.trans E0
  have hE (g : X) (v : U) :
      E (Additive.ofMul (MulAut.conjNormal g v)) =
        Atlas.G2.Natural.action (ZMod 2) (q g) (E (Additive.ofMul v)) := by
    exact he0 (f g) (EU (Additive.ofMul v))
  have hVR : V ≤ P.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
      (chosen.le_sylow.trans hTP) (hPX.trans hXN)
  have hUR : U ≤ R := fun _ hx => hVR hx
  have hRD : R.map q ≤ Derived := by
    rintro _ ⟨x,hx,rfl⟩
    exact (e (f x)).property
  have hJ := thompson_centralizes_of_image_le_derived U q E hE R hUR hRD
  have hJG := map_mono (f := X.subtype) hJ
  rw [←Stellmacher.elementaryAbelianMaxJ_map_injective _ X.subtype_injective,
    map_subgroupOf_eq_of_le hRX,map_centralizer_subtype,
    map_subgroupOf_eq_of_le hVX] at hJG
  exact unitary_baumann_normalizer_of_thompson_centralizes h chosen hmax eL hTV
    P hTP hPX (hJG.trans inf_le_right)

/-- Specialization to the original L₁=O²(C_L(V₁)) and R₁=O₂(L₁T).
The component image condition is the precise remaining action branch. -/
theorem unitary_original_baumann_bound_of_component_action
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Derived)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (e : inducedAutomizer D.V D.L ≃* Derived)
    (E0 : Additive D.V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2))
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction (ZMod 2) (e l) (E0 v))
    (hsmall : inducedAutomizer D.V (D.L ⊔ (D.T : Subgroup G)) ≤ inducedAutomizer D.V D.L) :
    normalizer (ChapterB.baumann ((D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2) : Set G) ≤
      normalizer (D.L : Set G) := by
  have hTV := (unitary_original_module_normalizers h hmax eL chosen structural).1
  have hL1 : D.L₁ ≤ D.L := (map_subtype_le _).trans inf_le_left
  exact unitary_baumann_normalizer_of_component_action h chosen hmax eL hTV e E0 he0 hsmall
    (D.L₁ ⊔ (D.T : Subgroup G)) le_sup_right (sup_le_sup hL1 le_rfl)
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
