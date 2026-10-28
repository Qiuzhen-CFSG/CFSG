module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.PlaneAction.FixedLifting
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.CentralCover

/-!
# The moved part of the original symplectic plane

The actual plane projection is a central surjection onto the natural SL₂
module. Perfectness of the local residual makes its moved subspace Irr⁺;
its natural image is the whole plane. The remaining quotient is generated
by the original C_V(L) and has binary dimension at most the field degree.
For field four these facts discharge all local-action premises of the
repaired component-uniqueness argument. The preceding component membership
remains with qt-d-1222-natural-relative-components, and final source assembly
with qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, 11.0.3(3), 11.1.3 and I.2.3(1),
printed pp.760,765,413. The full plane preimage is not asserted to be Irr⁺.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.PlaneAction

private theorem natural_top_isIrrPlus
    {A E : Type*} [Group A] [Field E] [CharP E 2] [Algebra (ZMod 2) E]
    (π : A →* SL(2,E)) (hπ : Function.Surjective π) :
    IsIrrPlus ((restrictScalars (k := ZMod 2) (specialLinearNatural (k := E) 2)).comp π)
      ⊤ ⊤ := by
  let σ := (restrictScalars (k := ZMod 2) (specialLinearNatural (k := E) 2)).comp π
  have htrans (v w : Fin 2 → E) (hv : v ≠ 0) (hw : w ≠ 0) :
      ∃ a : A, σ a v = w := by
    obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq E v w hv hw
    obtain ⟨a,rfl⟩ := hπ g
    exact ⟨a,hg⟩
  have hdich (J : Submodule (ZMod 2) (Fin 2 → E))
      (hs : (⊤ : Subgroup A) ≤ subspaceStabilizer σ J) : J = ⊥ ∨ J = ⊤ := by
    by_cases hz : J = ⊥
    · exact Or.inl hz
    right
    obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hz
    apply top_unique
    intro w _
    by_cases hw : w = 0
    · exact hw ▸ J.zero_mem
    obtain ⟨a,rfl⟩ := htrans v w hv0 hw
    exact (hs (mem_top a) v).mpr hv
  have hn : ¬ (⊤ : Submodule (ZMod 2) (Fin 2 → E)) ≤ fixedSpace σ ⊤ := by
    intro hf
    obtain ⟨a,ha⟩ := htrans ![1,0] ![0,1] (by simp) (by simp)
    have hh := hf (show (![1,0] : Fin 2 → E) ∈ (⊤ : Submodule (ZMod 2) _) from trivial)
      (⟨a,mem_top a⟩ : (⊤ : Subgroup A))
    have h0 := congrFun (ha.symm.trans hh) 0
    simp at h0
  have hm : subspaceCommutator σ ⊤ ⊤ = ⊤ := by
    rcases hdich _ (subspaceCommutator_invariant σ ⊤ ⊤) with hb | ht
    · exact (hn ((subspaceCommutator_eq_bot_iff σ ⊤ ⊤).mp hb)).elim
    · exact ht
  apply isIrrPlus_of_minimal σ (le_subspaceStabilizer σ ⊤ (by intros; trivial)) hm hn
  intro J hJ _
  rcases hdich J hJ with hb | ht
  · exact Or.inr (hb ▸ bot_le)
  · exact Or.inl ht

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

private def localInNormalizerEquiv :
    ((flag m S).Li 1).subgroupOf (normalizer ((flag m S).Vi 1 : Set G)) ≃* (flag m S).Li 1 :=
  subgroupOfEquivOfLe ((localResidual_le _).trans inf_le_right)

private def localNaturalAction :
    Representation (ZMod 2)
      (((flag m S).Li 1).subgroupOf (normalizer ((flag m S).Vi 1 : Set G)))
      (Fin 2 → S.field.Carrier) :=
  (restrictScalars (k := ZMod 2) (specialLinearNatural 2)).comp
    ((planeProjection S m).comp (localInNormalizerEquiv S m).toMonoidHom)

private theorem localNaturalAction_isIrrPlus : IsIrrPlus (localNaturalAction S m) ⊤ ⊤ :=
  natural_top_isIrrPlus _ ((planeProjection_surjective S m).comp
    (localInNormalizerEquiv S m).surjective)

/-- Irr⁺ holds on the actual commutator plane, with the central-quotient bound. -/
theorem secondMoved_isIrrPlus_and_quotient_rank :
    IsIrrPlus (Components.flagAction (flag m S) 1)
      (((flag m S).Li 1).subgroupOf (normalizer ((flag m S).Vi 1 : Set G)))
      (Components.secondMoved (flag m S)) ∧
      Module.finrank (ZMod 2) (Additive ((flag m S).Vi 1) ⧸
        Components.secondMoved (flag m S)) ≤ S.field.degree :=
  Components.secondMoved_of_cover S (flag m S) (localNaturalAction S m)
    (planeMap S m) (planeMap_surjective S m)
    (fun a v => planeMap_intertwines S m (localInNormalizerEquiv S m a) v)
    (planeMap_eq_zero_iff S m) (localNaturalAction_isIrrPlus S m)

/-- The moved subspace still maps onto the entire natural plane. -/
theorem secondMoved_map :
    (Components.secondMoved (flag m S)).map (planeMap S m) = ⊤ := by
  let f := flag m S
  let A := (f.Li 1).subgroupOf (normalizer (f.Vi 1 : Set G))
  let τ := (Components.flagAction f 1).comp A.subtype
  have hm : subspaceCommutator τ ⊤ (⊤ : Subgroup A) = Components.secondMoved f := by
    rw [subspaceCommutator_comp_map,← MonoidHom.range_eq_map,range_subtype]
    rfl
  rw [← hm]
  rw [map_moved_of_surjective_intertwining τ (localNaturalAction S m) ⊤
    (planeMap S m) (planeMap_surjective S m)
    (fun a v => planeMap_intertwines S m (localInNormalizerEquiv S m a) v)]
  exact (localNaturalAction_isIrrPlus S m).choose_spec.1

/-- The original central kernel supplements the moved plane. -/
theorem secondMoved_sup_kernel :
    Components.secondMoved (flag m S) ⊔ (planeMap S m).ker = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨i,hi,hiv⟩ := (show planeMap S m v ∈
    (Components.secondMoved (flag m S)).map (planeMap S m) from
      (secondMoved_map S m).symm ▸ Submodule.mem_top)
  have hk : v-i ∈ (planeMap S m).ker := by
    change planeMap S m (v-i) = 0
    rw [map_sub,hiv,sub_self]
  have h := (Components.secondMoved (flag m S) ⊔ (planeMap S m).ker).add_mem
    (Submodule.mem_sup_left hi) (Submodule.mem_sup_right hk)
  simpa only [add_sub_cancel] using h

/-- The moved subspace is the literal ambient commutator [V₂,L₂]. -/
theorem secondMoved_ambient :
    (Components.secondMoved (flag m S)).toAddSubgroup.toSubgroup'.map
      ((flag m S).Vi 1).subtype = ⁅(flag m S).Vi 1,(flag m S).Li 1⁆ := by
  let f := flag m S
  let I := Components.secondMoved f
  let Q := AddSubgroup.toZModSubmodule 2
    ((⁅f.Vi 1,f.Li 1⁆ : Subgroup G).subgroupOf (f.Vi 1)).toAddSubgroup
  have hIQ : I ≤ Q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩
    change ((Components.flagAction f 1 a v - v).toMul : G) ∈ ⁅f.Vi 1,f.Li 1⁆
    rw [toMul_sub]
    change (a.val * (v.toMul : G) * a.val⁻¹) / (v.toMul : G) ∈ ⁅f.Vi 1,f.Li 1⁆
    rw [div_eq_mul_inv]
    rw [commutator_comm]
    exact commutator_mem_commutator ha v.toMul.property
  have hc : ⁅f.Li 1,f.Vi 1⁆ ≤ f.Vi 1 :=
    le_normalizer_iff_commutator_le_right.mp ((localResidual_le _).trans inf_le_right)
  apply le_antisymm
  · rintro x ⟨v,hv,rfl⟩
    exact hIQ hv
  · rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha v hv
    refine ⟨⟨⁅a,v⁆,hc (commutator_mem_commutator ha hv)⟩,?_,rfl⟩
    change Additive.ofMul (⟨⁅a,v⁆,_⟩ : f.Vi 1) ∈ I
    refine Submodule.subset_span ⟨⟨a,(localResidual_le _ ha).2⟩,ha,
      Additive.ofMul (⟨v,hv⟩ : f.Vi 1),Submodule.mem_top,?_⟩
    apply Additive.toMul.injective
    rw [toMul_sub]
    apply Subtype.ext
    change ⁅a,v⁆ = (a*v*a⁻¹)/v
    simp only [commutatorElement_def,div_eq_mul_inv]

/-- Restriction of the original natural projection to the actual commutator. -/
def commutatorPlaneProjection : (⁅(flag m S).Vi 1,(flag m S).Li 1⁆ : Subgroup G) →*
    Multiplicative (Fin 2 → S.field.Carrier) :=
  (naturalPlaneVectorProjection S m).comp (inclusion
    (le_normalizer_iff_commutator_le_left.mp ((localResidual_le _).trans inf_le_right)))

theorem commutatorPlaneProjection_surjective :
    Function.Surjective (commutatorPlaneProjection S m) := by
  intro w
  obtain ⟨v,hv,hvw⟩ := (show w.toAdd ∈
    (Components.secondMoved (flag m S)).map (planeMap S m) from
      (secondMoved_map S m).symm ▸ Submodule.mem_top)
  have hv' : (v.toMul : G) ∈ ⁅(flag m S).Vi 1,(flag m S).Li 1⁆ := by
    rw [← secondMoved_ambient S m]
    exact mem_map_of_mem _ hv
  exact ⟨⟨v.toMul,hv'⟩,hvw⟩

/-- The commutator-plane kernel is exactly its intersection with C_G(L). -/
theorem commutatorPlaneProjection_ker :
    (commutatorPlaneProjection S m).ker =
      (centralizer (L : Set G)).subgroupOf ⁅(flag m S).Vi 1,(flag m S).Li 1⁆ := by
  ext v
  change naturalPlaneVectorProjection S m _ = 1 ↔ (v : G) ∈ centralizer (L : Set G)
  rw [← MonoidHom.mem_ker,naturalPlaneVectorProjection_ker]
  rfl

/-- The natural quotient of the literal commutator, retaining the exact kernel. -/
def commutatorPlaneCentralQuotientEquiv :
    ((⁅(flag m S).Vi 1,(flag m S).Li 1⁆ : Subgroup G) ⧸ (commutatorPlaneProjection S m).ker) ≃*
      Multiplicative (Fin 2 → S.field.Carrier) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (commutatorPlaneProjection_surjective S m)

/-- The restricted projection still intertwines original ambient conjugation. -/
theorem commutatorPlaneProjection_intertwines (l : (flag m S).Li 1)
    (v : (⁅(flag m S).Vi 1,(flag m S).Li 1⁆ : Subgroup G)) :
    commutatorPlaneProjection S m
      ((⁅(flag m S).Vi 1,(flag m S).Li 1⁆ : Subgroup G).normalizerMonoidHom
        ⟨l,normalizer_commutator_ge_right _ _ l.property⟩ v) =
      Multiplicative.ofAdd (specialLinearNatural 2 (planeProjection S m l)
        (commutatorPlaneProjection S m v).toAdd) := by
  exact planeMap_intertwines S m l (Additive.ofMul
    ⟨v,le_normalizer_iff_commutator_le_left.mp
      ((localResidual_le _).trans inf_le_right) v.property⟩)

/-- In the original ambient group, C_V(L) supplements [V₂,L₂] to V₂. -/
theorem commutator_sup_centralizer :
    ⁅(flag m S).Vi 1,(flag m S).Li 1⁆ ⊔ (V ⊓ centralizer (L : Set G)) =
      (flag m S).Vi 1 := by
  let f := flag m S
  apply le_antisymm
  · exact sup_le
      (le_normalizer_iff_commutator_le_left.mp ((localResidual_le _).trans inf_le_right))
      (f.centralizer_le_Vi 1)
  · intro v hv
    have htop : Additive.ofMul (⟨v,hv⟩ : f.Vi 1) ∈
        Components.secondMoved f ⊔ (planeMap S m).ker := by
      rw [secondMoved_sup_kernel]
      trivial
    obtain ⟨i,hi,z,hz,he⟩ := Submodule.mem_sup.mp htop
    have hi' : (i.toMul : G) ∈ ⁅f.Vi 1,f.Li 1⁆ := by
      rw [← secondMoved_ambient S m]
      exact mem_map_of_mem _ hi
    have hz' : (z.toMul : G) ∈ V ⊓ centralizer (L : Set G) :=
      ⟨D.centralQuotientPreimage_le _ z.toMul.property,(planeMap_eq_zero_iff S m z).mp hz⟩
    have hh := (⁅f.Vi 1,f.Li 1⁆ ⊔ (V ⊓ centralizer (L : Set G))).mul_mem
      (mem_sup_left hi') (mem_sup_right hz')
    have he' := congrArg (fun w : Additive (f.Vi 1) => (w.toMul : G)) he
    simp only [toMul_add,coe_mul,toMul_ofMul] at he'
    exact he' ▸ hh

/-- The actual plane-map kernel has the rank of the literal relative centralizer. -/
theorem planeMap_kernel_finrank :
    Module.finrank (ZMod 2) (planeMap S m).ker = rank (V ⊓ centralizer (L : Set G)) :=
  Components.second_cover_kernel_finrank S (flag m S) (planeMap S m)
    (planeMap_eq_zero_iff S m)

/-- The repaired field-four 11.1.3 application has no remaining action premises. -/
theorem uniqueNoncentral_second_fieldFour (hfour : S.field.degree = 2)
    (hL : Source.ComponentIn (normalizer ((flag m S).Vi 1 : Set G)) ((flag m S).Li 1)) :
    Source.UniqueNoncentralComponent (normalizer ((flag m S).Vi 1 : Set G))
      ((flag m S).Vi 1) ((flag m S).Li 1) :=
  Components.uniqueNoncentral_second_fieldFour_of_natural_cover S (flag m S)
    hfour hL (planeProjection S m) (planeProjection_surjective S m)
    (planeMap S m) (planeMap_surjective S m) (planeMap_intertwines S m)
    (planeMap_eq_zero_iff S m) (planeCore_centralizes S m)

/-- The second-normalizer sieve feeds this concrete marked field-four action. -/
theorem uniqueNoncentral_second_fieldFour_of_reduction (hfour : S.field.degree = 2)
    (K X : Subgroup G)
    (hK : Source.NormalComponentIn (normalizer ((flag m S).Vi 1 : Set G)) K)
    (href : Components.RefinementReduction L ((flag m S).Li 0) ((flag m S).Li 1) K X 1 S.field.degree) :
    Source.UniqueNoncentralComponent (normalizer ((flag m S).Vi 1 : Set G))
      ((flag m S).Vi 1) ((flag m S).Li 1) := by
  apply uniqueNoncentral_second_fieldFour S m hfour
  rw [href.second_eq]
  exact hK.1

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.PlaneAction
