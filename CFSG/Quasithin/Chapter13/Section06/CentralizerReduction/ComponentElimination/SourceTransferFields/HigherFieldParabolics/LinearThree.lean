module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The SL₃ flag-residual construction in the literal plus quotient

Starting with K in Y_z, its Tᵥ-invariance and an actual equivalence
K⁺ ≃ SL₃(F), pull both standard maximal parabolics back along K → K⁺.
Their residual images generate K⁺, so one moves z. If the same model
marks the image of Tᵥ ∩ K in the standard unipotent subgroup, both
preimages contain that intersection. The plus core quotient of either
residual is explicitly PSL₂(F).

The ambient simple QTKE hypothesis supplies local SQTK. The earlier
13.6.6 characteristic-two conclusion, together with the actual Sylow
condition on Tᵥ, supplies characteristic two for each residual joined
to Tᵥ. These deductions retain the original quotient maps and kernels.

This is a partial construction for 13.6.19, not the SL₃ exclusion.
The marked module branch must still derive an aligned model, invariance
of its parabolics, and the nonzero core triple commutator. Local-family
membership, intrinsic kernel control and minimal parabolicity also remain
separate obligations. In particular the intrinsic model core quotient is
not silently identified with the core quotient of its ambient preimage.
Earlier-source discharge remains with the centralizer-reduction owner.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
13.6.14, 13.6.16 and 13.6.19, printed pp.929–931.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree
open ComponentSelection
universe u
variable {G : Type u} [Group G]

/-- The literal map from the selected component to its plus image. -/
def componentPlusMap (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    K →* plusImage K L T z v hL hz K :=
  ((plusMk K L T z v hL hz).comp (inclusion (K_le_plusActor K L T v))).codRestrict _
    (fun x => mem_map.mpr ⟨inclusion (K_le_plusActor K L T v) x, x.property, rfl⟩)

theorem componentPlusMap_surjective (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    Function.Surjective (componentPlusMap K L T z v hL hz) := by
  rintro ⟨x, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

theorem componentPlusMap_ker (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    (componentPlusMap K L T z v hL hz).ker =
      (centralizer (WK K L T z v : Set G)).subgroupOf K := by
  ext x
  change componentPlusMap K L T z v hL hz x = 1 ↔ _
  rw [Subtype.ext_iff]
  change inclusion (K_le_plusActor K L T v) x ∈ (plusMk K L T z v hL hz).ker ↔ _
  rw [plusMk_ker]
  rfl

/-- Pull a model subgroup back to K and keep its original ambient embedding. -/
def preimageIn {D : Type*} [Group D] (K : Subgroup G) (f : K →* D)
    (P : Subgroup D) : Subgroup G := (P.comap f).map K.subtype

theorem preimageIn_le {D : Type*} [Group D] (K : Subgroup G) (f : K →* D)
    (P : Subgroup D) : preimageIn K f P ≤ K := map_subtype_le _

private theorem residualIn_map {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (P : Subgroup A) :
    residualIn (P.map f) = (residualIn P).map f := by
  have h := congrArg (map (P.map f).subtype)
    (map_solvableResidual_eq (f.subgroupMap P) (f.subgroupMap_surjective P))
  have he : (P.map f).subtype.comp (f.subgroupMap P) = f.comp P.subtype := rfl
  simpa only [residualIn, map_map, he] using h.symm

/-- Residual formation commutes with taking the image of a full preimage. -/
theorem residualIn_preimage_image [Finite G] {D : Type*} [Group D]
    (K : Subgroup G) (f : K →* D) (hf : Function.Surjective f) (P : Subgroup D) :
    ((residualIn (preimageIn K f P)).subgroupOf K).map f = residualIn P := by
  rw [preimageIn, residualIn_map, subgroupOf,
    comap_map_eq_self_of_injective K.subtype_injective]
  exact map_solvableResidual_comap f hf P

theorem componentPlusMap_subgroup (K L T H : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hH : H ≤ K) :
    ((H.subgroupOf K).map (componentPlusMap K L T z v hL hz)).map
      (plusImage K L T z v hL hz K).subtype = plusImage K L T z v hL hz H := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact mem_map.mpr ⟨inclusion (K_le_plusActor K L T v) a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact mem_map.mpr ⟨componentPlusMap K L T z v hL hz ⟨a, hH ha⟩,
      mem_map.mpr ⟨⟨a, hH ha⟩, ha, rfl⟩, rfl⟩

/-- A model epimorphism constructed from the actual plus map transports
residual generation into precisely the quotient used in 13.6.19. -/
theorem plus_generation_of_model_residuals [Finite G] {D : Type*} [Group D]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : plusImage K L T z v hL hz K ≃* D) (P Q : Subgroup D)
    (hgen : residualIn P ⊔ residualIn Q = ⊤) :
    let f := e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)
    plusImage K L T z v hL hz K ≤
      plusImage K L T z v hL hz (residualIn (preimageIn K f P)) ⊔
        plusImage K L T z v hL hz (residualIn (preimageIn K f Q)) := by
  dsimp only
  let c := componentPlusMap K L T z v hL hz
  let f := e.toMonoidHom.comp c
  have hf : Function.Surjective f := e.surjective.comp
    (componentPlusMap_surjective K L T z v hL hz)
  let A := residualIn (preimageIn K f P)
  let B := residualIn (preimageIn K f Q)
  have hA : A ≤ K := (map_subtype_le _).trans (preimageIn_le K f P)
  have hB : B ≤ K := (map_subtype_le _).trans (preimageIn_le K f Q)
  have hm : (A.subgroupOf K).map c ⊔ (B.subgroupOf K).map c = ⊤ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_sup, map_map, map_map, map_top_of_surjective _ e.surjective]
    exact (congrArg₂ (· ⊔ ·)
      (residualIn_preimage_image K f hf P)
      (residualIn_preimage_image K f hf Q)).trans hgen
  have h := congrArg (map (plusImage K L T z v hL hz K).subtype) hm
  rw [Subgroup.map_sup, componentPlusMap_subgroup K L T A z v hL hz hA,
    componentPlusMap_subgroup K L T B z v hL hz hB,
    ← MonoidHom.range_eq_map, range_subtype] at h
  exact h.ge

/-- Tᵥ-invariance passes from a parabolic to its embedded solvable residual. -/
theorem residualIn_normalized (S P : Subgroup G)
    (hP : S ≤ normalizer (P : Set G)) :
    S ≤ normalizer (residualIn P : Set G) :=
  hP.trans (normalizer_le_normalizer_characteristic_image P (solvableResidual P))

/-- The actual Y_z condition and the invariance conclusion of 13.6.14
imply movement of z, through the original star kernel. -/
theorem moves_of_invariant_Yz (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G)) :
    ¬ K ≤ centralizer ({z} : Set G) := by
  have h := (invariant_component_consequences K L T z v hK hn).1.2
  exact fun hc => h ((starPreimage_starImage_centralizes_seed_iff z v K hK.1.1).mpr hc)

/-- The plus image of an actual residual preimage, identified through the
literal plus map and the specified model equivalence. -/
noncomputable def plusResidualEquiv [Finite G] {D : Type*} [Group D]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : plusImage K L T z v hL hz K ≃* D) (P : Subgroup D) :
    plusImage K L T z v hL hz
      (residualIn (preimageIn K (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) P)) ≃*
        residualIn P := by
  let c := componentPlusMap K L T z v hL hz
  let f := e.toMonoidHom.comp c
  let R := residualIn (preimageIn K f P)
  let C := (R.subgroupOf K).map c
  have hR : R ≤ K := (map_subtype_le _).trans (preimageIn_le K f P)
  have hC : C.map (plusImage K L T z v hL hz K).subtype =
      plusImage K L T z v hL hz R := componentPlusMap_subgroup K L T R z v hL hz hR
  have hM : C.map e.toMonoidHom = residualIn P := by
    rw [show C = (R.subgroupOf K).map c from rfl, map_map]
    exact residualIn_preimage_image K f
      (e.surjective.comp (componentPlusMap_surjective K L T z v hL hz)) P
  exact ((C.equivMapOfInjective _ (plusImage K L T z v hL hz K).subtype_injective).trans
    (MulEquiv.subgroupCongr hC)).symm.trans
      ((e.subgroupMap C).trans (MulEquiv.subgroupCongr hM))

open scoped MatrixGroups
variable (F : Type*) [Field F] [Finite F]

/-- Pullback of the actual point parabolic along K → K⁺ ≃ SL₃(F). -/
def pointPreimage (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F)) : Subgroup G :=
  preimageIn K (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz))
    (Matrix.PSL3.LinearThree.pointParabolicSL F)

/-- Pullback of the actual line parabolic along the same map. -/
def linePreimage (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F)) : Subgroup G :=
  preimageIn K (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz))
    (Matrix.PSL3.LinearThree.lineParabolicSL F)

theorem pointPreimage_maximal (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F)) :
    IsCoatom ((pointPreimage F K L T z v hL hz e).subgroupOf K) := by
  rw [pointPreimage, preimageIn, subgroupOf,
    comap_map_eq_self_of_injective K.subtype_injective]
  exact Subgroup.isCoatom_comap_of_surjective
    (e.surjective.comp (componentPlusMap_surjective K L T z v hL hz))
    (Matrix.PSL3.LinearThree.pointParabolicSL_isCoatom F)

theorem linePreimage_maximal (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F)) :
    IsCoatom ((linePreimage F K L T z v hL hz e).subgroupOf K) := by
  rw [linePreimage, preimageIn, subgroupOf,
    comap_map_eq_self_of_injective K.subtype_injective]
  exact Subgroup.isCoatom_comap_of_surjective
    (e.surjective.comp (componentPlusMap_surjective K L T z v hL hz))
    (Matrix.PSL3.LinearThree.lineParabolicSL_isCoatom F)

/-- Intrinsic source movement selects one of the constructed maximal
parabolics. Generation is proved in SL₃ and transferred through plusMk. -/
theorem moving_flag_residual [Finite G] (hcard : 4 ≤ Nat.card F)
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F)) :
    ∃ P ∈ ({pointPreimage F K L T z v hL hz e,
      linePreimage F K L T z v hL hz e} : Set (Subgroup G)),
      P ≤ K ∧ IsCoatom (P.subgroupOf K) ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) := by
  have hg := plus_generation_of_model_residuals K L T z v hL hz e
    (Matrix.PSL3.LinearThree.pointParabolicSL F)
    (Matrix.PSL3.LinearThree.lineParabolicSL F)
    (Matrix.PSL3.LinearThree.parabolicResidualsSL_sup_eq_top F hcard)
  obtain ⟨P, hP, hPK, hm⟩ := moving_residual_of_plus_generation K L T
    (pointPreimage F K L T z v hL hz e) (linePreimage F K L T z v hL hz e)
    z v hL hz (preimageIn_le _ _ _) (preimageIn_le _ _ _) hg
    (moves_of_invariant_Yz K L T z v hK hn)
  refine ⟨P, hP, hPK, ?_, hm⟩
  rcases hP with hP | hP
  · subst P
    exact pointPreimage_maximal F K L T z v hL hz e
  · have he : P = linePreimage F K L T z v hL hz e := Set.mem_singleton_iff.mp hP
    subst P
    exact linePreimage_maximal F K L T z v hL hz e

variable [CharP F 2]

/-- The literal plus core quotient of the point-preimage residual. No
claim about the intrinsic kernel of that preimage is made here. -/
noncomputable def pointPreimagePlusCoreEquiv [Finite G] (hcard : 4 ≤ Nat.card F)
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F)) :
    (plusImage K L T z v hL hz (residualIn (pointPreimage F K L T z v hL hz e)) ⧸
      pCore 2 (plusImage K L T z v hL hz
        (residualIn (pointPreimage F K L T z v hL hz e)))) ≃* PSL(2, F) :=
  let eR := plusResidualEquiv K L T z v hL hz e (Matrix.PSL3.LinearThree.pointParabolicSL F)
  (QuotientGroup.congr _ _ eR (pCore_map_iso 2 eR)).trans
    (Matrix.PSL3.LinearThree.pointParabolicSLResidualCoreEquiv F hcard)

/-- The same quotient calculation for the line-preimage residual. -/
noncomputable def linePreimagePlusCoreEquiv [Finite G] (hcard : 4 ≤ Nat.card F)
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F)) :
    (plusImage K L T z v hL hz (residualIn (linePreimage F K L T z v hL hz e)) ⧸
      pCore 2 (plusImage K L T z v hL hz
        (residualIn (linePreimage F K L T z v hL hz e)))) ≃* PSL(2, F) :=
  let eR := plusResidualEquiv K L T z v hL hz e (Matrix.PSL3.LinearThree.lineParabolicSL F)
  (QuotientGroup.congr _ _ eR (pCore_map_iso 2 eR)).trans
    (Matrix.PSL3.LinearThree.lineParabolicSLResidualCoreEquiv F hcard)

omit [CharP F 2] in
/-- Marking the image of Tᵥ ∩ K in the standard Sylow places that actual
intersection in both constructed parabolics. -/
theorem marked_intersection_le (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hmark : ((Tv T v).subgroupOf K).map
      (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) ≤
        Matrix.PSL3.LinearThree.unipotentSL F) :
    Tv T v ⊓ K ≤ pointPreimage F K L T z v hL hz e ∧
      Tv T v ⊓ K ≤ linePreimage F K L T z v hL hz e := by
  constructor
  · intro x hx
    refine mem_map.mpr ⟨⟨x, hx.2⟩, ?_, rfl⟩
    exact ((Matrix.PSL3.LinearThree.unipotentSL_le_borelSL F).trans inf_le_left)
      (hmark (mem_map_of_mem _ (show (⟨x, hx.2⟩ : K) ∈ (Tv T v).subgroupOf K from hx.1)))
  · intro x hx
    refine mem_map.mpr ⟨⟨x, hx.2⟩, ?_, rfl⟩
    exact ((Matrix.PSL3.LinearThree.unipotentSL_le_borelSL F).trans inf_le_right)
      (hmark (mem_map_of_mem _ (show (⟨x, hx.2⟩ : K) ∈ (Tv T v).subgroupOf K from hx.1)))

omit F [Field F] [Finite F] [CharP F 2] in
/-- The local SQTK input is inherited from the actual involution
centralizer, retaining the complete ambient K-group hypothesis. -/
theorem residual_join_sqtk [Finite G] {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G) (T P : Subgroup G) (v : G)
    (hv : orderOf v = 2) (hP : P ≤ Gv v) :
    IsSQTK 𝒦 (residualIn P ⊔ Tv T v : Subgroup G) := by
  have hH : residualIn P ⊔ Tv T v ≤ Gv v :=
    sup_le ((map_subtype_le _).trans hP) inf_le_right
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hH)).mp
    ((hG.involution_centralizer_sqtk hv).subgroup
      ((residualIn P ⊔ Tv T v).subgroupOf (Gv v)))

omit F [Field F] [Finite F] [CharP F 2] in
/-- The earlier characteristic-two conclusion for Gᵥ passes to the
residual joined to Tᵥ because Tᵥ is the actual Sylow in Gᵥ. -/
theorem residual_join_characteristic_two [Finite G]
    (T P : Subgroup G) (v : G) (hP : P ≤ Gv v)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v)) :
    Theory.GroupTheory.generalizedFitting (residualIn P ⊔ Tv T v : Subgroup G) =
      pCore 2 (residualIn P ⊔ Tv T v : Subgroup G) := by
  let H := residualIn P ⊔ Tv T v
  have hH : H ≤ Gv v := sup_le ((map_subtype_le _).trans hP) inf_le_right
  obtain ⟨S, hS⟩ := hSylow
  have hSH : (S : Subgroup (Gv v)).map (Gv v).subtype ≤ H :=
    hS ▸ le_sup_right
  have hchar : HasCharacteristicTwo (Gv v) := by
    change centralizer (pCore 2 (Gv v) : Set (Gv v)) ≤ pCore 2 (Gv v)
    rw [← hf]
    exact Theory.GroupTheory.centralizer_generalizedFitting_le (Gv v)
  have hc : HasCharacteristicTwo (H.subgroupOf (Gv v)) :=
    centralizer_pCore_le_of_sylow_le S (H.subgroupOf (Gv v))
      (map_le_iff_le_comap.mp hSH) hchar
  exact Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
    (hc.of_equiv (subgroupOfEquivOfLe hH))

/-- Source-shaped selection over a field of order 2ᵐ, m > 1. The marked
Sylow condition locates both parabolics; movement and the literal PSL₂
plus-core quotient are derived. The normalizer and marked-module
obstructions are separate obligations. -/
theorem moving_marked_flag_residual [Finite G] {m : ℕ}
    (hm : 1 < m) (hF : Nat.card F = 2 ^ m)
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hmark : ((Tv T v).subgroupOf K).map
      (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) ≤
        Matrix.PSL3.LinearThree.unipotentSL F) :
    ∃ P ∈ ({pointPreimage F K L T z v hL hz e,
      linePreimage F K L T z v hL hz e} : Set (Subgroup G)),
      P ≤ K ∧ IsCoatom (P.subgroupOf K) ∧ Tv T v ⊓ K ≤ P ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) ∧
        Nonempty ((plusImage K L T z v hL hz (residualIn P) ⧸
          pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2, F)) := by
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 4 = (2 : ℕ) ^ 2 by decide).le.trans
      (pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) hm)
  obtain ⟨P, hP, hPK, hmax, hmove⟩ := moving_flag_residual F hcard K L T z v hL hz hK hn e
  have hmark' := marked_intersection_le F K L T z v hL hz e hmark
  refine ⟨P, hP, hPK, hmax, ?_, hmove, ?_⟩
  · rcases hP with hP | hP
    · subst P
      exact hmark'.1
    · exact (Set.mem_singleton_iff.mp hP) ▸ hmark'.2
  · rcases hP with hP | hP
    · subst P
      exact ⟨pointPreimagePlusCoreEquiv F hcard K L T z v hL hz e⟩
    · have he : P = linePreimage F K L T z v hL hz e := Set.mem_singleton_iff.mp hP
      subst P
      exact ⟨linePreimagePlusCoreEquiv F hcard K L T z v hL hz e⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree
end
