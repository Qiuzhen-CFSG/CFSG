module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear

/-!
# The two-core of the original linear point fixer

The original natural projection identifies C_L(V₁) with the preimage of
the vector stabilizer. The actual L₁ has this same image, so adjoining R₁
absorbs the two-core kernel and gives C_L(V₁)R₁=L₁R₁. Normality in L₁T
then identifies the two-core of this subgroup with R₁.

Together with the Sylow-omega comparison, this excludes the two central
layer rows of C.1.34 on the original point. The calculation retains the
full SL₃ quotient and includes q=4. The remaining doubled-natural row is
handled in Doubled; the intrinsic classification remains external.
Source: Aschbacher--Smith C.1.34, printed pp.136--137, and 11.1.5, p.765.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear
open PointCohomology.PointGeometry.SL3Core
open Matrix.PSL3.PointRadicalGeneration Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
  (f : InvariantFlag (.sl3 m))

private theorem standard_point_fixer (g : SL(3,S.field.Carrier)) :
    (∀ x ∈ standardPoint (F := S.field.Carrier), g.val *ᵥ x = x) ↔
      g ∈ pointLocalSL S.field.Carrier := by
  rw [mem_pointLocalSL_iff]
  constructor
  · intro h
    have he := h ![1,0,0] ((mem_standardPoint _).mpr (by simp))
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    have h2 := congrFun he 2
    simpa [mulVec,dotProduct,Fin.sum_univ_three] using And.intro h0 (And.intro h1 h2)
  · rintro ⟨h0,h1,h2⟩ x hx
    obtain ⟨hx1,hx2⟩ := (mem_standardPoint _).mp hx
    ext i
    fin_cases i <;> simp [mulVec,dotProduct,Fin.sum_univ_three,hx1,hx2,h0,h1,h2]

private theorem point_fixer_model (g : SL(3,S.field.Carrier)) :
    (∀ x ∈ f.space 0, g.val *ᵥ x = x) ↔
      g ∈ componentImage D S m (f.Li 0) := by
  obtain ⟨a,ha⟩ := exists_standardPoint_conjugator (f.space 0) (f.dimension 0)
  rw [componentImage_residual_conjugate D S m f a ha]
  let ρ := specialLinearNatural (k := S.field.Carrier) 3
  constructor
  · intro h
    have hg : a*g*a⁻¹ ∈ pointLocalSL S.field.Carrier := by
      apply (standard_point_fixer D S _).mp
      intro x hx
      have hx' : ρ a⁻¹ x ∈ f.space 0 := by
        rw [←ha,mem_conjugatePoint]
        change ρ a (ρ a⁻¹ x) ∈ standardPoint
        rw [Representation.self_inv_apply]
        exact hx
      have hh := congrArg (fun y => ρ a y) (h (ρ a⁻¹ x) hx')
      change ρ a (ρ g (ρ a⁻¹ x)) = ρ a (ρ a⁻¹ x) at hh
      change ρ (a*g*a⁻¹) x = x
      rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply]
      simpa only [Representation.self_inv_apply] using hh
    refine ⟨a*g*a⁻¹,hg,?_⟩
    simp [mul_assoc]
  · rintro ⟨g,hg,rfl⟩ x hx
    have hx' : ρ a x ∈ standardPoint := (mem_conjugatePoint _ a x).mp (ha ▸ hx)
    have hh := congrArg (fun y => ρ a⁻¹ y) ((standard_point_fixer D S g).mpr hg _ hx')
    change ρ a⁻¹ (ρ g (ρ a x)) = ρ a⁻¹ (ρ a x) at hh
    change ρ (a⁻¹*g*a⁻¹⁻¹) x = x
    rw [inv_inv,map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply]
    simpa only [Representation.inv_self_apply] using hh

/-- Fixation of the original point is detected by its literal component projection. -/
theorem point_fixer_projection_iff (l : L) :
    (l : G) ∈ centralizer (f.Vi 0 : Set G) ↔
      componentMap D S m l ∈ componentImage D S m (f.Li 0) := by
  rw [← point_fixer_model D S m f]
  constructor
  · intro h x hx
    obtain ⟨v,hv⟩ := (Coordinates.sl3 m).projection_surjective (Multiplicative.ofAdd x)
    have hvp : (v : G) ∈ f.Vi 0 := by
      apply ((Coordinates.sl3 m).mem_preimage _ v).mpr
      change ((Coordinates.sl3 m).projection v).toAdd ∈ f.space 0
      rw [hv]
      exact hx
    have hh : V.normalizerMonoidHom (inclusion D.normalizes l) v = v := by
      apply Subtype.ext
      change (l : G) * v * (l : G)⁻¹ = v
      rw [←h v hvp,mul_inv_cancel_right]
    have he := (projection_fixed_iff D S m l v).mpr hh
    rw [hv] at he
    exact he
  · intro h v hv
    let v' : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
    have hx := h _ (((Coordinates.sl3 m).mem_preimage _ v').mp hv)
    have he := congrArg Subtype.val ((projection_fixed_iff D S m l v').mp hx)
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The perfect point local centralizes the actual point, also at q=4. -/
theorem local_le_point_fixer : f.Li 0 ≤ L ⊓ centralizer (f.Vi 0 : Set G) := by
  intro l hl
  have hlL : l ∈ L := ((localResidual_le _).trans inf_le_left) hl
  exact ⟨hlL,(point_fixer_projection_iff D S m f ⟨l,hlL⟩).mpr
    ⟨⟨l,hlL⟩,hl,rfl⟩⟩

/-- Lifting the same quotient image leaves only the original two-core kernel. -/
theorem point_fixer_le_local_join_componentCore :
    L ⊓ centralizer (f.Vi 0 : Set G) ≤ f.Li 0 ⊔ L.pCoreIn 2 := by
  rintro l ⟨hl,hfix⟩
  obtain ⟨u,hu,he⟩ := (point_fixer_projection_iff D S m f ⟨l,hl⟩).mp hfix
  have hk : (⟨l,hl⟩ : L)*u⁻¹ ∈ pCore 2 L := by
    rw [← componentMap_ker D S m]
    change componentMap D S m ((⟨l,hl⟩ : L)*u⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hh := (f.Li 0 ⊔ L.pCoreIn 2).mul_mem
    (mem_sup_right (mem_map_of_mem L.subtype hk)) (mem_sup_left hu)
  change l * (u : G)⁻¹ * (u : G) ∈ _ at hh
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

/-- The full component kernel lies in the original point radical. -/
theorem componentCore_le_radical : L.pCoreIn 2 ≤ f.Ri 0 := by
  have hQ : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  apply hQ.trans
  intro q hq
  exact inf_pCoreIn_le_of_le 2
    (sup_le (((localResidual_le _).trans inf_le_left).trans le_sup_left) le_sup_right)
    ⟨mem_sup_right (hQT hq),hq⟩

/-- The literal point fixer times R₁ is exactly L₁R₁. -/
theorem point_fixer_join_radical :
    (L ⊓ centralizer (f.Vi 0 : Set G)) ⊔ f.Ri 0 = f.Li 0 ⊔ f.Ri 0 := by
  apply le_antisymm
  · exact sup_le ((point_fixer_le_local_join_componentCore D S m f).trans
      (sup_le_sup_left (componentCore_le_radical D S m f) _)) le_sup_right
  · exact sup_le_sup_right (local_le_point_fixer D S m f) _

/-- The original point-fixer core calculation used to select C.1.34's block row. -/
theorem point_fixer_core :
    ((L ⊓ centralizer (f.Vi 0 : Set G)) ⊔ f.Ri 0).pCoreIn 2 = f.Ri 0 := by
  rw [point_fixer_join_radical D S m f]
  have hRP : f.Ri 0 ≤ f.Li 0 ⊔ (T : Subgroup G) := pCoreIn_le _ _
  have hnorm : f.Li 0 ⊔ (T : Subgroup G) ≤ normalizer (f.Ri 0 : Set G) :=
    (f.Li 0 ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  apply le_antisymm
  · exact pCoreIn_mono_of_normalizes
      (sup_le le_sup_left ((localRadical_le_sylow _).trans le_sup_right))
      (sup_le (le_sup_left.trans (f.Li 0 ⊔ f.Ri 0).le_normalizer)
        ((le_inf (f.sylow_normalizes_Li 0) (sylow_normalizes_Ri f 0)).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)))
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) le_sup_right
      ((sup_le le_sup_left hRP).trans hnorm)

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
/-- On the actual point Sylow, C.1.34(3)--(4) cannot occur. The remaining
classification input is intrinsic; no radical or centrality premise is added. -/
theorem alternatives_block_or_double
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (h : MSModuleAlternatives L (f.Ri 0) ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0))
      S.field.degree S.field.Carrier e) :
    ChapterC.IsSL3EvenBlock L S.field.degree ∨
    (HasSectionModel L (msQ L (f.Ri 0)) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := S.field.Carrier) 3).prod
        (Representation.specialLinearNatural (k := S.field.Carrier) 3)) ∧
      MSNotCentralizerCore L (f.Ri 0) ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0))) := by
  rcases alternatives_point_fixer_core D S m f e h with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (h (point_fixer_core D S m f).symm).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear
