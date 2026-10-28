module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.QuotientIdentification.Centralizer
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.QuotientIdentification.Marked

/-!
# Compatible quotient recognition for the original line normalizer

This conditional interface uses the preceding source data and the descended
identity `M_E = Y_E T_E`. The original `I₀` contributes its recognized index;
its action kernel is never identified with `Q_E`. The initial decomposition
marks `⟨Y_E,τ⟩` as the first factor and the actual centralizer image as the
second, whose type is then proved using the three-coset action.

The maximum-elementary argument also supplies an actual involution in
`J(R)` outside `Q_E`, ready for the commutator calculation. The two residual
quotients and their commutator lift are further obligations; this module
alone is not source Lemma 15.3.67.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification
variable {G : Type*} [Group G]

/-- The preceding geometric and recognition inputs consumed by the quotient proof.
The local core equation is the action-kernel clause of 15.3.66(5), and
`local_product` is the separately proved descent identity. The initially
marked second factor has no assumed isomorphism type. -/
structure Inputs (M Y T V E : Subgroup G) where
  line_le : E ≤ V
  sylow : Sylow 2 (lineNormalizer E)
  sylow_map : (sylow : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E
  T_le_M : T ≤ M
  thompson_eq : elementaryAbelianMaxJ (lineT T E) =
    elementaryAbelianMaxJ (T ⊓ centralizer (V : Set G))
  core_centralizes_line : lineQ E ≤ centralizer (E : Set G)
  normalizer_V_le_M : normalizer (V : Set G) ≤ M
  product_with_I : (lineNormalizer E : Set G) = (lineM M E : Set G) * (lineI E : Set G)
  I0_index : (lineI0 T V E ⊓ lineM M E).relIndex (lineI0 T V E) = 3
  local_product : lineM M E = lineY Y E ⊔ lineT T E
  local_core : (lineY Y E ⊔ lineT T E : Subgroup G).pCoreIn 2 =
    (lineY Y E ⊔ lineT T E) ⊓ centralizer (E : Set G)
  Y_normal : ((lineY Y E).subgroupOf (lineNormalizer E)).Normal
  marked : MarkedDecomposition Y T E

variable {M Y T V E : Subgroup G}

/-- The second `S₃` is derived from the original index, core and Thompson data. -/
noncomputable def originalCentralizerEquiv [Finite G] [IsMulCommutative V]
    (s : Inputs M Y T V E) :
    (centralizer (E : Set G) ⧸ pCore 2 (centralizer (E : Set G))) ≃* Equiv.Perm (Fin 3) :=
  Classical.choice (centralizer_core_quotient M T V E s.line_le s.sylow s.sylow_map
    s.T_le_M s.thompson_eq s.core_centralizes_line s.normalizer_V_le_M s.product_with_I
    s.I0_index (centralizer_intersection_isTwo_of_core M Y T E s.local_product s.local_core))

/-- The actual original core quotient, preserving the earlier marked factors. -/
noncomputable def originalProductEquiv [Finite G] [IsMulCommutative V]
    (s : Inputs M Y T V E) :
    (lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) ≃*
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
  markedProductEquiv Y T E s.marked (originalCentralizerEquiv s)

/-- The surjection from the original normalizer to its two marked `S₃` factors. -/
noncomputable def originalProductMap [Finite G] [IsMulCommutative V]
    (s : Inputs M Y T V E) :
    lineNormalizer E →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
  (originalProductEquiv s).toMonoidHom.comp (quotientMap E)

/-- Both marked factors are covered by the original quotient map. -/
theorem originalProductMap_surjective [Finite G] [IsMulCommutative V]
    (s : Inputs M Y T V E) : Function.Surjective (originalProductMap s) :=
  (originalProductEquiv s).surjective.comp (QuotientGroup.mk'_surjective _)

/-- Its kernel is the intrinsic core of the original `G_E`. -/
theorem originalProductMap_ker [Finite G] [IsMulCommutative V]
    (s : Inputs M Y T V E) : (originalProductMap s).ker = pCore 2 (lineNormalizer E) := by
  ext x
  change originalProductEquiv s (quotientMap E x) = 1 ↔ _
  rw [← (originalProductEquiv s).map_one, (originalProductEquiv s).injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

/-- In ambient notation, the product-map kernel is exactly the original `Q_E`. -/
theorem originalProductMap_ker_ambient [Finite G] [IsMulCommutative V]
    (s : Inputs M Y T V E) :
    (originalProductMap s).ker.map (lineNormalizer E).subtype = lineQ E := by
  rw [originalProductMap_ker]
  rfl

/-- The original first marked coordinate is preserved, not chosen anew. -/
theorem originalProductEquiv_first_coordinate [Finite G] [IsMulCommutative V]
    (s : Inputs M Y T V E) (q : lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) :
    (originalProductEquiv s q).1 = (s.marked.equiv q).1 := rfl

/-- The originally marked `⟨Y_E,τ⟩` has precisely the first full factor as image. -/
theorem originalProductMap_first_factor [Finite G] [IsMulCommutative V]
    (s : Inputs M Y T V E) :
    ((lineY Y E ⊔ zpowers s.marked.tau).subgroupOf (lineNormalizer E)).map
      (originalProductMap s) = (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥ :=
  markedProductEquiv_first_factor Y T E s.marked (originalCentralizerEquiv s)

/-- Centralizer elements go to the second factor through their intrinsic quotient. -/
theorem originalProductMap_centralizer [Finite G] [IsMulCommutative V]
    (s : Inputs M Y T V E) (c : centralizer (E : Set G)) :
    originalProductMap s (inclusion (centralizer_le_normalizer (E : Set G)) c) =
      (1, originalCentralizerEquiv s (QuotientGroup.mk' (pCore 2 (centralizer (E : Set G))) c)) :=
  markedProductEquiv_centralizer Y T E s.marked (originalCentralizerEquiv s) c

/-- The original centralizer image is precisely the second full `S₃` factor. -/
theorem originalProductMap_second_factor [Finite G] [IsMulCommutative V]
    (s : Inputs M Y T V E) :
    ((centralizer (E : Set G)).subgroupOf (lineNormalizer E)).map (originalProductMap s) =
      (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod ⊤ := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    have he := originalProductMap_centralizer s (⟨c, hc⟩ : centralizer (E : Set G))
    exact ⟨congrArg Prod.fst he, mem_top _⟩
  · rintro ⟨hx, _⟩
    obtain ⟨c, hc⟩ := ((originalCentralizerEquiv s).surjective.comp
      (QuotientGroup.mk'_surjective (pCore 2 (centralizer (E : Set G))))) x.2
    refine ⟨inclusion (centralizer_le_normalizer (E : Set G)) c, c.property, ?_⟩
    simp only [Function.comp_apply] at hc
    rw [originalProductMap_centralizer, hc]
    exact Prod.ext hx.symm rfl

/-- The first coordinate has the actual line centralizer as kernel. -/
theorem originalProductMap_fst_ker [Finite G] [IsMulCommutative V]
    (s : Inputs M Y T V E) :
    ((MonoidHom.fst _ _).comp (originalProductMap s)).ker =
      (centralizer (E : Set G)).subgroupOf (lineNormalizer E) := by
  have hcore : (originalProductMap s).ker ≤
      (centralizer (E : Set G)).subgroupOf (lineNormalizer E) := by
    rw [originalProductMap_ker]
    intro x hx
    exact s.core_centralizes_line (mem_map_of_mem (lineNormalizer E).subtype hx)
  have he : ((⊥ : Subgroup (Equiv.Perm (Fin 3))).prod ⊤).comap
      (originalProductMap s) = (centralizer (E : Set G)).subgroupOf (lineNormalizer E) := by
    rw [← originalProductMap_second_factor s, comap_map_eq, sup_of_le_left hcore]
  rw [← he]
  ext x
  exact (and_iff_left (mem_top _)).symm

/-- The second coordinate kernel is the preimage of the initial first factor;
the original core is retained in that preimage. -/
theorem originalProductMap_snd_ker [Finite G] [IsMulCommutative V]
    (s : Inputs M Y T V E) :
    ((MonoidHom.snd _ _).comp (originalProductMap s)).ker =
      (lineY Y E ⊔ zpowers s.marked.tau).subgroupOf (lineNormalizer E) ⊔
        pCore 2 (lineNormalizer E) := by
  have he : ((⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥).comap
      (originalProductMap s) =
      (lineY Y E ⊔ zpowers s.marked.tau).subgroupOf (lineNormalizer E) ⊔
        pCore 2 (lineNormalizer E) := by
    rw [← originalProductMap_first_factor s, comap_map_eq, originalProductMap_ker]
  rw [← he]
  ext x
  exact (and_iff_right (mem_top _)).symm

/-- The two original residuals intersect only inside the original two-core. -/
theorem lineY_inf_lineX_le_lineQ [Finite G] [IsMulCommutative V]
    (s : Inputs M Y T V E) : lineY Y E ⊓ lineX E ≤ lineQ E := by
  intro x hx
  let xH : lineNormalizer E := ⟨x, (lineY_le Y E hx.1).2⟩
  have hfirst : originalProductMap s xH ∈ (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥ := by
    rw [← originalProductMap_first_factor s]
    exact mem_map_of_mem _ (show xH ∈
      (lineY Y E ⊔ zpowers s.marked.tau).subgroupOf (lineNormalizer E) from
      mem_sup_left hx.1)
  have hsecond : originalProductMap s xH ∈ (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod ⊤ := by
    rw [← originalProductMap_second_factor s]
    exact mem_map_of_mem _ (show xH ∈
      (centralizer (E : Set G)).subgroupOf (lineNormalizer E) from lineX_le_centralizer E hx.2)
  have hk : xH ∈ (originalProductMap s).ker := Prod.ext hsecond.1 hfirst.2
  rw [originalProductMap_ker] at hk
  exact mem_map_of_mem (lineNormalizer E).subtype hk

/-- Restricting the recognized product map to a relatively normal subgroup
retains exactly its intrinsic two-core as kernel. -/
theorem originalProductMap_restrict_ker [Finite G] [IsMulCommutative V]
    (s : Inputs M Y T V E) (A : Subgroup G) (hA : A ≤ lineNormalizer E)
    (hn : (A.subgroupOf (lineNormalizer E)).Normal) :
    ((originalProductMap s).comp (inclusion hA)).ker = pCore 2 A := by
  calc
    _ = (restrictedQuotient E A hA).ker := by
      ext x
      change originalProductEquiv s (restrictedQuotient E A hA x) = 1 ↔
        restrictedQuotient E A hA x = 1
      rw [← (originalProductEquiv s).map_one, (originalProductEquiv s).injective.eq_iff]
    _ = _ := restrictedQuotient_ker E A hA hn

/-- The residual intersection is exactly the intersection of their two-cores. -/
theorem lineY_inf_lineX_eq_core_intersection [Finite G] [IsMulCommutative V]
    (s : Inputs M Y T V E) :
    lineY Y E ⊓ lineX E = (lineY Y E).pCoreIn 2 ⊓ (lineX E).pCoreIn 2 := by
  rw [lineY_twoCore Y E s.Y_normal, lineX_twoCore]
  apply le_antisymm
  · intro x hx
    have hq := lineY_inf_lineX_le_lineQ s hx
    exact ⟨⟨hx.1, hq⟩, ⟨hx.2, hq⟩⟩
  · exact inf_le_inf inf_le_left inf_le_left

/-- An actual involution among the maximum-elementary Thompson generators
survives the original quotient; this supplies the nontrivial second-factor action. -/
theorem exists_thompson_involution [Finite G] (s : Inputs M Y T V E) :
    ∃ j ∈ elementaryAbelianMaxJ (T ⊓ centralizer (V : Set G)), j ^ 2 = 1 ∧ j ∉ lineQ E := by
  classical
  by_contra hn
  push Not at hn
  apply centralizerThompson_not_le_lineQ M T V E s.line_le s.sylow s.sylow_map
    s.T_le_M s.thompson_eq s.I0_index
  apply sSup_le
  intro A hA a ha
  let : IsElementaryAbelian 2 A := hA.2.1
  exact hn a ((le_sSup hA) ha) (elemPow_eq_one_of_isElementaryAbelian a ha)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification
