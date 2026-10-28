module
public import Theory.AtlasPort.LinearGroups.G2.CubicCartan
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import Theory.GroupTheory.PerfectSolvableSectionLift
public import Theory.GroupTheory.CommutatorPreimage.Membership
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TorusPropagation

/-!
# The original chosen Cartan factor in the G₂ tensor exclusion

Full-Sylow local components are placed in the two literal parabolic residuals
without separate conjugation choices. A nonzero natural vector fixed by the
common Sylow and the old component selects the long residual; a distinct local
component is the short one. The chosen cubic factor inside that short component
centralizes the old component modulo its two-core by the concrete calculation.

The actual model map may be defined only on the source overgroup. Its restricted
two-kernel reflects the old two-core, while the original normalizer and Cartan
orbit remain in the larger ambient group. The resulting section centralization
feeds the existing Cartan propagation contradiction with the original cubic.

Source: Aschbacher–Smith B.4.6(14), printed p.88, and 9.3.9, printed p.734.
The original Cartan construction, common Sylow/model marking and orbit equality
remain explicit; no model-centralization assumption is used.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter4 Atlas.G2 Atlas.G2.LieParabolicSetup
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings.FiveLocalFF

theorem source_g2_local_at_standard_sylow (hF : Nat.card F = 4)
    (B : Subgroup (Model F)) (hB : B ∈ localCComponents (Atlas.G2.LieParabolicSetup.sylow (F := F)))
    (hproper : B ≠ ⊤) : B = local₁ ∨ B = local₂ := by
  have hq : 2 < Nat.card F := by rw [hF]; decide
  let : IsSimpleGroup (Model F) := Atlas.G2.isSimple hq
  have hjoin : B ⊔ unipotent ≠ ⊤ := by
    intro ht
    have hc : B.IsCComponent := by
      have hm := hB
      change (B.subgroupOf (B ⊔ unipotent)).IsCComponent at hm
      rw [ht] at hm
      simpa only [map_subgroupOf_eq_of_le le_top] using hm.map_subtype (.top)
    exact (hc.subnormal.eq_bot_or_top_of_isSimpleGroup inferInstance).elim hc.ne_bot hproper
  have hp := ProperSylowOvergroups.le_parabolic (B ⊔ unipotent)
    le_sup_right (lt_top_iff_ne_top.mpr hjoin)
  let := hB.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (Atlas.G2.LieParabolicSetup.sylow (F := F) : Subgroup (Model F)) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  rcases hp with hp | hp
  · left
    let := local₁_isPerfect hq
    apply local_eq_of_sl2_core_quotient local₁ hq
      (local₁CoreQuotientEquivPSL.trans longSLEquivPSL.symm)
      (Atlas.G2.LieParabolicSetup.sylow (F := F)) B hB
    · rw [←HigherFieldResiduals.parabolic₁_residual hq]
      exact le_map_solvableResidual_of_isPerfect _ parabolic₁ (le_sup_left.trans hp)
    · exact unipotent_le_local₁
  · right
    let := local₂_isPerfect hq
    apply local_eq_of_sl2_core_quotient local₂ hq
      (local₂CoreQuotientEquivPSL.trans longSLEquivPSL.symm)
      (Atlas.G2.LieParabolicSetup.sylow (F := F)) B hB
    · rw [←HigherFieldResiduals.parabolic₂_residual hq]
      exact le_map_solvableResidual_of_isPerfect _ parabolic₂ (le_sup_left.trans hp)
    · exact unipotent_le_local₂

theorem source_g2_fixed_local_is_long (hF : Nat.card F = 4)
    (B : Subgroup (Model F)) (hB : B ∈ localCComponents (Atlas.G2.LieParabolicSetup.sylow (F := F)))
    (hproper : B ≠ ⊤) (v : Natural.Space F) (hv : v ≠ 0)
    (hU : ∀ u ∈ unipotent (K := F), Natural.action F u v = v)
    (hfix : ∀ b ∈ B, Natural.action F b v = v) : B = local₂ := by
  let w := Atlas.G2.Restricted.NaturalCoordinates.equiv F v
  have hw : w ≠ 0 := by
    intro he
    exact hv ((Atlas.G2.Restricted.NaturalCoordinates.equiv F).map_eq_zero_iff.mp he)
  have haction (g : Model F) (hg : Natural.action F g v = v) :
      Atlas.G2.Restricted.NaturalCoordinates.action F g w = w := by
    change Atlas.G2.Restricted.NaturalCoordinates.equiv F
      (Natural.action F g ((Atlas.G2.Restricted.NaturalCoordinates.equiv F).symm w)) = w
    simp only [w,LinearEquiv.symm_apply_apply,hg]
  exact Atlas.G2.CubicCartan.long_local_of_fixes_nonzero_unipotent_fixed B
    (source_g2_local_at_standard_sylow hF B hB hproper) w hw
    (fun u hu => haction u (hU u hu)) (fun b hb => haction b (hfix b hb))

theorem source_tensor_g2_chosen_cubic_factor
    (hF : Nat.card F = 4) (f : G →* Model F) (K E : Subgroup G)
    (hK : K.map f = local₂) (hE : E.map f ≤ local₁)
    (hEN : E.map f ≤ normalizer (unipotent (K := F) : Set (Model F)))
    (hEK : E ≤ normalizer (K : Set G))
    (hk : IsPGroup 2 (f.subgroupMap K).ker)
    (h3 : ∀ x ∈ E, x ^ 3 = 1) : E ≤ sectionCentralizer K := by
  apply (le_sectionCentralizer_iff E K).mpr
  refine ⟨hEK,commutator_le.mpr ?_⟩
  intro x hx k hmem
  have hxmap := mem_map_of_mem f hx
  have hcalc := Atlas.G2.CubicCartan.short_normalizer_cubic_commutators hF (f x)
    (hE hxmap) (hEN hxmap) (by rw [←map_pow,h3 x hx,map_one])
  apply mem_pCoreIn_of_map_mem f K hk
  · exact le_normalizer_iff_commutator_le_right.mp hEK (commutator_mem_commutator hx hmem)
  · rw [map_commutatorElement,hK]
    exact hcalc.2 (f k) (hK ▸ mem_map_of_mem f hmem)

theorem source_tensor_g2_chosen_cartan_contradiction
    (hF : Nat.card F = 4) (f : G →* Model F) (K D E N : Subgroup G)
    (hK : K.map f = local₂) (hE : E.map f ≤ local₁)
    (hEN : E.map f ≤ normalizer (unipotent (K := F) : Set (Model F)))
    (hEK : E ≤ normalizer (K : Set G))
    (hk : IsPGroup 2 (f.subgroupMap K).ker)
    (h3 : ∀ x ∈ E, x ^ 3 = 1)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hNK : N ≤ normalizer (K : Set G)) (hgen : componentOrbit E N = D)
    (b : G) (hbD : b ∈ D) (hbK : b ∈ K) (hb3 : orderOf b = 3) : False :=
  source_tensor_torus_cubic_contradiction K D E N eK hNK
    (source_tensor_g2_chosen_cubic_factor hF f K E hK hE hEN hEK hk h3)
    hgen b hbD hbK hb3


theorem source_tensor_g2_original_chosen_factor
    (hF : Nat.card F = 4) (I K E : Subgroup G) (hKI : K ≤ I) (hEI : E ≤ I)
    (f : I →* Model F) (hK : (K.subgroupOf I).map f = local₂)
    (hE : (E.subgroupOf I).map f ≤ local₁)
    (hEN : (E.subgroupOf I).map f ≤ normalizer (unipotent (K := F) : Set (Model F)))
    (hEK : E ≤ normalizer (K : Set G))
    (hk : IsPGroup 2 (f.subgroupMap (K.subgroupOf I)).ker)
    (h3 : ∀ x ∈ E, x ^ 3 = 1) : E ≤ sectionCentralizer K := by
  have hEK' : E.subgroupOf I ≤ normalizer (K.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hKI]
    exact comap_mono hEK
  have hc := source_tensor_g2_chosen_cubic_factor hF f (K.subgroupOf I) (E.subgroupOf I)
    hK hE hEN hEK' hk (fun x hx => Subtype.ext (h3 x hx))
  have hcomm := ((le_sectionCentralizer_iff _ _).mp hc).2
  apply (le_sectionCentralizer_iff E K).mpr
  refine ⟨hEK,?_⟩
  have hm := map_mono (f := I.subtype) hcomm
  rwa [map_commutator,map_subgroupOf_eq_of_le hEI,
    map_pCoreIn_of_injective 2 _ _ I.subtype_injective,map_subgroupOf_eq_of_le hKI] at hm

theorem source_tensor_g2_original_factor_of_fixed_local_pair
    (hF : Nat.card F = 4) (I K L E : Subgroup G) (hKI : K ≤ I) (hEI : E ≤ I)
    (f : I →* Model F)
    (hKlocal : (K.subgroupOf I).map f ∈ localCComponents (sylow (F := F)))
    (hKproper : (K.subgroupOf I).map f ≠ ⊤)
    (hLlocal : (L.subgroupOf I).map f ∈ localCComponents (sylow (F := F)))
    (hLproper : (L.subgroupOf I).map f ≠ ⊤)
    (hne : (L.subgroupOf I).map f ≠ (K.subgroupOf I).map f)
    (v : Natural.Space F) (hv : v ≠ 0)
    (hU : ∀ u ∈ unipotent (K := F), Natural.action F u v = v)
    (hfix : ∀ k ∈ (K.subgroupOf I).map f, Natural.action F k v = v)
    (hEL : E ≤ L)
    (hEN : (E.subgroupOf I).map f ≤ normalizer (unipotent (K := F) : Set (Model F)))
    (hEK : E ≤ normalizer (K : Set G))
    (hk : IsPGroup 2 (f.subgroupMap (K.subgroupOf I)).ker)
    (h3 : ∀ x ∈ E, x ^ 3 = 1) : E ≤ sectionCentralizer K := by
  have hK := source_g2_fixed_local_is_long hF ((K.subgroupOf I).map f)
    hKlocal hKproper v hv hU hfix
  have hL : (L.subgroupOf I).map f = local₁ := by
    rcases source_g2_local_at_standard_sylow hF ((L.subgroupOf I).map f)
      hLlocal hLproper with hL | hL
    · exact hL
    · exact (hne (hL.trans hK.symm)).elim
  exact source_tensor_g2_original_chosen_factor hF I K E hKI hEI f hK
    ((map_mono (comap_mono hEL)).trans_eq hL) hEN hEK hk h3

theorem source_tensor_g2_original_cartan_contradiction
    (hF : Nat.card F = 4) (I K D E N : Subgroup G) (hKI : K ≤ I) (hEI : E ≤ I)
    (f : I →* Model F)
    (hK : (K.subgroupOf I).map f = local₂) (hE : (E.subgroupOf I).map f ≤ local₁)
    (hEN : (E.subgroupOf I).map f ≤ normalizer (unipotent (K := F) : Set (Model F)))
    (hEK : E ≤ normalizer (K : Set G))
    (hk : IsPGroup 2 (f.subgroupMap (K.subgroupOf I)).ker)
    (h3 : ∀ x ∈ E, x ^ 3 = 1)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hNK : N ≤ normalizer (K : Set G)) (hgen : componentOrbit E N = D)
    (b : G) (hbD : b ∈ D) (hbK : b ∈ K) (hb3 : orderOf b = 3) : False :=
  source_tensor_torus_cubic_contradiction K D E N eK hNK
    (source_tensor_g2_original_chosen_factor hF I K E hKI hEI f hK hE hEN hEK hk h3)
    hgen b hbD hbK hb3

end CFSG.Quasithin.Chapter10
