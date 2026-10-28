module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.Sp4Inner
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.AmbientLocalCores
public import Theory.SpecificGroups.PSL3.CartanActions.ResidualInner

/-!
# Inner placement in the actual special linear component

The full marked seed identifies a point or line local in SL₃. Projecting
its two-power radical action to PSL₃ preserves the local and its literal
core quotient. The local block calculation eliminates the field component;
perfectness lifts innerness through the full covering center. The original
G₂ natural action then gives Kz = K through the constructed Hall actor.

The other original natural actions and final 11.4.2 assembly remain with
qt-d-1222-shadow-component-comparison; earlier-source discharge remains
with qt-d-1222-shadow-components. Source: Aschbacher--Smith 11.4.2,
printed p.777, using 11.0.4 and 11.1.5. Imported ATLAS calculations retain
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.RootPlaneGeometry Matrix.PSL3.ExtensionBorel
open Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3.LinearThree.OuterExtensions.CoreCalculation
open Theory.GroupTheory.AutomorphismExtensionBorel

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall

private theorem sl3_local_detection {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) (point : Bool)
    (a : MulAut SL(3,F)) (ha : (localSL F point).map a.toMonoidHom = localSL F point)
    (ht : ∃ k : ℕ, a^(2^k)=1)
    (hc : ∀ x ∈ localSL F point, a x * x⁻¹ ∈ (localSL F point).pCoreIn 2) :
    ∃ g : SL(3,F), a = MulAut.conj g := by
  let b := centerAction F a
  have hm : (localSL F point).map (Matrix.PSL3.projection F) = localFactor F point := by
    cases point <;> rfl
  have hb : (localFactor F point).map b.toMonoidHom = localFactor F point := by
    rw [←hm,map_map]
    have he : b.toMonoidHom.comp (Matrix.PSL3.projection F) = (Matrix.PSL3.projection F).comp a.toMonoidHom := rfl
    rw [he,←map_map,ha]
  let E := ExtensionBorel.linearField F
  have hi : MulAut.innerSubgroup PSL(3,F) ≤ E :=
    (inner_le_innerDiagonal F).trans le_sup_left
  have hbe : b ∈ E := AmbientLocalCores.preserving_local_mem_linearField F hn hF point b hb
  let be : E := ⟨b,hbe⟩
  have hbn : be ∈ normalizer (localIn F E hi point : Set E) := by
    rw [localIn,←rootIn_eq_map]
    exact (mem_normalizer_rootIn_iff _ E hi (inner_injective F) be).mpr hb
  let an : normalizer (localIn F E hi point : Set E) := ⟨be,hbn⟩
  have hp : ∃ k : ℕ, an.val^(2^k)=1 := by
    obtain ⟨k,hk⟩ := ht
    refine ⟨k,Subtype.ext ?_⟩
    change (centerAction F a)^(2^k)=1
    rw [←map_pow,hk,map_one]
  let ar : localSL F point →* localSL F point :=
    (a.toMonoidHom.comp (localSL F point).subtype).codRestrict _
      (fun x => ha.le (mem_map_of_mem _ x.property))
  have hq (x : localSL F point) : ar x * x⁻¹ ∈ pCore 2 (localSL F point) := by
    apply (mem_map_iff_mem (localSL F point).subtype_injective).mp
    exact hc x.val x.property
  have htriv : localBlockAction F E hi point an = 1 := by
    apply (localBlockAction_eq_iff F E hi point an 1).mpr
    intro y
    obtain ⟨x,rfl⟩ := (localProjectEquiv F point).surjective y
    have he : actorLocal F E hi point an (localProjectEquiv F point x) =
        localProjectEquiv F point (ar x) := by
      apply Subtype.ext
      change b (localProjectEquiv F point x).val = _
      rw [localProjectEquiv_val,localProjectEquiv_val]
      rfl
    rw [he]
    change block F point (localProjectEquiv F point (ar x)) =
      block F point (localProjectEquiv F point x)
    apply mul_inv_eq_one.mp
    rw [←map_inv,←map_mul,←map_inv,←map_mul]
    have hcore : localProjectEquiv F point (ar x * x⁻¹) ∈ pCore 2 (localFactor F point) := by
      rw [←pCore_map_iso 2 (localProjectEquiv F point)]
      exact mem_map_of_mem _ (hq x)
    change localFactorQuotientEquiv F point (QuotientGroup.mk' _ _) = 1
    rw [show QuotientGroup.mk' (pCore 2 (localFactor F point))
      (localProjectEquiv F point (ar x * x⁻¹)) = 1 from (QuotientGroup.eq_one_iff _).mpr hcore, map_one]
  have hin := two_element_mem_local_of_trivial_block F E hi le_rfl point an hp htriv
  obtain ⟨g,hg,he⟩ := hin
  have hbi : b ∈ MulAut.innerSubgroup PSL(3,F) := ⟨g,congrArg Subtype.val he⟩
  obtain ⟨g,hg⟩ := CartanActions.ResidualInner.special_inner_of_projective_inner a hbi
  exact ⟨g,hg.symm⟩

open Classification SeedFrame
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The original radical is inner for either full SL₃ local marking. -/
theorem sl3_radical_image_le_component_of_marked_seed
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hT : (T : Subgroup G) ≤ E.G₁)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2^E.input.field.degree)
    (e : componentImage E ≃* SL(3,F))
    (he : (innerSeed E).map e.toMonoidHom = pointLocalSL F ∨
      (innerSeed E).map e.toMonoidHom = lineLocalSL F) :
    (radical E).map (projection E) ≤ componentImage E := by
  rcases he with he | he
  · exact radical_image_le_component_of_local_detection E h hf hne hstar hcent hT e _ he
      (sl3_local_detection E.input.field.degree_pos hF true)
  · exact radical_image_le_component_of_local_detection E h hf hne hstar hcent hT e _ he
      (sl3_local_detection E.input.field.degree_pos hF false)

/-- In the special linear image row the original seed quotient and Sylow action
construct the marking and discharge all inner-placement premises. -/
theorem sl3_radical_image_le_component
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hT : (T : Subgroup G) ≤ E.G₁)
    (e₁ : (E.L₁ ⧸ pCore 2 E.L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) E.input.field.Carrier)
    (hm : Source.IsSL (componentImage E) 3 (2^E.input.field.degree)) :
    (radical E).map (projection E) ≤ componentImage E := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨a,ha⟩ := sl3_full_parabolic_frame E h hf hne hstar hcent e₁ hT hF e
  exact sl3_radical_image_le_component_of_marked_seed E h hf hne hstar hcent hT hF a
    (ha.imp And.right And.right)

variable {E}
open Representation CFSG.Quasithin.ChapterB.QuasisimpleSource

/-- The original G₂ natural action excludes the SL₃ image through the actual
Hall actor. Innerness and ambient normalization are proved here. -/
theorem ofFlag_g2_eq_of_sl3
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (e₁ : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hm : Source.IsSL (componentImage (ofFlag S f X z H)) 3 (2 ^ S.field.degree))
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  have hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G) := by
    rcases hradical with hn | hb
    · exact hn
    · exact (LocalGeometry.Normalizers.PointCohomology.PointGeometry.no_g2_block_marking
        D S m hb.2.1).elim
  by_contra hne
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  have hi := sl3_radical_image_le_component (ofFlag S f X z H)
    h hf hne hstar hcent (f.invariant 0) e₁ hm
  obtain ⟨p,Y,hp,hodd,hd,hYK,hYR,hY,hrY⟩ := exists_odd_actor_of_inner_radical
    (ofFlag S f X z H) h hf hne hstar hcent (.inl hm) hi
  let : Fact p.Prime := ⟨hp⟩
  have hYM := hYR.trans hNM
  have hYL : Y ≤ L := by
    rw [LocalGeometry.Preliminary.g2_prime_residual D S m hp
      (hd.trans (Nat.sub_dvd_pow_sub_pow (2 ^ S.field.degree) 1 2))]
    have hres : (Y.subgroupOf (normalizer (L : Set G))).map
        (normalizer (L : Set G)).subtype ≤
        (primeToResidual p (normalizer (L : Set G))).map (normalizer (L : Set G)).subtype :=
      map_mono (le_primeToResidual_of_isPGroup
      (hY.comap_subtype : IsPGroup p (Y.subgroupOf (normalizer (L : Set G)))))
      (f := (normalizer (L : Set G)).subtype)
    rwa [map_subgroupOf_eq_of_le hYM] at hres
  exact ofFlag_false_of_rank_two_cartan S f X z H h hlinear h1132
    Y hYK hYL hodd hrY


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
