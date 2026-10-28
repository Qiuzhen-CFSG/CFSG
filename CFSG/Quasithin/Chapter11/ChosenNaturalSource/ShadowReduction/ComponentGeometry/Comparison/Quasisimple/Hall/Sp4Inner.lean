module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.SeedEquality
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.LocalCoreKernel
public import Theory.GroupTheory.NormalSubgroupInvolutionFiber
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.G2Inner

/-!
# Inner placement of the original radical in the symplectic image

The same component marking identifies the actual seed with a full symplectic
local. The radical preserves that local and acts trivially on its two-core
quotient. The concrete local automorphism kernel theorem makes each radical
element inner. Self-centralization of the generalized Fitting subgroup lifts
this back to membership in the literal component image, retaining the actual
KzT action quotient throughout.

For an original G₂ natural module this supplies the Hall contradiction and
Kz = K without innerness, strict omega-center or cubic-containment premises.
The SL₃ and even-degree G₂ images, other original natural rows, and final
11.4.2 assembly remain with qt-d-1222-shadow-component-comparison; earlier
source inputs retain final discharge by qt-d-1222-shadow-components.
Source: Aschbacher--Smith 11.4.2, printed p.777, using 11.0.4 and 11.1.5.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
open Classification SeedFrame
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- A marked local automorphism-kernel calculation places the literal radical
in the component image. The symplectic consumer below supplies that calculation. -/
theorem radical_image_le_component_of_local_detection
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hT : (T : Subgroup G) ≤ E.G₁)
    {M : Type*} [Group M] [Finite M] (e : componentImage E ≃* M)
    (J : Subgroup M) (he : (innerSeed E).map e.toMonoidHom = J)
    (hdetect : ∀ a : MulAut M, J.map a.toMonoidHom = J →
      (∃ k : ℕ, a ^ (2^k) = 1) →
      (∀ x ∈ J, a x * x⁻¹ ∈ J.pCoreIn 2) → ∃ m : M, a = MulAut.conj m) :
    (radical E).map (projection E) ≤ componentImage E := by
  let := componentImage_normal E h
  let f := (componentImage E).subtype.comp e.symm.toMonoidHom
  have hfi : Function.Injective f := (componentImage E).subtype_injective.comp e.symm.injective
  have hJ : J.map f = seed E := by
    rw [←he,map_map]
    have hh : f.comp e.toMonoidHom = (componentImage E).subtype := by
      ext x
      exact congrArg Subtype.val (e.symm_apply_apply x)
    rw [hh]
    exact map_subgroupOf_eq_of_le (AlternatingSeven.seedImage_le_componentImage E)
  let a := normalConjThrough (componentImage E) e
  have ha (r : ActionQuotient E) (x : M) : f (a r x) = r * f x * r⁻¹ := by
    obtain ⟨x,rfl⟩ := e.surjective x
    rw [normalConjThrough_apply]
    change (e.symm (e _)).val = _
    simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_apply, MulAut.conjNormal_apply, Subgroup.subtype_apply]
  have hR : IsPGroup 2 ((radical E).map (projection E)) :=
    ((isPGroup_pCoreIn 2 (E.L₁ ⊔ (T : Subgroup G))).comap_subtype).map _
  have hRn : (radical E).map (projection E) ≤ normalizer (seed E : Set (ActionQuotient E)) :=
    (map_mono (show radical E ≤ (sylow E : Subgroup (localGroup E)) from
      fun _ hx => radical_le_sylow E hx)).trans (sylow_image_normalizes_seed E hT)
  intro r hr
  have hfix : J.map (a r).toMonoidHom = J := by
    apply map_injective hfi
    rw [map_map]
    have hh : f.comp (a r).toMonoidHom = (MulAut.conj r).toMonoidHom.comp f :=
      MonoidHom.ext (ha r)
    rw [hh,←map_map,hJ]
    exact mem_normalizer_iff_map_conj_eq.mp (hRn hr)
  have htwo : ∃ k : ℕ, (a r) ^ (2^k) = 1 := by
    obtain ⟨k,hk⟩ := hR ⟨r,hr⟩
    exact ⟨k,by rw [←map_pow,show r ^ (2^k) = 1 from congrArg Subtype.val hk,map_one]⟩
  have htriv (x : M) (hx : x ∈ J) : a r x * x⁻¹ ∈ J.pCoreIn 2 := by
    have hc := radical_seed_commutator_le_core E hT
      (commutator_mem_commutator hr (show f x ∈ seed E from hJ ▸ mem_map_of_mem f hx))
    rw [←hJ,←map_pCoreIn_of_injective 2 J f hfi] at hc
    apply (mem_map_iff_mem hfi).mp
    convert hc using 1
    rw [map_mul,map_inv,ha]
    rfl
  by_contra hout
  have hF := (action_structure E h hf hne hstar hcent).2.1
  have hc : centralizer (componentImage E : Set (ActionQuotient E)) ≤ componentImage E := by
    rw [show componentImage E = generalizedFitting (ActionQuotient E) from hF]
    exact centralizer_generalizedFitting_le _
  exact normalConjThrough_not_inner (componentImage E) e hc r hout (hdetect (a r) hfix htwo htriv)

/-- The literal radical is inner under the same full symplectic seed marking. -/
theorem sp4_radical_image_le_component_of_marked_seed
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hT : (T : Subgroup G) ≤ E.G₁)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2^E.input.field.degree)
    (e : componentImage E ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (he : (innerSeed E).map e.toMonoidHom = Theory.SpecificGroups.SymplecticFour.pointLocal ∨
      (innerSeed E).map e.toMonoidHom = Theory.SpecificGroups.SymplecticFour.planeLocal) :
    (radical E).map (projection E) ≤ componentImage E := by
  rcases he with he | he
  · apply radical_image_le_component_of_local_detection E h hf hne hstar hcent hT e _ he
    intro a ha ht hc
    have hc' (x : Theory.SpecificGroups.SymplecticFour.pointLocal (F := F)) :
        Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.restrict a _ ha x / x ∈
          pCore 2 Theory.SpecificGroups.SymplecticFour.pointLocal := by
      apply (mem_map_iff_mem (Theory.SpecificGroups.SymplecticFour.pointLocal (F := F)).subtype_injective).mp
      change a x.val * x.val⁻¹ ∈ _
      exact hc x.val x.property
    obtain ⟨k,_,hk⟩ := Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.point_core_inner_of_quotient_trivial
      hF E.input.nonbinary a ha ht hc'
    exact ⟨k.val,hk⟩
  · apply radical_image_le_component_of_local_detection E h hf hne hstar hcent hT e _ he
    intro a ha ht hc
    have hc' (x : Theory.SpecificGroups.SymplecticFour.planeLocal (F := F)) :
        Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.restrict a _ ha x / x ∈
          pCore 2 Theory.SpecificGroups.SymplecticFour.planeLocal := by
      apply (mem_map_iff_mem (Theory.SpecificGroups.SymplecticFour.planeLocal (F := F)).subtype_injective).mp
      change a x.val * x.val⁻¹ ∈ _
      exact hc x.val x.property
    obtain ⟨k,_,hk⟩ := Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.plane_core_inner_of_quotient_trivial
      hF E.input.nonbinary a ha ht hc'
    exact ⟨k.val,hk⟩

/-- In the symplectic image row the original seed quotient and Sylow action
construct the marking and discharge all inner-placement premises. -/
theorem sp4_radical_image_le_component
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hT : (T : Subgroup G) ≤ E.G₁)
    (e₁ : (E.L₁ ⧸ pCore 2 E.L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) E.input.field.Carrier)
    (hm : Source.IsSp (componentImage E) 2 (2^E.input.field.degree)) :
    (radical E).map (projection E) ≤ componentImage E := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨a,ha⟩ := sp4_full_parabolic_frame E h hf hne hstar hcent e₁ hT hF e
  exact sp4_radical_image_le_component_of_marked_seed E h hf hne hstar hcent hT hF a
    (ha.imp And.right And.right)

variable {E}
open Representation CFSG.Quasithin.ChapterB.QuasisimpleSource

/-- The original G₂ natural action excludes the Sp₄ image through the actual
Hall actor. Innerness and ambient normalization are proved here. -/
theorem ofFlag_g2_eq_of_sp4
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
    (hm : Source.IsSp (componentImage (ofFlag S f X z H)) 2 (2 ^ S.field.degree))
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
  have hi := sp4_radical_image_le_component (ofFlag S f X z H)
    h hf hne hstar hcent (f.invariant 0) e₁ hm
  obtain ⟨p,Y,hp,hodd,hd,hYK,hYR,hY,hrY⟩ := exists_odd_actor_of_inner_radical
    (ofFlag S f X z H) h hf hne hstar hcent (.inr (.inl hm)) hi
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
