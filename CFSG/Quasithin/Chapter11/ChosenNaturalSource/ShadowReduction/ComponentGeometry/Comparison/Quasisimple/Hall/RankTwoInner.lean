module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.Sl3Inner
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.AutomorphismDescription
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.StandardLocalExtensions

/-!
# Inner radical placement in every surviving rank-two image

The G₂ field component is detected on either actual local quotient. Each
local has odd index, so a power of odd degree of a normalizing inner actor
lies in the local. Its action on the PSL₂ quotient is inner. A two-power
field automorphism trivial on that quotient is consequently trivial.
This argument includes even field degree and keeps the original local map.

Together with the SL₃ and Sp₄ calculations, the full seed marking now places
the literal R₁ image inside the component in all surviving rows. For an
original G₂ natural action, the Hall actor gives Kz = K in every row.
Strict omega-center containment for the other original natural actions and
final 11.4.2 assembly remain with qt-d-1222-shadow-component-comparison;
earlier source premises retain qt-d-1222-shadow-components as discharge owner.
Source: Aschbacher--Smith 11.4.2, printed p.777, using F.1.12, 11.0.4
and 11.1.5. Imported G₂ calculations retain LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall

private theorem field_eq_one_of_odd_index_local
    {M F : Type*} [Group M] [Finite M] [Field F] [CharP F 2]
    (J : Subgroup M) (hodd : Odd J.index)
    (e : (J ⧸ pCore 2 J) ≃* PSL(2,F))
    (φ : MulAut M) (β : MulAut J) (σ : F ≃+* F)
    (hβ : ∀ x : J, (β x).val = φ x.val)
    (hf : ∀ x : J, e (QuotientGroup.mk' _ (β x)) =
      Atlas.fieldEquivPSL 2 σ (e (QuotientGroup.mk' _ x)))
    (g : M) (a : MulAut M) (ha : a = MulAut.conj g * φ)
    (hJ : J.map a.toMonoidHom = J)
    (ht : ∃ k : ℕ, σ^(2^k)=1)
    (hc : ∀ x ∈ J, a x * x⁻¹ ∈ J.pCoreIn 2) : σ = 1 := by
  have hφ : J.map φ.toMonoidHom = J := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change φ x ∈ J
      rw [←hβ ⟨x,hx⟩]
      exact (β ⟨x,hx⟩).property
    · intro x hx
      refine ⟨(β.symm ⟨x,hx⟩).val,(β.symm ⟨x,hx⟩).property,?_⟩
      change φ (β.symm ⟨x,hx⟩).val = x
      rw [←hβ,β.apply_symm_apply]
  have hg : g ∈ normalizer (J : Set M) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [ha] at hJ
    change J.map ((MulAut.conj g).toMonoidHom.comp φ.toMonoidHom) = J at hJ
    rwa [←map_map,hφ] at hJ
  let gn : normalizer (J : Set M) := ⟨g,hg⟩
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  let r : normalizer (J : Set M) →* MulAut PSL(2,F) :=
    (MulAut.congr e).toMonoidHom.comp
      ((quotientAut (pCore 2 J)).comp J.normalizerMonoidHom)
  have hr (u : normalizer (J : Set M)) (x : J) :
      r u (q x) = q (J.normalizerMonoidHom u x) := by
    change e (quotientAut (pCore 2 J) (J.normalizerMonoidHom u)
      (e.symm (e (QuotientGroup.mk' _ x)))) = _
    rw [e.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have heq : r gn * Atlas.RankOneFieldAutomorphisms.pslFieldAction σ = 1 := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 J)) y
    change r gn (Atlas.fieldEquivPSL 2 σ (q x)) = q x
    have hf' : q (β x) = Atlas.fieldEquivPSL 2 σ (q x) := hf x
    rw [←hf',hr]
    have hcore : J.normalizerMonoidHom gn (β x) * x⁻¹ ∈ pCore 2 J := by
      apply (mem_map_iff_mem J.subtype_injective).mp
      change g * (β x).val * g⁻¹ * x.val⁻¹ ∈ J.pCoreIn 2
      rw [hβ]
      change (MulAut.conj g * φ) x.val * x.val⁻¹ ∈ J.pCoreIn 2
      rw [←ha]
      exact hc x.val x.property
    apply mul_inv_eq_one.mp
    rw [←map_inv,←map_mul]
    change e (QuotientGroup.mk' (pCore 2 J) _) = 1
    rw [show QuotientGroup.mk' (pCore 2 J) (J.normalizerMonoidHom gn (β x) * x⁻¹) = 1 from
      (QuotientGroup.eq_one_iff _).mpr hcore,map_one]
  let d := (J.subgroupOf (normalizer (J : Set M))).index
  have hd : Odd d := hodd.of_dvd_nat (relIndex_dvd_index_of_le J.le_normalizer)
  have hgd : g^d ∈ J := by
    change gn^d ∈ J.subgroupOf (normalizer (J : Set M))
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (J.subgroupOf (normalizer (J : Set M))) (gn^d) = 1
    rw [map_pow]
    exact pow_card_eq_one'
  let j : J := ⟨g^d,hgd⟩
  have hrd : r gn ^ d = MulAut.conj (q j) := by
    rw [←map_pow]
    apply MulEquiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 J)) y
    change r (gn^d) (q x) = MulAut.conj (q j) (q x)
    rw [hr]
    have hh : J.normalizerMonoidHom (gn^d) x = j*x*j⁻¹ := Subtype.ext rfl
    rw [hh,map_mul,map_mul,map_inv]
    rfl
  have hs : σ^d = 1 := by
    apply Atlas.RankOneFieldAutomorphisms.field_eq_one_of_PSL_inner _ (q j)⁻¹
    change Atlas.RankOneFieldAutomorphisms.pslFieldAction (σ^d) = _
    rw [map_pow,eq_inv_of_mul_eq_one_right heq,inv_pow,hrd,map_inv]
  obtain ⟨k,hk⟩ := ht
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (hd.coprime_two_right.pow_right k)
    (orderOf_dvd_of_pow_eq_one hs) (orderOf_dvd_of_pow_eq_one hk)

open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.LieAutomorphismExtensions

private theorem g2_short_detection {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (a : MulAut (Model F))
    (ha : (local₁ (F := F)).map a.toMonoidHom = local₁)
    (ht : ∃ k : ℕ, a^(2^k)=1)
    (hc : ∀ x ∈ local₁, a x * x⁻¹ ∈ (local₁ (F := F)).pCoreIn 2) :
    ∃ g : Model F, a = MulAut.conj g := by
  obtain ⟨g,σ,he⟩ := exists_inner_field hq a
  have htσ : ∃ k : ℕ, σ^(2^k)=1 := by
    obtain ⟨k,hk⟩ := ht
    refine ⟨k,?_⟩
    have hh := congrArg (fieldComponent hq) hk
    rw [map_pow,he,fieldComponent_inner_field,map_one] at hh
    exact hh
  have ho : Odd (local₁ (F := F)).index :=
    unipotent_index_odd.of_dvd_nat (index_dvd_of_le unipotent_le_local₁)
  have hs := field_eq_one_of_odd_index_local local₁ ho local₁CoreQuotientEquivPSL
    (fieldAction σ) (shortFieldAction σ) σ (shortFieldAction_apply_val σ)
    (shortPSLHom_field σ) g a he ha htσ hc
  exact ⟨g,by rw [he,hs,map_one,mul_one]⟩

private theorem g2_long_detection {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (a : MulAut (Model F))
    (ha : (local₂ (F := F)).map a.toMonoidHom = local₂)
    (ht : ∃ k : ℕ, a^(2^k)=1)
    (hc : ∀ x ∈ local₂, a x * x⁻¹ ∈ (local₂ (F := F)).pCoreIn 2) :
    ∃ g : Model F, a = MulAut.conj g := by
  obtain ⟨g,σ,he⟩ := exists_inner_field hq a
  have htσ : ∃ k : ℕ, σ^(2^k)=1 := by
    obtain ⟨k,hk⟩ := ht
    refine ⟨k,?_⟩
    have hh := congrArg (fieldComponent hq) hk
    rw [map_pow,he,fieldComponent_inner_field,map_one] at hh
    exact hh
  have ho : Odd (local₂ (F := F)).index :=
    unipotent_index_odd.of_dvd_nat (index_dvd_of_le unipotent_le_local₂)
  have hs := field_eq_one_of_odd_index_local local₂ ho local₂CoreQuotientEquivPSL
    (fieldAction σ) (longFieldAction σ) σ (longFieldAction_apply_val σ)
    (longPSLHom_field σ) g a he ha htσ hc
  exact ⟨g,by rw [he,hs,map_one,mul_one]⟩

open Classification SeedFrame
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- Either full G₂ local detects the original radical, with no parity
restriction on the source field degree. -/
theorem g2_radical_image_le_component_of_marked_seed
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hT : (T : Subgroup G) ≤ E.G₁)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2^E.input.field.degree)
    (e : componentImage E ≃* Model F)
    (he : (innerSeed E).map e.toMonoidHom = local₁ ∨
      (innerSeed E).map e.toMonoidHom = local₂) :
    (radical E).map (projection E) ≤ componentImage E := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^E.input.field.degree from
      Nat.pow_lt_pow_right (by decide) E.input.nonbinary)
  rcases he with he | he
  · exact radical_image_le_component_of_local_detection E h hf hne hstar hcent hT e _ he
      (g2_short_detection hq)
  · exact radical_image_le_component_of_local_detection E h hf hne hstar hcent hT e _ he
      (g2_long_detection hq)

/-- The original quotient and full Sylow normalization discharge inner
placement in all three surviving component-image rows. -/
theorem rankTwo_radical_image_le_component
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hT : (T : Subgroup G) ≤ E.G₁)
    (e₁ : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier))
    (hm : RankTwoModel E) :
    (radical E).map (projection E) ≤ componentImage E := by
  obtain ⟨F,_,_,hF,hframe⟩ := full_parabolic_frame E h hf hne hstar hcent e₁ hT hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  rcases hframe with ⟨e,he⟩ | ⟨e,he⟩ | ⟨e,he⟩
  · exact sl3_radical_image_le_component_of_marked_seed E h hf hne hstar hcent hT hF e
      (he.imp And.right And.right)
  · exact sp4_radical_image_le_component_of_marked_seed E h hf hne hstar hcent hT hF e
      (he.imp And.right And.right)
  · exact g2_radical_image_le_component_of_marked_seed E h hf hne hstar hcent hT hF e
      (he.imp And.right And.right)

variable {E}
open Representation CFSG.Quasithin.ChapterB.QuasisimpleSource

/-- The original G₂ natural action excludes every surviving rank-two image through the actual
Hall actor. Innerness and ambient normalization are proved here. -/
theorem ofFlag_g2_eq_of_rankTwo
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
    (hm : RankTwoModel (ofFlag S f X z H))
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
  have hi := rankTwo_radical_image_le_component (ofFlag S f X z H)
    h hf hne hstar hcent (f.invariant 0) e₁ hm
  obtain ⟨p,Y,hp,hodd,hd,hYK,hYR,hY,hrY⟩ := exists_odd_actor_of_inner_radical
    (ofFlag S f X z H) h hf hne hstar hcent hm hi
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
