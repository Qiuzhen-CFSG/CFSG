module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Sp4Four.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Sp4Four.FieldCoverGeometry
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.TwoCentralSubspace.Lift
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.SylowBridge

/-!
# Excluding the Sp₄(4) field exception in the source configuration

The full source configuration gives a marked elementary order-eight action
on Y itself, retaining its A₆ component and fixed component Sylow subgroup.
Any nonidentity actor fixing a Sylow subgroup of Y lifts to a subspace B
of corank two in V, containing A₁. Relative normality in C_G(A₁) and the
small-corank Sylow bridge then produce a Sylow subgroup of Y fixed by V.
Its central-quotient image would be a Sylow subgroup of Sp₄(4) fixed by the
field involution. The proved field-fixed index bound rules this out.

The final theorem discharges `FieldCoverSylowGeometry` using its proved
central-cover calculation. That calculation eliminates the cover via the
actual multiplier theorem before transporting Sylow fixation. The source
assembly uses relative normality in C_G(A₁), the proved small-corank Sylow
bridge, and the existing local residual convention.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.6.5,
E.6.8, printed pp.246–248, and E.6.23, p.254 (PDF p.265). The field-fixed
index comparison is 16.1.8, pp.1172–1173.
-/

public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Sp4Four
universe u
variable {G : Type u} [Group G] [Finite G] {M V U A L X Y : Subgroup G} {g : G}

/-- The marked action before passing to the central quotient. -/
theorem fixed_six_action [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    ∃ s : FixedSixAction Y, s.actors = actionImage V Y ∧
      zpowers s.involution = actionImage A Y := by
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := actionImage A Y) 2
    (by rw [action_order_two d hY])
  have hz : zpowers (b : MulAut Y) = actionImage A Y := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr b.property)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hb, action_order_two d hY]
  have hfixed : FixedPoints.subgroup (actionImage A Y) Y = (b : MulAut Y).fixedSubgroup := by
    ext x
    constructor
    · intro hx
      exact (MulAut.mem_fixedSubgroup _ _).mpr (hx b)
    · intro hx
      have hle : zpowers b.val ≤ MulAction.stabilizer (MulAut Y) x :=
        zpowers_le.mpr ((MulAut.mem_fixedSubgroup _ _).mp hx)
      intro a
      exact hle (hz.symm ▸ a.property)
  have hAV : actionImage A Y ≤ actionImage V Y :=
    Subgroup.map_mono (fun _ hx => d.subspace_mem.1 hx)
  let e : X ≃* X.subgroupOf Y := (subgroupOfEquivOfLe hY.proper.le).symm
  obtain ⟨e₆⟩ := d.six.model
  obtain ⟨P, _, hP⟩ := whole_action_fixes_component_sylow h d hY
  refine ⟨{
    actors := actionImage V Y
    elementary := elementary_actionImage (hY.normalized_by_V d.subspace_mem.1)
    card_actors := whole_action_order d hY
    involution := b.val
    involution_mem := hAV b.property
    involution_order := (Subgroup.orderOf_coe b).trans hb
    six := X.subgroupOf Y
    component := ?_
    model := ⟨e.symm.trans e₆⟩
    sylow := P.mapSurjective (f := e.toMonoidHom) e.surjective
    fixes := ?_ }, rfl, hz⟩
  · rw [← hfixed]
    exact ⟨(six_fixed_component d hY).1, (six_fixed_component d hY).2.1⟩
  · rintro a ha x ⟨y, hy, rfl⟩
    exact hP a ha y hy

/-- Field descent rules out a fixed Sylow even on a nontrivial central cover. -/
theorem no_fixed_sylow
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (e : (Y ⧸ center Y) ≃* Sp F)
    (he : ((actionImage A Y).map (quotientAut (center Y))).map
      (MulAut.congr e).toMonoidHom =
        zpowers (DiagramAutomorphisms.FieldFixedResidual.representative 1))
    (P : Sylow 2 Y) :
    ¬ (P : Subgroup Y).map Y.subtype ≤ centralizer (A : Set G) := by
  intro hP
  let q := QuotientGroup.mk' (center Y)
  let f := e.toMonoidHom.comp q
  let Q := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hf : DiagramAutomorphisms.FieldFixedResidual.representative (F := F) 1 ∈
      ((actionImage A Y).map (quotientAut (center Y))).map
        (MulAut.congr e).toMonoidHom := by
    rw [he]
    exact mem_zpowers _
  obtain ⟨a, ⟨b, hb, rfl⟩, ha⟩ := hf
  have hfix : (Q : Subgroup (Sp F)) ≤
      (DiagramAutomorphisms.FieldFixedResidual.representative (F := F) 1).fixedSubgroup := by
    rintro z ⟨y, hy, rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [← ha]
    change e (quotientAut (center Y) b (e.symm (e (q y)))) = e (q y)
    rw [e.symm_apply_apply, quotientAut_apply_mk]
    have hbfix : b y = y := by
      obtain ⟨c, hc, rfl⟩ := hb
      apply Subtype.ext
      change (c : G) * (y : G) * (c : G)⁻¹ = y
      exact mul_inv_eq_iff_eq_mul.mpr (hP (mem_map_of_mem Y.subtype hy) c hc)
    rw [hbfix]
  have hi := DiagramAutomorphisms.FieldFixedResidual.two_lt_fixed_index
    (F := F) (m := 1) (by decide) (by simpa using hF) Q
  rw [subgroupOf_eq_top.mpr hfix, index_top] at hi
  omega

/-- A nonidentity Sylow-fixing actor gives precisely the source subspace. -/
theorem subspace_of_sylow_fixed_actor [IsElementaryAbelian 2 V]
    {g : G} (c : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y)
    {a : MulAut Y} (ha : a ∈ actionImage V Y) (ha1 : a ≠ 1)
    (P : Sylow 2 Y) (hP : ∀ x ∈ (P : Subgroup Y), a x = x) :
    ∃ B : Subgroup G, intersection A U g ≤ B ∧ B ≤ V ∧ subgroupCorank V B = 2 ∧
      Nat.card (actionImage B Y) = 2 ∧
        ∃ P : Sylow 2 Y, (P : Subgroup Y).map Y.subtype ≤ centralizer (B : Set G) := by
  have hn := hY.normalized_by_V c.subspace_mem.1
  let ρ := Y.normalizerMonoidHom.comp (inclusion hn)
  let S := zpowers a
  let W := S.comap ρ
  let B := W.map V.subtype
  have hSρ : S ≤ ρ.range := zpowers_le.mpr ((actionImage_eq_range hn) ▸ ha)
  have hcardρ : Nat.card ρ.range = 8 := by
    rw [← actionImage_eq_range hn]
    exact whole_action_order c hY
  let _ := elementary_actionImage hn
  have ha2 : a ^ 2 = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (actionImage V Y)) ⟨a, ha⟩)
  have hcardS : Nat.card S = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha2 ha1
  have hBimage : actionImage B Y = S := by
    rw [actionImage_map hn, map_comap_eq, inf_eq_right.mpr hSρ]
  have hindexS : S.relIndex ρ.range = 4 := by
    have hp := relIndex_mul_relIndex (⊥ : Subgroup (MulAut Y)) S ρ.range bot_le hSρ
    rw [relIndex_bot_left, relIndex_bot_left, hcardS, hcardρ] at hp
    omega
  have hindexB : B.relIndex V = 4 := by
    have htop : (⊤ : Subgroup V).map V.subtype = V := by rw [← MonoidHom.range_eq_map, V.range_subtype]
    change (W.map V.subtype).relIndex V = 4
    conv_lhs => rhs; rw [← htop]
    rw [relIndex_map_map_of_injective _ _ V.subtype_injective,
      relIndex_top_right, index_comap]
    exact hindexS
  refine ⟨B, ?_, map_subtype_le W, ?_, hBimage ▸ hcardS, P, ?_⟩
  · intro x hx
    have hxC : x ∈ V ⊓ centralizer (Y : Set G) := (fixed_space c hY).symm ▸ hx
    refine ⟨⟨x, hxC.1⟩, ?_, rfl⟩
    have hk : ρ ⟨x, hxC.1⟩ = 1 := by
      change (⟨x, hxC.1⟩ : V) ∈ ρ.ker
      rw [conjugation_ker]
      exact hxC.2
    change ρ ⟨x, hxC.1⟩ ∈ S
    rw [hk]
    exact one_mem S
  · rw [subgroupCorank, hindexB]
    decide
  · rintro y ⟨x, hx, rfl⟩ b hb
    have hbN := hn (map_subtype_le W hb)
    have hbS : Y.normalizerMonoidHom ⟨b, hbN⟩ ∈ S :=
      hBimage ▸ (show Y.normalizerMonoidHom ⟨b, hbN⟩ ∈ actionImage B Y from
        ⟨⟨b, hbN⟩, hb, rfl⟩)
    have hsfix : ∀ s ∈ S, s x = x := by
      have hle : S ≤ MulAction.stabilizer (MulAut Y) x := zpowers_le.mpr (hP x hx)
      exact fun s hs => hle hs
    have he := congrArg Subtype.val (hsfix _ hbS)
    change b * (x : G) * b⁻¹ = x at he
    exact mul_inv_eq_iff_eq_mul.mp he

/-- Conditional source assembly: its sole extra input constructs a Sylow-fixing actor
on the actual central cover. The theorem below discharges this input. -/
theorem symplecticFieldSourceExclusion_of_geometry
    (hgeom : FieldCoverSylowGeometry.{u})
    (T : Sylow 2 G) (M V : Subgroup G) [IsElementaryAbelian 2 V] :
    SymplecticFieldSourceExclusion T M V := by
  intro h h15 earlier U A L X g d hne Y hY F _ _ _ hF e he
  let _ := extension_quasisimple hY
  have hcenter : IsPGroup 2 (center Y) := by
    rw [extension_center d hne earlier.odd_core_free hY]
    exact pCore_isPGroup
  obtain ⟨s, hs, hsa⟩ := fixed_six_action h d hY
  have hfield : ((zpowers s.involution).map (quotientAut (center Y))).map
      (MulAut.congr e).toMonoidHom =
        zpowers (DiagramAutomorphisms.FieldFixedResidual.representative 1) := by
    rw [hsa]
    exact he
  obtain ⟨a, ha, ha1, P, hP⟩ := hgeom Y hcenter F hF e s hfield
  obtain ⟨B, h1B, hBV, hc, _, R, hR⟩ :=
    subspace_of_sylow_fixed_actor d hY (hs ▸ ha) ha1 P hP
  have hm := (lemma_E_6_16_1 h h15 d.hyperplane d.hyperplane_mem.2.2.1).2.1
  obtain ⟨R', hR'⟩ := exists_sylow_centralized_by_V h h1B hBV
    (hc ▸ hm) hY.component.1 hY.normal R hR
  exact no_fixed_sylow hF e he R'
    (hR'.trans (Subgroup.centralizer_le d.subspace_mem.1))

/-- The genuine Sp₄(4) field exception is impossible under the original source
configuration, with no additional geometric or central-cover premise. -/
theorem symplecticFieldSourceExclusion
    (T : Sylow 2 G) (M V : Subgroup G) [IsElementaryAbelian 2 V] :
    SymplecticFieldSourceExclusion T M V :=
  symplecticFieldSourceExclusion_of_geometry fieldCoverSylowGeometry T M V

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Sp4Four
