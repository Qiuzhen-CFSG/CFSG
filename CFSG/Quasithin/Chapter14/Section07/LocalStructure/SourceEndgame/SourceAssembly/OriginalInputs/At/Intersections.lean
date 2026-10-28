module
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl

/-!
# Residual intersections at the original Sylow

The marked L₃(2) point residual and its Sylow commutator force the
normalizer-section residual D₁ to centralize L/O₂(L). Normalization by LT
and the original maximal two-local uniqueness then force D₁ = 1.
Consequently D meets N_G(L) inside T and the literal R₁ is Sylow in DR₁.
Only structural 12.2.2 at this G,T is used; known-simple A/C supplies
uniqueness. This is the intersection step of AS 14.7.67(4), p.1070,
for the local final assembly owned by qt-d-14775-source.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.SectionCentralizationAt
variable {G A : Type*} [Group G] [Group A]

private theorem perfect_two_eq_bot (B : Subgroup G)
    (hb : IsPPerfect 2 B) (hp : IsPGroup 2 B) : B = ⊥ := by
  apply bot_unique
  intro x hx
  exact congrArg Subtype.val (DFunLike.congr_fun
    (hb.hom_eq_one_of_isPGroup hp (MonoidHom.id B)) ⟨x,hx⟩)

private theorem normal_perfect_dichotomy [Finite G]
    (hG : IsPPerfect 2 G) (hc : (Nat.card (G ⧸ pCore 2 G)).Prime)
    (B : Subgroup G) [B.Normal] (hb : IsPPerfect 2 B) : B = ⊥ ∨ B = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let : Fact (Nat.card (G ⧸ pCore 2 G)).Prime := ⟨hc⟩
  rcases (B.map q).eq_bot_or_eq_top_of_prime_card with h | h
  · left
    apply perfect_two_eq_bot B hb
    exact pCore_isPGroup.to_le (by
      simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff B).mp h)
  · right
    have hs : B ⊔ pCore 2 G = ⊤ := by
      have hh := congrArg (Subgroup.comap q) h
      simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
    exact hG B inferInstance (isPGroup_quotient_of_sup_eq_top B (pCore 2 G) pCore_isPGroup hs)

private theorem image_dichotomy [Finite G] [Finite A]
    (P X : Subgroup G) (f : G →* A)
    (hp : IsPPerfect 2 P) (hx : IsPPerfect 2 X)
    (hc : (Nat.card (P.map f ⧸ pCore 2 (P.map f))).Prime)
    (hn : P ≤ normalizer (X : Set G)) (hi : X.map f ≤ P.map f) :
    X.map f = ⊥ ∨ X.map f = P.map f := by
  let B := (X.map f).subgroupOf (P.map f)
  have hbn : B.Normal := normal_subgroupOf_of_le_normalizer
    ((map_mono hn).trans (le_normalizer_map _))
  let := hbn
  have hb : IsPPerfect 2 B :=
    (hx.of_surjective (f.subgroupMap X) (f.subgroupMap_surjective X)).of_surjective
      (subgroupOfEquivOfLe hi).symm.toMonoidHom (subgroupOfEquivOfLe hi).symm.surjective
  rcases normal_perfect_dichotomy
    (hp.of_surjective (f.subgroupMap P) (f.subgroupMap_surjective P)) hc B hb with h | h
  · left
    have hh := congrArg (Subgroup.map (P.map f).subtype) h
    simpa only [B, map_subgroupOf_eq_of_le hi, Subgroup.map_bot] using hh
  · right
    have hh := congrArg (Subgroup.map (P.map f).subtype) h
    simpa only [B, map_subgroupOf_eq_of_le hi, ← MonoidHom.range_eq_map, range_subtype] using hh

/-- An image inside a minimal two-perfect section collapses when its Sylow
commutators lift into the prescribed two-group intersection. -/
private theorem image_eq_bot [Finite G] [Finite A]
    (P X S L H : Subgroup G) (f : G →* A)
    (hp : IsPPerfect 2 P) (hx : IsPPerfect 2 X)
    (hc : (Nat.card (P.map f ⧸ pCore 2 (P.map f))).Prime)
    (hn : P ≤ normalizer (X : Set G))
    (hsn : S ≤ normalizer (X : Set G))
    (hxl : X ≤ normalizer (L : Set G))
    (hsl : S ≤ L) (hpl : P ≤ L) (hph : P ≤ H)
    (hker : L ⊓ f.ker ≤ H)
    (hi : X.map f ≤ P.map f)
    (hcomm : ⁅P,S⁆ = P)
    (hsmall : IsPGroup 2 (X ⊓ H : Subgroup G)) : X.map f = ⊥ := by
  have hcx : ⁅X,S⁆ ≤ X := le_normalizer_iff_commutator_le_left.mp hsn
  have hcl : ⁅X,S⁆ ≤ L := (commutator_mono le_rfl hsl).trans
    (le_normalizer_iff_commutator_le_right.mp hxl)
  have hch : ⁅X,S⁆ ≤ H := by
    intro c hc'
    have him : f c ∈ P.map f := hi (mem_map_of_mem f (hcx hc'))
    obtain ⟨p,hp',he⟩ := him
    have hk : p⁻¹ * c ∈ L ⊓ f.ker :=
      ⟨L.mul_mem (L.inv_mem (hpl hp')) (hcl hc'), by
        change f (p⁻¹ * c) = 1
        rw [map_mul,map_inv,he,inv_mul_cancel]⟩
    have hh := H.mul_mem (hph hp') (hker hk)
    simpa only [mul_inv_cancel_left] using hh
  have hctwo : IsPGroup 2 (⁅X,S⁆ : Subgroup G) := hsmall.to_le (le_inf hcx hch)
  rcases image_dichotomy P X f hp hx hc hn hi with h | h
  · exact h
  · have him : (⁅X,S⁆).map f = P.map f := by
      rw [map_commutator,h,← map_commutator,hcomm]
    have htwo : IsPGroup 2 (P.map f) := him ▸ hctwo.map f
    exact h.trans (perfect_two_eq_bot (P.map f)
      (hp.of_surjective (f.subgroupMap P) (f.subgroupMap_surjective P)) htwo)
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.SectionCentralizationAt

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.SectionCentralizationAt
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

private noncomputable def modelMap (e : (L ⧸ pCore 2 L) ≃* SL) : L →* SL :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

private noncomputable def modelAction (e : (L ⧸ pCore 2 L) ≃* SL) :
    normalizer (L : Set G) →* MulAut SL :=
  (MulAut.congr e).toMonoidHom.comp ((quotientAut (pCore 2 L)).comp L.normalizerMonoidHom)

omit [Finite G] in
private theorem modelAction_apply (e : (L ⧸ pCore 2 L) ≃* SL)
    (g : normalizer (L : Set G)) (l : L) :
    modelAction L e g (modelMap L e l) = modelMap L e (L.normalizerMonoidHom g l) := by
  change e (quotientAut (pCore 2 L) (L.normalizerMonoidHom g)
    (e.symm (e (QuotientGroup.mk' (pCore 2 L) l)))) = _
  rw [e.symm_apply_apply, quotientAut_apply_mk]
  rfl

omit [Finite G] in
private theorem modelAction_inner (e : (L ⧸ pCore 2 L) ≃* SL) (l : L) :
    modelAction L e ⟨l,L.le_normalizer l.property⟩ = MulAut.conj (modelMap L e l) := by
  apply MulEquiv.ext
  intro y
  obtain ⟨a,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) y
  change modelAction L e ⟨l,L.le_normalizer l.property⟩ (modelMap L e a) =
    MulAut.conj (modelMap L e l) (modelMap L e a)
  rw [modelAction_apply]
  change modelMap L e (l * a * l⁻¹) = modelMap L e l * modelMap L e a * (modelMap L e l)⁻¹
  rw [map_mul,map_mul,map_inv]

omit [Finite G] in
private theorem modelAction_image (e : (L ⧸ pCore 2 L) ≃* SL)
    (A : Subgroup G) (hAL : A ≤ L) :
    (A.subgroupOf (normalizer (L : Set G))).map (modelAction L e) =
      ((A.subgroupOf L).map (modelMap L e)).map MulAut.conj := by
  ext α
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨modelMap L e ⟨a,hAL ha⟩, ⟨⟨a,hAL ha⟩,ha,rfl⟩, ?_⟩
    exact (modelAction_inner L e ⟨a,hAL ha⟩).symm
  · rintro ⟨_,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨⟨a,L.le_normalizer a.property⟩,ha,modelAction_inner L e a⟩

omit [Finite G] in
private theorem core_subgroupOf (A : Subgroup G) (hAL : A ≤ L) :
    (A.subgroupOf L).pCoreIn 2 = (A.pCoreIn 2).subgroupOf L := by
  apply map_injective L.subtype_injective
  rw [map_pCoreIn_of_injective 2 _ L.subtype L.subtype_injective,
    map_subgroupOf_eq_of_le hAL, map_subgroupOf_eq_of_le ((pCoreIn_le 2 A).trans hAL)]

omit [Finite G] in
private theorem modelAction_preserves (e : (L ⧸ pCore 2 L) ≃* SL)
    (A : Subgroup G) (g : normalizer (L : Set G))
    (hA : (g : G) ∈ normalizer (A : Set G)) :
    ((A.subgroupOf L).map (modelMap L e)).map (modelAction L e g).toMonoidHom =
      (A.subgroupOf L).map (modelMap L e) := by
  have hle : ((A.subgroupOf L).map (modelMap L e)).map
      (modelAction L e g).toMonoidHom ≤ (A.subgroupOf L).map (modelMap L e) := by
    rintro _ ⟨_,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨L.normalizerMonoidHom g a, (mem_normalizer_iff.mp hA a).mp ha,
      (modelAction_apply L e g a).symm⟩
  apply eq_of_le_of_card_ge hle
  exact le_of_eq (card_map_of_injective (modelAction L e g).injective).symm

private theorem modelAction_fixes_section (e : (L ⧸ pCore 2 L) ≃* SL)
    (A : Subgroup G) (hAL : A ≤ L) (X : Subgroup G)
    (hc : ⁅X,A⁆ ≤ A.pCoreIn 2) (x : normalizer (L : Set G)) (hx : (x : G) ∈ X) :
    ∀ a ∈ (A.subgroupOf L).map (modelMap L e),
      modelAction L e x a * a⁻¹ ∈ ((A.subgroupOf L).map (modelMap L e)).pCoreIn 2 := by
  have hk : IsPGroup 2 (modelMap L e).ker := by
    have he : (modelMap L e).ker = pCore 2 L := by
      exact (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
    rw [he]
    exact pCore_isPGroup
  rintro _ ⟨a,ha,rfl⟩
  rw [modelAction_apply, ← map_inv, ← map_mul,
    ← map_pCoreIn_of_ker_isPGroup (modelMap L e) hk]
  apply mem_map_of_mem
  rw [core_subgroupOf L A hAL]
  exact hc (commutator_mem_commutator hx ha)

private theorem modelAction_inner_image (e : (L ⧸ pCore 2 L) ≃* SL)
    (A X : Subgroup G) (hAL : A ≤ L)
    (hn : X ≤ normalizer (A : Set G)) (hc : ⁅X,A⁆ ≤ A.pCoreIn 2)
    (P : Subgroup SL) (hP : P = pointParabolicSL ∨ P = lineParabolicSL)
    (hm : (A.subgroupOf L).map (modelMap L e) = residual P) :
    (X.subgroupOf (normalizer (L : Set G))).map (modelAction L e) ≤
      (A.subgroupOf (normalizer (L : Set G))).map (modelAction L e) := by
  rw [modelAction_image L e A hAL,hm]
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨g,hg,he⟩ := quotient_fixer_is_conj P hP (modelAction L e x)
    (by rw [← hm]; exact modelAction_preserves L e A x (hn hx))
    (by rw [← hm]; exact modelAction_fixes_section L e A hAL X hc x hx)
  exact ⟨g,hg,he.symm⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.SectionCentralizationAt

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.SectionCentralizationAt
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem model_image_core_card (L A : Subgroup G) (hAL : A ≤ L)
    (e : (L ⧸ pCore 2 L) ≃* SL)
    (P : Subgroup SL) (hP : P = pointParabolicSL ∨ P = lineParabolicSL)
    (hm : (A.subgroupOf L).map (modelMap L e) = residual P) :
    Nat.card ((A.subgroupOf (normalizer (L : Set G))).map (modelAction L e) ⧸
      pCore 2 ((A.subgroupOf (normalizer (L : Set G))).map (modelAction L e))) = 3 := by
  have hc : Nat.card (residual P ⧸ pCore 2 (residual P)) = 3 := by
    rcases hP with rfl | rfl
    · rw [point_residual]
      exact card_point_core_quotient
    · rw [line_residual]
      exact card_line_core_quotient
  let E := (residual P).equivMapOfInjective MulAut.conj conj_injective
  let Q := QuotientGroup.congr (pCore 2 (residual P))
    (pCore 2 ((residual P).map MulAut.conj)) E (pCore_map_iso 2 E)
  rw [modelAction_image L e A hAL,hm]
  exact (Nat.card_congr Q.toEquiv).symm.trans hc

omit [Finite G] in
private theorem modelAction_kernel_on_L (L H : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL) (hQH : L.pCoreIn 2 ≤ H) :
    L.subgroupOf (normalizer (L : Set G)) ⊓ (modelAction L e).ker ≤
      H.subgroupOf (normalizer (L : Set G)) := by
  intro x hx
  have hi : MulAut.conj (modelMap L e ⟨x,hx.1⟩) = 1 :=
    (modelAction_inner L e ⟨x,hx.1⟩).symm.trans hx.2
  have he : modelMap L e ⟨x,hx.1⟩ = 1 := conj_injective (hi.trans (map_one _).symm)
  have hq : (⟨x,hx.1⟩ : L) ∈ pCore 2 L :=
    (QuotientGroup.eq_one_iff _).mp (e.injective (he.trans e.map_one.symm))
  exact hQH (mem_map.mpr ⟨⟨x,hx.1⟩,hq,rfl⟩)

omit [Finite G] in
private theorem normalized_subgroupOf (A B M : Subgroup G)
    (h : A ≤ normalizer (B : Set G)) :
    A.subgroupOf M ≤ normalizer (B.subgroupOf M : Set M) := by
  apply le_normalizer_iff.mpr
  intro a ha b hb
  exact le_normalizer_iff.mp h a ha b hb

/-- A marked parabolic residual detects the complete quotient action. -/
private theorem commutator_le_core (L A X S H : Subgroup G)
    (hAL : A ≤ L) (hSL : S ≤ L) (hAH : A ≤ H) (hQH : L.pCoreIn 2 ≤ H)
    (hXM : X ≤ normalizer (L : Set G))
    (hAX : A ≤ normalizer (X : Set G))
    (hSX : S ≤ normalizer (X : Set G))
    (hXA : X ≤ normalizer (A : Set G))
    (hsmall : IsPGroup 2 (X ⊓ H : Subgroup G))
    (hA : IsPPerfect 2 A) (hX : IsPPerfect 2 X)
    (hsection : ⁅X,A⁆ ≤ A.pCoreIn 2) (hcomm : ⁅A,S⁆ = A)
    (e : (L ⧸ pCore 2 L) ≃* SL)
    (P : Subgroup SL) (hP : P = pointParabolicSL ∨ P = lineParabolicSL)
    (hm : (A.subgroupOf L).map (modelMap L e) = residual P) :
    ⁅X,L⁆ ≤ L.pCoreIn 2 := by
  let M := normalizer (L : Set G)
  let f := modelAction L e
  have hAM : A ≤ M := hAL.trans L.le_normalizer
  have hSM : S ≤ M := hSL.trans L.le_normalizer
  have hAf : IsPPerfect 2 (A.subgroupOf M) := hA.of_surjective
    (subgroupOfEquivOfLe hAM).symm.toMonoidHom (subgroupOfEquivOfLe hAM).symm.surjective
  have hXf : IsPPerfect 2 (X.subgroupOf M) := hX.of_surjective
    (subgroupOfEquivOfLe hXM).symm.toMonoidHom (subgroupOfEquivOfLe hXM).symm.surjective
  have hc : (Nat.card ((A.subgroupOf M).map f ⧸ pCore 2 ((A.subgroupOf M).map f))).Prime := by
    rw [model_image_core_card L A hAL e P hP hm]
    decide
  have hcom : ⁅A.subgroupOf M,S.subgroupOf M⁆ = A.subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hAM,map_subgroupOf_eq_of_le hSM,hcomm]
  have hsm : IsPGroup 2 (X.subgroupOf M ⊓ H.subgroupOf M : Subgroup M) := by
    have he : X.subgroupOf M ⊓ H.subgroupOf M = (X ⊓ H).subgroupOf M := rfl
    rw [he]
    exact hsmall.comap_subtype
  have hz := image_eq_bot (A.subgroupOf M) (X.subgroupOf M) (S.subgroupOf M)
    (L.subgroupOf M) (H.subgroupOf M) f hAf hXf hc
    (normalized_subgroupOf A X M hAX) (normalized_subgroupOf S X M hSX)
    (normalized_subgroupOf X L M hXM)
    (fun _ h => hSL h) (fun _ h => hAL h) (fun _ h => hAH h)
    (modelAction_kernel_on_L L H e hQH)
    (modelAction_inner_image L e A X hAL hXA hsection P hP hm) hcom hsm
  have hker := (map_eq_bot_iff (X.subgroupOf M)).mp hz
  apply commutator_le.mpr
  intro x hx l hl
  let a : M := ⟨x,hXM hx⟩
  let b : L := ⟨l,hl⟩
  have ha : modelAction L e a = 1 := hker hx
  have hf : modelMap L e (L.normalizerMonoidHom a b) = modelMap L e b := by
    rw [← modelAction_apply,ha]
    rfl
  have hq : (L.normalizerMonoidHom a b) / b ∈ pCore 2 L := by
    apply QuotientGroup.eq_iff_div_mem.mp
    exact e.injective hf
  exact mem_map.mpr ⟨(L.normalizerMonoidHom a b) / b,hq,by
    change (x * l * x⁻¹) / l = ⁅x,l⁆
    rw [div_eq_mul_inv,commutatorElement_def]⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.SectionCentralizationAt

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.SectionCentralizationAt
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open CFSG.Quasithin.Chapter12.Section08
open CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open ResidualNormalizer
open BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

private theorem linearTwo_derived_card : Nat.card (commutator (LinearGroup 2)) = 3 := by
  have h3 : commutator (Equiv.Perm (Fin 3)) = alternatingGroup (Fin 3) := by
    apply le_antisymm
    · exact Abelianization.commutator_subset_ker Equiv.Perm.sign
    · intro g hg
      have h : ∀ g : Equiv.Perm (Fin 3), Equiv.Perm.sign g = 1 →
          ∃ a b : Equiv.Perm (Fin 3), ⁅a,b⁆ = g := by decide +kernel
      obtain ⟨a,b,rfl⟩ := h g hg
      exact commutator_mem_commutator (mem_top _) (mem_top _)
  let E := linearTwoEquivSymmetricThree
  have hm : (commutator (LinearGroup 2)).map E.toMonoidHom = alternatingGroup (Fin 3) := by
    rw [_root_.map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ E.surjective,
      ← _root_.commutator_def,h3]
  rw [← card_map_of_injective (K := commutator (LinearGroup 2)) (f := E.toMonoidHom) E.injective,hm,nat_card_alternatingGroup,Nat.card_fin]
  rfl

private theorem Li_core_quotient_card (d : Data T L V F W) :
    Nat.card (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) = 3 := by
  let := d.natural.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  obtain ⟨m⟩ := F.naturalSeedMarking_of_ambient (by decide : 3 ≤ 3) L
    d.natural.chosen.normalizes d.natural.naturalMarking
  exact (Nat.card_congr m.quotientEquiv.toEquiv).trans linearTwo_derived_card

private theorem exists_L_sylow (d : Data T L V F W)
    (structural : CFSG.Quasithin.Chapter12.Section02.Structural1222At CFSG.KnownSimple.IsKnownSimple T) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  obtain ⟨S,hS⟩ := (T.subtype (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G))).exists_map_subtype_eq_inf_of_normalizes
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer (d.natural.sylow_normalizes_at structural))
  refine ⟨S, map_injective L.subtype_injective ?_⟩
  rw [hS,Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right,subgroupOf_map_subtype]

private theorem Li_marking_and_commutator (d : Data T L V F W)
    (structural : CFSG.Quasithin.Chapter12.Section02.Structural1222At CFSG.KnownSimple.IsKnownSimple T) :
    ⁅F.Li L 1,(T : Subgroup G) ⊓ L⁆ = F.Li L 1 ∧
      ∃ (e : (L ⧸ pCore 2 L) ≃* SL) (P : Subgroup SL),
        (P = pointParabolicSL ∨ P = lineParabolicSL) ∧
        ((F.Li L 1).subgroupOf L).map (modelMap L e) = residual P := by
  let := d.natural.chosen.elementary
  let e₀ := d.natural.naturalMarking.quotientEquiv.trans (slEquivLinear 3).symm
  let f := modelMap L e₀
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = pCore 2 L :=
      (MonoidHom.ker_comp_of_injective _ _ e₀.injective).trans (QuotientGroup.ker_mk' _)
    rw [he]
    exact pCore_isPGroup
  let A₀ := (F.Li L 1).subgroupOf L
  let A := A₀.map f
  have hAL : F.Li L 1 ≤ L := (F.Li_le L 1).trans inf_le_left
  have hp₀ : IsPPerfect 2 A₀ := Li_twoPerfect.of_surjective
    (subgroupOfEquivOfLe hAL).symm.toMonoidHom (subgroupOfEquivOfLe hAL).symm.surjective
  have hp : IsPPerfect 2 A := hp₀.of_surjective (f.subgroupMap A₀) (f.subgroupMap_surjective A₀)
  have hqker : IsPGroup 2 (f.subgroupMap A₀).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let eA := subgroupOfEquivOfLe hAL
  let eQ := QuotientGroup.congr (pCore 2 A₀) (pCore 2 (F.Li L 1)) eA (pCore_map_iso 2 eA)
  let eImage := MonoidHom.quotientPCoreEquivOfSurjective (f.subgroupMap A₀)
    (f.subgroupMap_surjective A₀) hqker
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 :=
    (Nat.card_congr eImage.toEquiv).symm.trans
      ((Nat.card_congr eQ.toEquiv).trans (Li_core_quotient_card d))
  obtain ⟨S,hS⟩ := exists_L_sylow d structural
  let R := S.mapSurjective (f := f) (e₀.surjective.comp (QuotientGroup.mk'_surjective _))
  have hn₀ : (S : Subgroup L) ≤ normalizer (A₀ : Set L) := by
    rw [hS]
    exact normalized_subgroupOf _ _ _ (T_normalizes_Li (d.natural.sylow_normalizes_at structural))
  have hn : (R : Subgroup SL) ≤ normalizer (A : Set SL) :=
    (map_mono hn₀).trans (le_normalizer_map f)
  obtain ⟨_,_,_,_,g,P,hP,_,hmark,_,_⟩ := ResidualRecognition.recognize A R hp hc hn
  have hcomm : A₀ = ⁅A₀,(S : Subgroup L)⁆ :=
    eq_commutator_of_isPPerfect_of_map_eq A₀ S hp₀ hn₀ f hk
      (ResidualRecognition.commutator_sylow_eq A R hp hc hn).symm
  constructor
  · have hm := congrArg (Subgroup.map L.subtype) hcomm.symm
    rw [map_commutator,hS,map_subgroupOf_eq_of_le hAL,subgroupOf_map_subtype] at hm
    exact hm
  · refine ⟨e₀.trans (MulAut.conj g),P,hP,?_⟩
    change A₀.map ((MulAut.conj g).toMonoidHom.comp f) = residual P
    rw [← map_map]
    exact hmark
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.SectionCentralizationAt

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Chapter12.Section08 ResidualNormalizer
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The source commutator identity uses the original Sylow intersection. -/
theorem Data.Li_eq_commutator_sylow_inf_at (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    F.Li L 1 = ⁅F.Li L 1, (T : Subgroup G) ⊓ L⁆ :=
  (ResidualNormalizer.SectionCentralizationAt.Li_marking_and_commutator d structural).1.symm

/-- The actual section kernel's residual centralizes the original L quotient. -/
theorem Data.D₁_commutator_le_core_at (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    ⁅D₁ L F,L⁆ ≤ L.pCoreIn 2 := by
  have hTM := d.natural.sylow_normalizes_at structural
  have hAL : F.Li L 1 ≤ L := (F.Li_le L 1).trans inf_le_left
  have hAH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hQH : L.pCoreIn 2 ≤ F.H := by
    have hc : L.pCoreIn 2 ≤ centralizer (V : Set G) :=
      (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
        (sup_le L.le_normalizer hTM)).trans d.natural.chosen.core_centralizes
    exact (hc.trans (centralizer_le (F.le_seed 1))).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨hcomm,e,P,hP,hm⟩ := ResidualNormalizer.SectionCentralizationAt.Li_marking_and_commutator d structural
  exact ResidualNormalizer.SectionCentralizationAt.commutator_le_core L (F.Li L 1) (D₁ L F)
    ((T : Subgroup G) ⊓ L) F.H hAL inf_le_right hAH hQH
    (D₁_le.trans inf_le_right) (hAH.trans (H_normalizes_D₁ d hTM))
    (inf_le_left.trans (T_normalizes_D₁ hTM))
    ((D₁_le.trans inf_le_left).trans (D_normalizes_Li hTM))
    (T.isPGroup'.to_le ((inf_le_inf_right F.H (D₁_le.trans inf_le_left)).trans
      d.D_inf_H_le_sylow)) Li_twoPerfect D₁_twoPerfect
    ((commutator_mono (D₁_le.trans inf_le_left) le_rfl).trans (D_commutator_Li hTM))
    hcomm e P hP hm
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ResidualNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)
omit [Finite G] in
private theorem normalizes_join_of_commutator {A B X : Subgroup G}
    (hc : ⁅X, A⁆ ≤ B) (hn : X ≤ normalizer (B : Set G)) :
    X ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro x hx y hy
  have ha : A.map (MulAut.conj x).toMonoidHom ≤ A ⊔ B := by
    rintro _ ⟨a, ha, rfl⟩
    have hh := (A ⊔ B).mul_mem
      (mem_sup_right (hc (commutator_mem_commutator hx ha))) (mem_sup_left ha)
    change x * a * x⁻¹ ∈ A ⊔ B
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
  have hb : B.map (MulAut.conj x).toMonoidHom ≤ B :=
    (mem_normalizer_iff_map_conj_eq.mp (hn hx)).le
  have hjoin : (A ⊔ B).map (MulAut.conj x).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    exact sup_le ha (hb.trans le_sup_right)
  exact hjoin (mem_map_of_mem _ hy)


omit [Finite G] in
private theorem core_ne_bot_of_normalized_twoPerfect
    {X M : Subgroup G} (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M)
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hp : IsPPerfect 2 X) (hchar : HasCharacteristicTwo M) (hne : X ≠ ⊥) :
    X.pCoreIn 2 ≠ ⊥ := by
  intro hbot
  have hQT : M.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow M (T.subtype hTM)).trans_eq (map_subgroupOf_eq_of_le hTM)
  have hXQ : X ≤ normalizer (M.pCoreIn 2 : Set G) :=
    (hXM.trans M.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hi : X ⊓ M.pCoreIn 2 ≤ X.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 M).to_le inf_le_right) inf_le_left
      ((le_inf X.le_normalizer hXQ).trans inf_normalizer_le_normalizer_inf)
  have hc : X ≤ centralizer (M.pCoreIn 2 : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    rw [← hbot]
    exact (le_inf (le_normalizer_iff_commutator_le_left.mp (hQT.trans hn))
      (le_normalizer_iff_commutator_le_right.mp hXQ)).trans hi
  have hXcore : X ≤ M.pCoreIn 2 := by
    intro x hx
    have hm : (⟨x, hXM hx⟩ : M) ∈ centralizer (pCore 2 M : Set M) := by
      intro y hy
      apply Subtype.ext
      exact mem_centralizer_iff.mp (hc hx) y (mem_map.mpr ⟨y, hy, rfl⟩)
    exact mem_map.mpr ⟨⟨x, hXM hx⟩, hchar hm, rfl⟩
  have he := hp.hom_eq_one_of_isPGroup ((isPGroup_pCoreIn 2 M).to_le hXcore)
    (MonoidHom.id X)
  apply hne
  apply bot_unique
  intro x hx
  exact congrArg Subtype.val (DFunLike.congr_fun he ⟨x, hx⟩)

include d
/-- The second product-residual identity, with the original L two-core. -/
theorem D₁_L_core_residual_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    (pResidual 2 (D₁ L F ⊔ L.pCoreIn 2 : Subgroup G)).map
      (D₁ L F ⊔ L.pCoreIn 2).subtype = D₁ L F := by
  have hTM := d.natural.sylow_normalizes_at structural
  have hQLT : L.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_mono_of_normalizes (le_sup_left : L ≤ L ⊔ (T : Subgroup G))
      (sup_le L.le_normalizer hTM)).trans
      ((pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq
        (map_subgroupOf_eq_of_le le_sup_right))
  exact embedded_pResidual_join_pGroup _ _ D₁_twoPerfect (isPGroup_pCoreIn 2 _)
    (hQLT.trans (T_normalizes_D₁ hTM))

/-- Centralization on L/O₂(L) promotes normalization to all of LT. This
premise is the still separate L₃(2) section argument in the source. -/
theorem LT_normalizes_D₁_of_sectionCentralization_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hc : ⁅D₁ L F, L⁆ ≤ L.pCoreIn 2) :
    L ⊔ (T : Subgroup G) ≤ normalizer (D₁ L F : Set G) := by
  refine sup_le ?_ (T_normalizes_D₁ (d.natural.sylow_normalizes_at structural))
  have hn : L ≤ normalizer ((D₁ L F ⊔ L.pCoreIn 2 : Subgroup G) : Set G) :=
    normalizes_join_of_commutator ((commutator_comm _ _).trans_le hc)
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hr := hn.trans (normalizer_le_normalizer_characteristic_image
    (D₁ L F ⊔ L.pCoreIn 2) (pResidual 2 _))
  rwa [d.D₁_L_core_residual_at structural] at hr

/-- A nontrivial D₁ has nontrivial two-core. This is why maximal two-local
uniqueness applies to its normalizer, despite D₁ being a two-residual. -/
theorem D₁_core_ne_bot_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hne : D₁ L F ≠ ⊥) : (D₁ L F).pCoreIn 2 ≠ ⊥ := by
  have hTM := d.natural.sylow_normalizes_at structural
  exact core_ne_bot_of_normalized_twoPerfect hTM (D₁_le.trans inf_le_right)
    (T_normalizes_D₁ hTM) D₁_twoPerfect
    (d.counterexample.qtke.evenCharacteristic T _
      (d.natural.maximal_unique_at structural).1 hTM) hne

/-- The uniqueness/escape end of the D₁ argument, retaining precisely the
unproved section-centralization step as an explicit premise. -/
theorem D₁_eq_bot_of_sectionCentralization_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hc : ⁅D₁ L F, L⁆ ≤ L.pCoreIn 2) : D₁ L F = ⊥ := by
  by_contra hne
  have hTM := d.natural.sylow_normalizes_at structural
  have hchar := normalizer_le_normalizer_characteristic_image (D₁ L F) (pCore 2 (D₁ L F))
  have hn : normalizer ((D₁ L F).pCoreIn 2 : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
    · intro N hN hJN
      exact Set.mem_singleton_iff.mp ((d.natural.maximal_unique_at structural).2 ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hN, hJN⟩)
    · exact isPGroup_pCoreIn 2 _
    · exact d.D₁_core_ne_bot_at structural hne
    · exact (d.LT_normalizes_D₁_of_sectionCentralization_at structural hc).trans hchar
  exact d.K_not_le_normalizer_L hTM
    (((K_le_H F).trans (H_normalizes_D₁ d hTM)).trans (hchar.trans hn))

/-- The two intersection conclusions after the source centralization step. -/
theorem residual_intersections_of_sectionCentralization_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hc : ⁅D₁ L F, L⁆ ≤ L.pCoreIn 2) :
    D₁ L F = ⊥ ∧ D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G) := by
  have hz := d.D₁_eq_bot_of_sectionCentralization_at structural hc
  exact ⟨hz, (D₁_eq_bot_iff_inf_le_sylow (d.natural.sylow_normalizes_at structural)).mp hz⟩


/-- The actual intersection and Sylow conclusions of the local-control paragraph. -/
theorem residual_intersections_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    D₁ L F = ⊥ ∧ D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G) ∧
      D F ⊓ (T : Subgroup G) ≤ F.Ri L 1 ∧
      Chapter1.IsSylowIn 2 (F.Ri L 1) (D F ⊔ F.Ri L 1) := by
  obtain ⟨hz,hi⟩ := d.residual_intersections_of_sectionCentralization_at structural
    (d.D₁_commutator_le_core_at structural)
  exact ⟨hz,hi,d.D_inf_T_le_Ri,d.Ri_isSylowIn_D_sup_Ri⟩
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
