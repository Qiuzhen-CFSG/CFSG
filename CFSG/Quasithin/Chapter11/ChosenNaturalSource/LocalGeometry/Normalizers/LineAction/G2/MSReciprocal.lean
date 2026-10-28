module
public import Theory.Representation.G2NaturalNormalizerOffenders
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.SymplecticFourOrthogonalCover.EmbeddedProjectionAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.MSGeometry

/-!
# Reciprocal G₂(4) fixed-space bounds

An offender in a faithful ambient natural G₂(4) action is inner and has
binary rank and fixed codimension six. Comparing the two reciprocal indices
therefore makes both elementary images offenders of order 64. A literal
surjective subgroup projection supplies the needed fixed-space bound from
the original centralizer index, retaining its kernel.

MSCriticalActors applies these facts to the constructed source vertex actions.
This is the initial reciprocal comparison in MS93 (3.2), pp.865--866; the
later comparison of field structures, and hence the G₂ exclusion, remains
with the line-action owner.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS

private def binaryLinearEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module (ZMod 2) A] [Module (ZMod 2) B] (e : A ≃+ B) : A ≃ₗ[ZMod 2] B :=
  { e with map_smul' := ZMod.map_smul e }

private theorem ambient_offender_le_additive
    {J W F : Type*} [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    [Field F] [Finite F] [CharP F 2]
    (ρ : Representation (ZMod 2) J W) (B : Subgroup J) [B.Normal]
    (e : B ≃* Atlas.G2.Model F) (E : W ≃+ Atlas.G2.Natural.Space F)
    (he : ∀ (b : B) v, E (ρ (b : J) v) = Atlas.G2.Natural.action F (e b) (E v))
    (hf : Function.Injective ρ) (hc : Nat.card F = 4)
    (A : Subgroup J) (hA : IsOffender ρ A) : A ≤ B := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  apply Atlas.G2.Natural.Normalizer.ambient_offender_le F ρ B e
    (binaryLinearEquiv E) he hf (by decide : 2 ≤ 2) hc hA

/-- A genuine offender in the full natural G₂(4) normalizer is inner, of
binary rank six, with precisely six dimensions of movement. -/
theorem ambient_offender_rank_six
    {J : Type*} [Group J] [Finite J] (F : BinaryField) (hF : F.degree = 2)
    (ρ : Representation (ZMod 2) J (Atlas.G2.Natural.Space F.Carrier))
    (B : Subgroup J) [B.Normal] (e : B ≃* Atlas.G2.Model F.Carrier)
    (he : ∀ (b : B) v, ρ (b : J) v = Atlas.G2.Natural.action F.Carrier (e b) v)
    (hf : Function.Injective ρ) (A : Subgroup J) (hA : IsOffender ρ A) :
    A ≤ B ∧ rank A = 6 ∧ fixedCodim ρ A = 6 := by
  have hc : Nat.card F.Carrier = 2^2 := by rw [F.card_eq,hF]
  have hAB := ambient_offender_le_additive ρ B e (AddEquiv.refl _) he hf hc A hA
  have ho := (hA.subgroupOf ρ hAB).map_equivariant (ρ.comp B.subtype)
    (Atlas.G2.NaturalOffenders.binaryNatural (F := F.Carrier))
    e.toMonoidHom e.injective (@binaryLinearEquiv _ _ _ _ _ _ (AddEquiv.refl _)) (fun b v => he b v)
  have hr := Atlas.G2.NaturalOffenders.natural_offender_rank hc (by decide : 0 < 2) _ ho
  have hd := Atlas.G2.NaturalOffenders.natural_offender_fixedCodim hc (by decide : 0 < 2) _ ho
  rw [rank_map_injective _ e.injective,rank_subgroupOf hAB] at hr
  have hde := fixedCodim_map_equivariant (ρ.comp B.subtype)
    (Atlas.G2.NaturalOffenders.binaryNatural (F := F.Carrier)) e.toMonoidHom
    (@binaryLinearEquiv _ _ _ _ _ _ (AddEquiv.refl _)) (fun b v => he b v) (A.subgroupOf B)
  rw [fixedCodim_subgroupOf ρ hAB,hd] at hde
  exact ⟨hAB,hr,hde⟩

/-- Reciprocal natural fixed-space bounds force both critical actors to be
inner offenders of order 64. The two coefficient fields may be different. -/
theorem reciprocal_natural_indices
    {J₁ J₂ : Type*} [Group J₁] [Group J₂] [Finite J₁] [Finite J₂]
    (F₁ F₂ : BinaryField) (hF₁ : F₁.degree = 2) (hF₂ : F₂.degree = 2)
    (ρ₁ : Representation (ZMod 2) J₁ (Atlas.G2.Natural.Space F₁.Carrier))
    (ρ₂ : Representation (ZMod 2) J₂ (Atlas.G2.Natural.Space F₂.Carrier))
    (B₁ : Subgroup J₁) [B₁.Normal] (B₂ : Subgroup J₂) [B₂.Normal]
    (e₁ : B₁ ≃* Atlas.G2.Model F₁.Carrier) (e₂ : B₂ ≃* Atlas.G2.Model F₂.Carrier)
    (he₁ : ∀ (b : B₁) v, ρ₁ (b : J₁) v = Atlas.G2.Natural.action F₁.Carrier (e₁ b) v)
    (he₂ : ∀ (b : B₂) v, ρ₂ (b : J₂) v = Atlas.G2.Natural.action F₂.Carrier (e₂ b) v)
    (hf₁ : Function.Injective ρ₁) (hf₂ : Function.Injective ρ₂)
    (A₁ : Subgroup J₁) (A₂ : Subgroup J₂)
    (hA₁ : IsElementaryTwo A₁) (hA₂ : IsElementaryTwo A₂)
    (h₁₂ : 2 ^ fixedCodim ρ₁ A₁ ≤ Nat.card A₂)
    (h₂₁ : 2 ^ fixedCodim ρ₂ A₂ ≤ Nat.card A₁) :
    A₁ ≤ B₁ ∧ A₂ ≤ B₂ ∧ Nat.card A₁ = 64 ∧ Nat.card A₂ = 64 ∧
      fixedCodim ρ₁ A₁ = 6 ∧ fixedCodim ρ₂ A₂ = 6 := by
  rw [hA₂.card_eq_two_pow_rank,Nat.pow_le_pow_iff_right (by decide : 1 < 2)] at h₁₂
  rw [hA₁.card_eq_two_pow_rank,Nat.pow_le_pow_iff_right (by decide : 1 < 2)] at h₂₁
  have hboth : IsOffender ρ₁ A₁ ∧ IsOffender ρ₂ A₂ := by
    by_cases hle : rank A₂ ≤ rank A₁
    · have ha : IsOffender ρ₁ A₁ := ⟨hA₁,h₁₂.trans hle⟩
      obtain ⟨_,hr,hd⟩ := ambient_offender_rank_six F₁ hF₁ ρ₁ B₁ e₁ he₁ hf₁ A₁ ha
      exact ⟨ha,hA₂,by omega⟩
    · have hb : IsOffender ρ₂ A₂ := ⟨hA₂,h₂₁.trans (by omega)⟩
      obtain ⟨_,hr,hd⟩ := ambient_offender_rank_six F₂ hF₂ ρ₂ B₂ e₂ he₂ hf₂ A₂ hb
      exact ⟨⟨hA₁,by omega⟩,hb⟩
  obtain ⟨hb₁,hr₁,hd₁⟩ := ambient_offender_rank_six F₁ hF₁ ρ₁ B₁ e₁ he₁ hf₁ A₁ hboth.1
  obtain ⟨hb₂,hr₂,hd₂⟩ := ambient_offender_rank_six F₂ hF₂ ρ₂ B₂ e₂ he₂ hf₂ A₂ hboth.2
  exact ⟨hb₁,hb₂,by rw [hA₁.card_eq_two_pow_rank,hr₁];rfl,
    by rw [hA₂.card_eq_two_pow_rank,hr₂];rfl,hd₁,hd₂⟩

/-- A natural quotient of the literal moving subgroup bounds its fixed-space
index by the original centralizer index. -/
theorem natural_fixed_index_le
    {G J W : Type*} [Group G] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W]
    (ρ : Representation (ZMod 2) J W)
    (U A : Subgroup G) [Finite U] (hn : A ≤ normalizer (U : Set G))
    (π : U →* Multiplicative W) (hp : Function.Surjective π) (δ : A →* J)
    (hact : ∀ (a : A) (u : U),
      π ⟨a.val*u.val*a.val⁻¹,(mem_normalizer_iff.mp (hn a.property) u).mp u.property⟩ =
        Multiplicative.ofAdd (ρ (δ a) (π u).toAdd)) :
    2 ^ fixedCodim ρ δ.range ≤ (centralizer (A : Set G)).relIndex U := by
  let P := fixedSpace ρ δ.range
  let f : U →* Multiplicative (W ⧸ P) := P.mkQ.toAddMonoidHom.toMultiplicative.comp π
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨w,hw⟩ := P.mkQ_surjective v.toAdd
    obtain ⟨u,hu⟩ := hp (Multiplicative.ofAdd w)
    refine ⟨u,?_⟩
    change Multiplicative.ofAdd (P.mkQ (π u).toAdd)=v
    rw [hu,toAdd_ofAdd,hw,ofAdd_toAdd]
  have hker : (centralizer (A : Set G)).subgroupOf U ≤ f.ker := by
    intro u hu
    change P.mkQ (π u).toAdd=0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rintro ⟨g,⟨a,rfl⟩⟩
    have hconj : a.val*u.val*a.val⁻¹=u.val := by
      have hc : a.val*u.val=u.val*a.val := hu a.val a.property
      rw [hc,mul_inv_cancel_right]
    have hh := hact a u
    have he : (⟨a.val*u.val*a.val⁻¹,
      (mem_normalizer_iff.mp (hn a.property) u).mp u.property⟩ : U)=u := Subtype.ext hconj
    rw [he] at hh
    exact congrArg Multiplicative.toAdd hh.symm
  have hidx : f.ker.index = 2 ^ fixedCodim ρ δ.range := by
    rw [index_ker,f.range_eq_top_of_surjective hf,Nat.card_congr
      (topEquiv : (⊤ : Subgroup (Multiplicative (W ⧸ P))) ≃* _).toEquiv]
    change Nat.card (W ⧸ P) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    rfl
  rw [←hidx]
  change f.ker.index ≤ ((centralizer (A : Set G)).subgroupOf U).index
  have h := relIndex_le_of_le_left (L := (⊤ : Subgroup U)) hker index_ne_zero_of_finite
  simpa only [relIndex_top_right] using h

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
