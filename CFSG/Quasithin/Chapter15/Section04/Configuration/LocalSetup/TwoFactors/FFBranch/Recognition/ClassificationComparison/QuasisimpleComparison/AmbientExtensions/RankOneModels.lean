module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.Targets
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.AmbientExtensions.Rows
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import Theory.SpecificGroups.SL2.NineFieldExtension
public import GorensteinWalter.PSL2PerfectOfCard
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.CComponent.QuasisimpleFactors


/-!
# The rank-one rows in the ambient FF comparison

The small actor bounds the odd prime divisors of the ambient group. In row (6),
the defining prime is therefore at most seven. The source congruence and degree
bound leave q = 7, 9, 25; the actual PSL₂(25) order introduces the forbidden
prime thirteen. The checked exceptional action comparisons identify the two
remaining PSL₂ groups with SL₃(2) and A₆. The genuine triple-six cover is retained.

In row (8), the prime congruence leaves p = 3. The actual cubic-Frobenius action
on PSL₂(9) identifies its extension with S₆ by the new intrinsic field-extension
comparison. That comparison proves the outside lift is an involution; splitting
is not part of the source input. The triple-symmetric cover keeps its given map.

The marked result identifies the image of F*(N), for the original offender N,
with the whole ordinary model in row (6) and the embedded A₆ in row (8). It also
specializes the original offender, quotient, derived, centralizer and
representation maps. Neither actor pruning nor N = D is assumed. The public
`rankOne_model` discharges exactly these two rows conditional on the supplied
small actor; exhaustive ambient assembly stays with `AmbientExtensions`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.6.18(6),(8), pp.309–310; B.5.1/B.5.6, pp.99–110;
K.1.3, p.453; and 15.4.18, p.1163. The exceptional isomorphisms retain their
ATLAS attribution and license in the imported Theory modules.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace QuasisimpleComparison.AmbientExtensions
open GoldschmidtAlternatives
universe u v w
variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D} {K : GroupClass.{u}}

private theorem definingPrime_dvd {F : Type*} [Field F] [Finite F]
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (hF : Nat.card F = p ^ e) : p ∣ Nat.card PSL(2,F) := by
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ ho.pow)
  have hd : p ∣ Nat.card PSL(2,F) * 2 := by
    rw [hc, hF]
    exact (dvd_pow_self p (Nat.ne_of_gt he)).trans (dvd_mul_right _ _)
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact hd
  · have hh := Nat.le_of_dvd (by decide : 0 < 2) hd
    have := hp.two_le
    have := Nat.odd_iff.mp ho
    omega

/-- Only the seven- and nine-element fields survive the literal row (6) restrictions. -/
theorem rankOne_parameter (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) {p e : ℕ}
    (hp : p.Prime) (he : 0 < e) (he2 : e ≤ 2)
    (hq : p ^ e % 16 = 7 ∨ p ^ e % 16 = 9)
    (hm : ClassicalGroup.IsPSL D 2 (p ^ e)) : p ^ e = 7 ∨ p ^ e = 9 := by
  have ho : Odd p := hp.odd_of_ne_two (by
    rintro rfl
    interval_cases e <;> norm_num at hq)
  obtain ⟨F, _, _, hF, ⟨f⟩⟩ := hm
  have hd : p ∣ Nat.card D := by
    rw [Nat.card_congr f.toEquiv]
    exact definingPrime_dvd hp ho he hF
  have hl : p ≤ 7 := by
    by_contra hn
    exact no_large_prime h s hp (by omega) hd
  have hp2 := hp.two_le
  have hsmall : p ^ e = 7 ∨ p ^ e = 9 ∨ p ^ e = 25 := by
    interval_cases p <;> interval_cases e <;> omega
  rcases hsmall with h7 | h9 | h25
  · exact Or.inl h7
  · exact Or.inr h9
  · have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F)
      (hF ▸ ho.pow)
    rw [hF, h25] at hc
    have hd13 : 13 ∣ Nat.card D := by
      rw [Nat.card_congr f.toEquiv]
      have hn : Nat.card PSL(2,F) = 7800 := by omega
      rw [hn]
      decide
    exact (no_large_prime h s (by decide : Nat.Prime 13) (by decide) hd13).elim

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private noncomputable def psl2Card7EquivSl3Two {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 7) : PSL(2,F) ≃* SL(3,ZMod 2) := by
  letI : Fintype F := Fintype.ofFinite F
  let e : F ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq (K := F) (K' := ZMod 7) (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact (Atlas.fieldEquivPSL 2 e).trans
    Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two

/-- The complete sixth row gives an actual small ambient model, retaining the cover. -/
theorem case6_model (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : Case6 G₁ G₂) :
    SmallAmbientModel D := by
  rcases hr.1 with hc | ⟨p, e, hp, he, he2, hq, hm⟩
  · exact Or.inl (.tripleSix hc)
  · have hq' := rankOne_parameter h s hp he he2 hq hm
    obtain ⟨F, _, _, hF, ⟨f⟩⟩ := hm
    rcases hq' with h7 | h9
    · exact Or.inl (.linearThree (f.trans (psl2Card7EquivSl3Two (hF.trans h7))))
    · exact Or.inl (.alternatingSix (f.trans
        (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 (hF.trans h9))))

/-- The embedded PSL₂ in the eighth row forces the defining prime to be three. -/
theorem fieldExtension_parameter (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) {p : ℕ}
    (hp : p.Prime) (hp8 : p % 8 = 3) (hm : FieldExtension D p) : p = 3 := by
  obtain ⟨F, _, _, hF, _, _, i, _, hi, _⟩ := hm
  have ho := hp.odd_of_ne_two (by omega)
  have hd := (definingPrime_dvd hp ho (by decide : 0 < 2) hF).trans
    (card_dvd_of_injective i hi)
  have hl : p ≤ 7 := by
    by_contra hn
    exact no_large_prime h s hp (by omega) hd
  omega

/-- Retain the genuine triple cover or the precise cubic-Frobenius extension. -/
theorem case8_reduction (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : Case8 G₁ G₂) :
    TripleSymmetric D 6 ∨ FieldExtension D 3 := by
  rcases hr.1 with hc | ⟨p, hp, hp8, hm⟩
  · exact Or.inl hc
  · exact Or.inr (fieldExtension_parameter h s hp hp8 hm ▸ hm)

attribute [local instance] offenderSubgroup_normal

/-- All subgroup and action maps refer to the original offender subgroup. -/
structure RankOneMarking {M : Type w} [Group M] (ρ : Representation (ZMod 2) D V)
    (e : D ≃* M) : Prop where
  fitting : (componentImage ρ).map e.toMonoidHom = generalizedFitting M
  residual : (componentImage ρ).map e.toMonoidHom = pResidual 2 M
  restriction :
    ((ρ.comp e.symm.toMonoidHom).comp
      ((offenderSubgroup ρ).map e.toMonoidHom).subtype).comp
        (offenderEquiv (ρ := ρ) e).toMonoidHom = ρ.comp (offenderSubgroup ρ).subtype
  quotient : letI := offenderImage_normal (ρ := ρ) e
    ∀ x : D, offenderQuotientEquiv (ρ := ρ) e (QuotientGroup.mk' (offenderSubgroup ρ) x) =
      QuotientGroup.mk' ((offenderSubgroup ρ).map e.toMonoidHom) (e x)
  derived :
    ((commutator (offenderSubgroup ρ)).map (offenderSubgroup ρ).subtype).map e.toMonoidHom =
      (commutator ((offenderSubgroup ρ).map e.toMonoidHom)).map
        ((offenderSubgroup ρ).map e.toMonoidHom).subtype
  centralizer :
    (centralizer (offenderSubgroup ρ : Set D)).map e.toMonoidHom =
      centralizer ((offenderSubgroup ρ).map e.toMonoidHom : Set M)

/-- Apply all published structural markings to one constructed ambient equivalence. -/
theorem rankOneMarking (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    {M : Type w} [Group M] (e : D ≃* M) : RankOneMarking ρ e := by
  refine ⟨?_, ?_, marked_restriction e, ?_, marked_derived e, marked_centralizer e⟩
  · rw [← fitting_eq_componentImage h b]
    exact map_generalizedFitting_equiv e
  · rw [← residual_eq_componentImage h b]
    exact map_pResidual_of_surjective 2 e.toMonoidHom e.surjective
  · exact offenderQuotientEquiv_mk e

/-- Exact rank-one models, with the embedded component and the literal action
marked in each ordinary model. The two covering alternatives retain their maps. -/
inductive RankOneModel (ρ : Representation (ZMod 2) D V) : Prop
  | linearThree (e : D ≃* SL(3,ZMod 2)) (marking : RankOneMarking ρ e)
      (component : (componentImage ρ).map e.toMonoidHom = ⊤)
  | alternatingSix (e : D ≃* alternatingGroup (Fin 6)) (marking : RankOneMarking ρ e)
      (component : (componentImage ρ).map e.toMonoidHom = ⊤)
  | symmetricSix (e : D ≃* Equiv.Perm (Fin 6)) (marking : RankOneMarking ρ e)
      (component : (componentImage ρ).map e.toMonoidHom = alternatingGroup (Fin 6))
  | tripleSix (cover : TripleAlternating D 6)
  | tripleSymmetricSix (cover : TripleSymmetric D 6)

omit [Finite D] in
/-- Forget the additional markings only after constructing the actual models. -/
theorem RankOneModel.smallAmbientModel (r : RankOneModel ρ) : SmallAmbientModel D := by
  cases r with
  | linearThree e _ _ => exact Or.inl (.linearThree e)
  | alternatingSix e _ _ => exact Or.inl (.alternatingSix e)
  | symmetricSix e _ _ => exact Or.inl (.symmetricSix e)
  | tripleSix hc => exact Or.inl (.tripleSix hc)
  | tripleSymmetricSix hc => exact Or.inr hc

private theorem pslTwo_quasisimple {F : Type*} [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F) : IsQuasisimple PSL(2,F) := by
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F) hF
  refine { toIsPerfect := GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by omega)
           simple := ?_ }
  exact ((QuotientGroup.quotientMulEquivOfEq (GorensteinWalter.psl2_center_eq_bot F)).trans
    QuotientGroup.quotientBot).isSimpleGroup

private theorem whole_component (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    {F : Type*} [Field F] [Finite F] (hF : 4 ≤ Nat.card F)
    (f : D ≃* PSL(2,F)) : componentImage ρ = ⊤ := by
  let := pslTwo_quasisimple hF
  let := IsQuasisimple.of_mulEquiv f.symm
  rw [← fitting_eq_componentImage h b, generalizedFitting_eq_top_of_quasisimple]

/-- Recognize row (6), and carry the actual embedded component to the whole model. -/
theorem case6_marked_model (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : Case6 G₁ G₂) :
    RankOneModel ρ := by
  rcases hr.1 with hc | ⟨p, e, hp, he, he2, hq, hm⟩
  · exact .tripleSix hc
  · have hq' := rankOne_parameter h s hp he he2 hq hm
    obtain ⟨F, _, _, hF, ⟨f⟩⟩ := hm
    have hcomp := whole_component h b (by omega : 4 ≤ Nat.card F) f
    rcases hq' with h7 | h9
    · let e := f.trans (psl2Card7EquivSl3Two (hF.trans h7))
      exact .linearThree e (rankOneMarking h b e)
        (by rw [hcomp]; exact map_top_of_surjective _ e.surjective)
    · let e := f.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 (hF.trans h9))
      exact .alternatingSix e (rankOneMarking h b e)
        (by rw [hcomp]; exact map_top_of_surjective _ e.surjective)

/-- The actual quadratic-field extension at p = 3 has component image A₆ in S₆. -/
theorem fieldExtension_marked_model (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (hm : FieldExtension D 3) : RankOneModel ρ := by
  obtain ⟨F, _, _, hF, σ, hs, i, t, hi, htwo, ht, hact⟩ := hm
  have h9 : Nat.card F = 9 := by simpa using hF
  obtain ⟨e, he, _⟩ := Atlas.Comparisons.Exceptional.NineFieldExtension.exists_equiv
    h9 σ hs i hi htwo t ht hact
  have hmap : i.range.map e.toMonoidHom = alternatingGroup (Fin 6) := by
    ext g
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      change e (i x) ∈ alternatingGroup (Fin 6)
      rw [he]
      exact (Atlas.Comparisons.Exceptional.NineFieldExtension.componentEquiv h9 x).property
    · intro hg
      obtain ⟨x, hx⟩ :=
        (Atlas.Comparisons.Exceptional.NineFieldExtension.componentEquiv h9).surjective ⟨g, hg⟩
      refine ⟨i x, ⟨x, rfl⟩, ?_⟩
      change e (i x) = g
      rw [he, hx]
  let := pslTwo_quasisimple (by omega : 4 ≤ Nat.card F)
  have hcomp : componentImage ρ = i.range := by
    rw [← fitting_eq_componentImage h b]
    exact generalizedFitting_eq_range_of_quasisimple_index_two i hi htwo h.twoCore
  exact .symmetricSix e (rankOneMarking h b e) (hcomp ▸ hmap)

/-- Recognize the complete eighth row, including the genuine triple-symmetric cover. -/
theorem case8_marked_model (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : Case8 G₁ G₂) :
    RankOneModel ρ := by
  rcases case8_reduction h s hr with hc | hm
  · exact .tripleSymmetricSix hc
  · exact fieldExtension_marked_model h b hm

/-- Both complete literal rank-one rows give the intended ambient catalogue,
with the original component, offender, quotient and representation maps. -/
theorem rankOne_marked_model (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : RankOneRows G₁ G₂) :
    RankOneModel ρ := by
  rcases hr with hr | hr
  · exact case6_marked_model h b s hr
  · exact case8_marked_model h b s hr

/-- Discharge both literal rank-one rows for the original ambient group. -/
theorem rankOne_model (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : RankOneRows G₁ G₂) :
    SmallAmbientModel D := (rankOne_marked_model h b s hr).smallAmbientModel

/-- The complete eighth row supplies the small ambient catalogue. -/
theorem case8_model (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : Case8 G₁ G₂) :
    SmallAmbientModel D := (case8_marked_model h b s hr).smallAmbientModel

/-- The rank-one alternatives in `comparison_reduction` allow either naming
of the generating pair. Both give the same marked original offender subgroup. -/
theorem rankOne_model_either_orientation (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (s : SmallActorModel (offenderSubgroup ρ))
    (hr : RankOneRows G₁ G₂ ∨ RankOneRows G₂ G₁) : SmallAmbientModel D := by
  rcases hr with hr | hr
  · exact rankOne_model h b s hr
  · let h' : ProjectiveLine.ClassifiedAction K ρ G₂ G₁ :=
      ⟨h.faithful, h.twoCore, h.threePrimeCore, h.triple.symm, h.goldschmidt.symm,
        h.ffHypothesis, h.ffWitness, h.ffAlternatives, h.quotient_twoGroup, h.sylow_fixedSpace⟩
    exact rankOne_model h' b s hr

end QuasisimpleComparison.AmbientExtensions
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
