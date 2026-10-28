module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.Flags
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import Theory.SpecificGroups.Janko1.Model.SylowTwo
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.GroupAction.InnerSylow

/-!
# The inner action forced by the actual J₁ quotient

Every automorphism of J₁ is inner. The image of T acting on K/O₂(K) is
a two-group containing the inner image of its actual Sylow subgroup, so
it acts through that Sylow. Since the J₁ Sylow is elementary abelian,
this action fixes the Sylow pointwise. The restricted quotient kernel on
the flag residual Y lies in O₂(Y); hence the original T-action fixes a
Sylow subgroup of Y/O₂(Y) pointwise. Binary PSL₂ Sylow-fixer rigidity
then makes this original quotient action inner.

The source application retains the actual inclusions, quotient maps and
conjugation actions. Recognition of the J₁ quotient remains with the
assembly owner qt-d-1222-natural-line-action; the inner-action clause is
derived here without a field-four or exceptional-configuration premise.
Source: Aschbacher--Smith, 3.3.12(3b) and 3.3.16, printed pp.589--591.
-/

public noncomputable section
open Subgroup

private theorem marked_janko_aut_inner {K : Type*} [Group K]
    (e : K ≃* Janko1.Model) (a : MulAut K) : a ∈ MulAut.innerSubgroup K := by
  obtain ⟨g,hg⟩ := Janko1.OuterCertificate.aut_inner (MulAut.congr e a)
  refine ⟨e.symm g,?_⟩
  ext x
  apply e.injective
  have hx := DFunLike.congr_fun hg (e x)
  simpa only [MulAut.conj_apply,MulAut.congr_apply,MulEquiv.trans_apply,e.symm_apply_apply,
    e.apply_symm_apply,map_mul,map_inv] using hx

private theorem marked_janko_two_action_fixes_sylow {K : Type*} [Group K] [Finite K]
    (e : K ≃* Janko1.Model) (P : Sylow 2 K) (A : Subgroup (MulAut K))
    (hA : IsPGroup 2 A) (hP : (P : Subgroup K).map MulAut.conj ≤ A)
    (a : MulAut K) (ha : a ∈ A) (x : K) (hx : x ∈ P) : a x = x := by
  obtain ⟨g,hg,hga⟩ := MulAut.mem_innerSylow_of_mem_inner P A hA hP ha
    (marked_janko_aut_inner e a)
  rw [←hga,MulAut.conj_apply]
  apply mul_inv_eq_iff_eq_mul.mpr
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let : IsElementaryAbelian 2 Q := Janko1.SylowTwo.elementary Q
  have hgQ : e g ∈ (Q : Subgroup Janko1.Model) := mem_map_of_mem e.toMonoidHom hg
  have hxQ : e x ∈ (Q : Subgroup Janko1.Model) := mem_map_of_mem e.toMonoidHom hx
  apply e.injective
  simpa only [Subgroup.coe_mul,map_mul] using congrArg (fun z : Q => (z : Janko1.Model))
    (isMulCommutative_iff.mp (inferInstance : IsMulCommutative Q)
      (⟨e g,hgQ⟩ : Q) ⟨e x,hxQ⟩)

private theorem binary_rank_one_sylow_fixer_inner {K : Type*} [Group K] [Finite K]
    {n : ℕ} (hm : ClassicalGroup.IsPSL K 2 (2^n)) (P : Sylow 2 K)
    (a : MulAut K) (hf : ∀ x ∈ P, a x = x) : a ∈ MulAut.innerSubgroup K := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa [Nat.card_eq_fintype_card] using hF)
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg,hga⟩ := Theory.PSL2.aut_fixing_sylow_inner Q (MulAut.congr e a) (by
    rintro x ⟨y,hy,rfl⟩
    change e (a (e.symm (e y))) = e y
    rw [e.symm_apply_apply,hf y hy])
  refine ⟨e.symm g,?_⟩
  ext x
  apply e.injective
  have hx := DFunLike.congr_fun hga (e x)
  simpa only [MulAut.conj_apply,MulAut.congr_apply,MulEquiv.trans_apply,e.symm_apply_apply,
    e.apply_symm_apply,map_mul,map_inv] using hx.symm

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c}

/-- The J₁ marking forces the original T-action on the original residual
quotient to be inner; this is not an additional exceptional-case premise. -/
theorem residual_action_inner_of_janko_containing {K : Subgroup G} (i : Fin 2)
    (hYK : f.Li i ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : K ⧸ pCore 2 K ≃* Janko1.Model) (t : (T : Subgroup G)) :
    coreQuotientAction (f.Li i) ⟨t,f.sylow_normalizes_Li i t.property⟩ ∈
      MulAut.innerSubgroup (f.Li i ⧸ pCore 2 (f.Li i)) := by
  let Y := f.Li i
  let qK := QuotientGroup.mk' (pCore 2 K)
  let α := (coreQuotientAction K).comp (inclusion hTK)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  let Pq := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 K))
  have hα : IsPGroup 2 α.range := T.isPGroup'.of_surjective α.rangeRestrict α.rangeRestrict_surjective
  have hPα : (Pq : Subgroup (K ⧸ pCore 2 K)).map MulAut.conj ≤ α.range := by
    rintro _ ⟨_,⟨y,hy,rfl⟩,rfl⟩
    have hyT : (y : G) ∈ (T : Subgroup G) := by
      exact mem_subgroupOf.mp (show y ∈ (T : Subgroup G).subgroupOf K from hP ▸ hy)
    refine ⟨⟨y,hyT⟩,?_⟩
    apply MulEquiv.ext
    intro x
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
    change coreQuotientAction K ⟨y,hTK hyT⟩ (qK k) = MulAut.conj (qK y) (qK k)
    rw [coreQuotientAction,MonoidHom.comp_apply,quotientAut_apply_mk]
    change qK (y * k * y⁻¹) = _
    rw [map_mul,map_mul,map_inv,MulAut.conj_apply]
  obtain ⟨U,hU⟩ := NormalSylowQuotientAction.intersection_sylow T Y (f.sylow_normalizes_Li i)
  let Uq := U.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  apply binary_rank_one_sylow_fixer_inner ((invariantFlag_geometry D S f).2.2.model i) Uq
  rintro _ ⟨y,hy,rfl⟩
  have hyT : (y : G) ∈ (T : Subgroup G) := by
    exact mem_subgroupOf.mp (show y ∈ (T : Subgroup G).subgroupOf Y from hU ▸ hy)
  have hyP : inclusion hYK y ∈ (P : Subgroup K) := hP.symm ▸ hyT
  have hfix := marked_janko_two_action_fixes_sylow e Pq α.range hα hPα (α t)
    ⟨t,rfl⟩ (qK (inclusion hYK y)) (mem_map_of_mem qK hyP)
  let q := qK.comp (inclusion hYK)
  have hp : IsPGroup 2 q.ker := by
    dsimp only [q,qK]
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hYK)
  have hker : q.ker ≤ pCore 2 Y := le_sSup ⟨inferInstance,hp⟩
  let aY := Y.normalizerMonoidHom ⟨t,f.sylow_normalizes_Li i t.property⟩
  have hfix' : q (aY y) = q y := by
    change coreQuotientAction K ⟨t,hTK t.property⟩ (qK (inclusion hYK y)) = _ at hfix
    rw [coreQuotientAction,MonoidHom.comp_apply,quotientAut_apply_mk] at hfix
    exact hfix
  change coreQuotientAction Y ⟨t,f.sylow_normalizes_Li i t.property⟩
    (QuotientGroup.mk' (pCore 2 Y) y) = _
  rw [coreQuotientAction,MonoidHom.comp_apply,quotientAut_apply_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  apply hker
  change q (aY y / y) = 1
  rw [map_div,hfix',div_eq_mul_inv,mul_inv_cancel]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
