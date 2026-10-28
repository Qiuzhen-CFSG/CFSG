module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledLinearOddDisplacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearSharpR
-- Retain the exact original component quotient and paired action marking.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearRank

/-!
# Original nonbinary beta and sharp r bounds

The SQTK cover is the literal normalizer of the nontrivial elementary whole
orbit. The original component image is normal in the actual automizer; its
surjective full-SL₃ marking puts the entire component in the covered native
normalizer image. Thus H.4 beta applies with rank on the original cover.
E.6.27 now gives the unconditional sharp r bound for this original branch.
Source: Aschbacher--Smith H.4.1, 7.4.1 and E.6.27, pp.383--385,700,257.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE

private theorem beta_of_marked_pair
    {H J U K : Type*} [Group H] [Group J] [Group K] [Finite K]
    [AddCommGroup U] [Module (ZMod 2) U]
    (F : BinaryField) (a : MulAut (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
    (hne : ¬ Nonempty ((linearNatural F 3).Equiv
      ((linearNatural F 3).comp a.toMonoidHom)))
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (i : J →* H) [i.range.Normal]
    (q : J →* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) (hq : Function.Surjective q)
    (E : U ≃ₗ[ZMod 2] ((Fin 3 → F.Carrier) × (Fin 3 → F.Carrier)))
    (hE : ∀ l v, E (ρ (i l) v)=((linearNatural F 3).prod
      ((linearNatural F 3).comp a.toMonoidHom)) (q l) (E v))
    (f : K →* H) (hfs : Function.Surjective f)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : primeRank p K ≤ 2)
    (x : H) (hx : orderOf x=p) : 4*F.degree ≤ fixedCodim ρ (zpowers x) := by
  let μ := (linearNatural F 3).prod ((linearNatural F 3).comp a.toMonoidHom)
  let γ : Representation (ZMod 2) H ((Fin 3 → F.Carrier) × (Fin 3 → F.Carrier)) :=
    E.conjRingEquiv.toMonoidHom.comp ρ
  have he (g : H) (v : U) : E (ρ g v)=γ g (E v) := by
    change E (ρ g v)=E (ρ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hγ : Function.Injective γ := E.conjRingEquiv.injective.comp hρ
  have hres (l : J) : γ (i l)=μ (q l) := by
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := E.surjective w
    rw [←he]
    exact hE l v
  have himage : i.range.map γ.asGroupHom=actionImage μ := by
    ext z
    constructor
    · rintro ⟨_,⟨l,rfl⟩,rfl⟩
      exact ⟨q l,Units.ext (hres l).symm⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨i l,⟨l,rfl⟩,Units.ext (hres l)⟩
  have hn (g : H) : γ.asGroupHom g ∈ linearNormalizer μ := by
    change γ.asGroupHom g ∈ normalizer (actionImage μ : Set _)
    rw [←himage]
    exact i.range.le_normalizer_map γ.asGroupHom
      (mem_map_of_mem _ (show g ∈ normalizer (i.range : Set H) from
        le_normalizer_of_normal (mem_top g)))
  let j : H →* linearNormalizer μ := γ.asGroupHom.codRestrict _ hn
  have hj : Function.Injective j := by
    intro x y hxy
    exact hγ (congrArg (fun z : linearNormalizer μ => z.val.val) hxy)
  have hinner (g) : normalizerEmbedding μ g ∈ (j.comp f).range := by
    obtain ⟨l,rfl⟩ := hq g
    obtain ⟨k,hk⟩ := hfs (i l)
    refine ⟨k,?_⟩
    change j (f k)=normalizerEmbedding μ (q l)
    rw [hk]
    apply Subtype.ext
    exact Units.ext (hres l)
  have hb := doubledLinear_normalizer_odd_displacement_of_cover F a hne (j.comp f)
    hinner hp ho hr (j x) ((orderOf_injective j hj x).trans hx) (by
      obtain ⟨k,hk⟩ := hfs x
      exact ⟨k,congrArg j hk⟩)
  have hc := fixedCodim_map_equivariant ρ (normalizerRepresentation μ) j E he (zpowers x)
  rw [MonoidHom.map_zpowers] at hc
  rwa [←hc] at hb

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The H.4 beta bound on the literal original whole-orbit automizer. -/
theorem sourceOrbit_linear_odd_prime_fixedCodim
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (x : Automizer D.sourceOrbit) (hx : orderOf x=p) :
    4*F.degree ≤ fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers x) := by
  obtain ⟨a,q,hq,hne,E,hE⟩ := D.original_twisted_coordinates h hd F hmodel
  let W := D.sourceOrbit
  let N := normalizer (W : Set G)
  let qN := W.normalizerMonoidHom.rangeRestrict
  let i : L →* Automizer W := qN.comp (inclusion D.sourceOrbit_component_normalizes)
  have hi : i.range=(L.subgroupOf N).map qN := by
    ext z
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨inclusion D.sourceOrbit_component_normalizes l,l.property,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
  let : (L.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)
  let : i.range.Normal := hi ▸ Normal.map inferInstance qN
    W.normalizerMonoidHom.rangeRestrict_surjective
  have hsq : IsSQTK KnownSimple.IsKnownSimple N :=
    h.simpleQTKE.twoLocal_sqtk ⟨W,D.sourceOrbit_weakClosure_setup.nontrivial,
      IsElementaryAbelian.isPGroup 2 W,rfl⟩
  exact beta_of_marked_pair F a hne (automizerRepresentation W)
    (automizerRepresentation_injective W) i q hq E hE qN
    W.normalizerMonoidHom.rangeRestrict_surjective hp ho (hsq.stronglyQuasithin p hp ho) x hx

/-- Every original subspace of corank below 4n has its full centralizer in N(L). -/
theorem sourceOrbit_linear_small_centralizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (U : Subgroup G) (hUW : U ≤ D.sourceOrbit)
    (hsmall : subgroupCorank D.sourceOrbit U < 4*F.degree) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) :=
  D.sourceOrbit_linear_centralizer_le_of_odd_fixedCodim h hd F hn hmodel
    (D.sourceOrbit_linear_odd_prime_fixedCodim h hd F hmodel) U hUW hsmall

/-- The genuine sharp 7.4.1 bound for the original nonbinary doubled row. -/
theorem sourceOrbit_linear_globalR
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) : ((4*F.degree : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit :=
  D.sourceOrbit_linear_globalR_of_odd_fixedCodim h hd F hn hmodel
    (D.sourceOrbit_linear_odd_prime_fixedCodim h hd F hmodel)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
