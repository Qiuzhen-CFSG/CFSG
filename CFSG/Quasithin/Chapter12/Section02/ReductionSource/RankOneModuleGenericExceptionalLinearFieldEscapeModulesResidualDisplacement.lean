module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesFactorRanks
public import Theory.Representation.PSL3Four.InvolutionDisplacement

/-!
# Excluding the pure residual opposite image

If the residual-centralizer factor were trivial, the checked Cartan split
and chief count would put the entire opposite image in the original
PSL₃(4) image, with rank two. Its nonidentity elements would move at most
three dimensions in the original span action. The Frobenius nine-by-eight
subgroup in that same residual forces every involution to move at least
four dimensions, a contradiction.

Thus a contrary nonabelian span forces a nontrivial centralizer factor.
This excludes the pure residual branch; it does not exclude configurations
where both factors survive. Excluding the centralizer factor using the
original ambient geometry, and hence proving span abelianness, remains
with this source owner. The strict quadratic-ratio endpoint is unchanged.

Source: Aschbacher--Smith 5.1.23, printed pp.645--646, refs/quasithin.pdf.
Final source assembly remains qt-d-1222-linear-field-cubic-escape; the earlier
local cubic data retain their separate producer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- A contrary span has a nontrivial opposite-image factor centralizing the residual. -/
theorem linear_cubic_nonabelian_opposite_centralizer_ne_bot
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z) (hn : 1 < n)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    let s := linear_cubic_centralizer_setup h d
    let E := ((conjugate (S.W g) g).subgroupOf S.H).map (SpanAction.projection s)
    let K := ((residual H).subgroupOf S.H).map (SpanAction.projection s)
    E ⊓ centralizer (K : Set (SpanAction.Actor s)) ≠ ⊥ := by
  intro S s E K
  rcases linear_cubic_nonabelian_opposite_factor_alternative
    D h hH hK hnf hlinear hpsl c d hn hne g hg hgn with hc | ⟨hr,hEK,hm⟩
  · exact hc
  · have hEne : E ≠ ⊥ := by
      intro he
      change rank E = 2 at hr
      rw [he,Representation.BinaryOffender.rank_bot] at hr
      omega
    obtain ⟨a,ha⟩ := ne_bot_iff_exists_ne_one.mp hEne
    have ha1 : (a : SpanAction.Actor s) ≠ 1 := by
      intro he
      exact ha (Subtype.ext he)
    obtain ⟨ho,hd⟩ := hm a a.property ha1
    obtain ⟨_,F,_,_,hF,⟨e⟩⟩ := linear_cubic_residual_image h hH hK hnf hlinear d
    let k : K := ⟨a,hEK a.property⟩
    have hk : orderOf k = 2 :=
      (orderOf_injective K.subtype K.subtype_injective k).symm.trans ho
    have hb := Representation.PSL3Four.involution_fixedCodim_ge_four_of_equiv hF e
      ((SpanAction.representation s).comp K.subtype)
      ((SpanAction.representation_faithful s).comp K.subtype_injective) k hk
    have he := fixedCodim_map_equivariant ((SpanAction.representation s).comp K.subtype)
      (SpanAction.representation s) K.subtype (LinearEquiv.refl _ _) (fun _ _ => rfl)
      (zpowers k)
    rw [MonoidHom.map_zpowers] at he
    have hb' : 4 ≤ fixedCodim (SpanAction.representation s) (zpowers (a : SpanAction.Actor s)) :=
      hb.trans_eq he
    omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
