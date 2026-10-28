module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesInvolutions
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesCartanSplit

/-!
# Splitting the original opposite image by the right Cartan

The original right Cartan B embeds into the faithful span-action image,
retains order three, and lies in the original residual image K ≅ PSL₃(4).
The original diagram actor puts the opposite elementary image E in
K C(K). Coprime action by this same B now splits E into its intersections
with K and C(K): the former is [E,B], the latter is C_E(B), and they are
disjoint. All images use the original centralizer-span projection.

This discharges the possible diagonal mixing between the residual and
centralizer factors in the remaining opposite-actor obstruction. Neither
factor is asserted to vanish; excluding the full ambient configuration,
and hence the nontrivial derived fixed factor X, remains necessary for
the abelian-span conclusion. The strict quadratic-ratio endpoint remains
proved in EscapeModules.

Source: Aschbacher--Smith E.2.7 and 5.1.23, printed pp.219 and 645--646,
refs/quasithin.pdf. Final source assembly remains
qt-d-1222-linear-field-cubic-escape.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- The actual right Cartan separates the two parts of the actual opposite image. -/
theorem linear_cubic_nonabelian_opposite_cartan_split
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    let s := linear_cubic_centralizer_setup h d
    let E := ((conjugate (S.W g) g).subgroupOf S.H).map (SpanAction.projection s)
    let K := ((residual H).subgroupOf S.H).map (SpanAction.projection s)
    let R := (B.subgroupOf S.H).map (SpanAction.projection s)
    Nat.card R = 3 ∧ R ≤ K ∧
      E = (E ⊓ K) ⊔ (E ⊓ centralizer (K : Set (SpanAction.Actor s))) ∧
      E ⊓ centralizer (R : Set (SpanAction.Actor s)) =
        E ⊓ centralizer (K : Set (SpanAction.Actor s)) ∧
      ⁅E,R⁆ = E ⊓ K ∧
      Disjoint (E ⊓ K) (E ⊓ centralizer (K : Set (SpanAction.Actor s))) := by
  intro S s E K R
  let bn := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  have hga : g ∈ S.L := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨he,_⟩ := SpanAction.binary_opposite_image s bn g hga hgn
  let : IsElementaryAbelian 2 E := he
  obtain ⟨hN,hm⟩ := linear_cubic_residual_image h hH hK hnf hlinear d
  let : K.Normal := hN
  have hRK : R ≤ K := map_mono (comap_mono (Global.right_cartan_le_residual c.toCartanPair))
  have hR : Nat.card R = 3 := (d.odd_subgroup_image_card s B
    (c.right_le.trans inf_le_right) (by rw [c.right_card]; decide)).trans c.right_card
  obtain ⟨F₀,_,_,hF₀,⟨e⟩⟩ := hm
  let : Fintype F₀ := Fintype.ofFinite F₀
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite Matrix.PSL3Four.F
  let i : F₀ ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF₀,Matrix.PSL3Four.card_F])
  let j := e.trans (Atlas.fieldEquivPSL 3 i)
  exact ⟨hR,hRK,Matrix.PSL3Four.ElementaryCubicSplitting.elementary_split K E R j
    (right_cartan_normalizes_opposite_image c d s g hg) hRK hR
    (linear_cubic_nonabelian_opposite_inner D h hH hK hnf hlinear hpsl c d hne g hg hgn)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
