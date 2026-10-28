module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesCartanSplit
public import Theory.SpecificGroups.PSL3Four.NormalElementaryFactors

/-!
# The ranks of the original opposite-image factors

The original Sylow diagram actor preserves the residual intersection of
the opposite elementary image. The PSL₃(4) root-plane calculation bounds
that intersection by four elements. The same original Cartan acts without
fixed points on it, ruling out order two. Thus its rank is zero or two,
and the earlier disjoint splitting adds its rank to the centralizer-factor
rank to give the original opposite rank.

If the centralizer factor is trivial, the chief count forces the residual
factor to have rank two. The actual displacement bound then puts every
nonidentity element at fixed codimension at most three. This isolates the
remaining small-involution residual case while retaining the alternative
of a nontrivial residual-centralizer factor. Neither alternative is excluded
here, and the abelian-span conclusion of 5.1.23 remains open.

All actors, kernels, and constituent markings come from the same original
centralizer-span projection. The strict quadratic-ratio endpoint remains
proved in EscapeModules. Final source assembly stays with
qt-d-1222-linear-field-cubic-escape; existence of the earlier local cubic
data retains its separate producer.

Source: Aschbacher--Smith E.2.7 and 5.1.23, printed pp.219,645--646,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- The residual factor of the original opposite image has rank zero or two.
Its complement is exactly the residual-centralizer intersection. -/
theorem linear_cubic_nonabelian_opposite_factor_ranks
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
    (rank (E ⊓ K) = 0 ∨ rank (E ⊓ K) = 2) ∧
      rank E = rank (E ⊓ K) + rank (E ⊓ centralizer (K : Set (SpanAction.Actor s))) := by
  intro S s E K
  let bn := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  have hga : g ∈ S.L := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨he,_⟩ := SpanAction.binary_opposite_image s bn g hga hgn
  let : IsElementaryAbelian 2 E := he
  obtain ⟨_,hEP,hPE⟩ := SpanAction.binary_opposite_image_core_and_normalizer s bn g hga hgn
  obtain ⟨hN,_⟩ := linear_cubic_residual_image h hH hK hnf hlinear d
  let : K.Normal := hN
  have hTC : (T : Subgroup G) ≤ S.H := le_sup_right.trans s.local_le
  let P := (T.subtype hTC).mapSurjective (SpanAction.projection_surjective s)
  obtain ⟨F,_,_,hF,j,t,a,b,ha,hb,hd⟩ :=
    linear_cubic_residual_diagram_action D h hH hK hnf hlinear d
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    simpa only [Nat.card_eq_fintype_card,show (2 : ℕ)^2 = 4 from by decide] using hF)
  have ht : SpanAction.projection s (inclusion hTC t) ∈ (P : Subgroup (SpanAction.Actor s)) :=
    mem_map_of_mem (SpanAction.projection s) t.property
  have hc : Nat.card (E ⊓ K : Subgroup (SpanAction.Actor s)) ≤ 4 :=
    Matrix.PSL3Four.NormalElementaryFactors.residual_intersection_card_le_four
      K P E hEP hPE hF j (SpanAction.projection s (inclusion hTC t)) ht a b ha hb hd
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite Matrix.PSL3Four.F
  let i : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF,Matrix.PSL3Four.card_F])
  let e := j.trans (Atlas.fieldEquivPSL 3 i)
  let R := (B.subgroupOf S.H).map (SpanAction.projection s)
  obtain ⟨hR,hRK,_⟩ :=
    linear_cubic_nonabelian_opposite_cartan_split D h hH hK hnf hlinear hpsl c d hne g hg hgn
  exact Matrix.PSL3Four.NormalElementaryFactors.split_ranks K E R e
    (right_cartan_normalizes_opposite_image c d s g hg) hRK hR
    (linear_cubic_nonabelian_opposite_inner D h hH hK hnf hlinear hpsl c d hne g hg hgn) hc

/-- If the centralizer factor disappears, the actual opposite actor has rank
two, lies in the residual, and all its involutions move at most three dimensions.
The alternative retains a nontrivial centralizer factor for the remaining exclusion. -/
theorem linear_cubic_nonabelian_opposite_factor_alternative
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
    E ⊓ centralizer (K : Set (SpanAction.Actor s)) ≠ ⊥ ∨
      (rank E = 2 ∧ E ≤ K ∧ ∀ a ∈ E, a ≠ 1 → orderOf a = 2 ∧
        fixedCodim (SpanAction.representation s) (zpowers a) ≤ 3) := by
  intro S s E K
  by_cases hz : E ⊓ centralizer (K : Set (SpanAction.Actor s)) = ⊥
  · right
    obtain ⟨hr,hsum⟩ := linear_cubic_nonabelian_opposite_factor_ranks
      D h hH hK hnf hlinear hpsl c d hne g hg hgn
    obtain ⟨_,hm,_,_,_,hmove⟩ := linear_cubic_nonabelian_opposite_involutions
      D h hpsl c d hn hne g hg hgn
    change rank E = rank (E ⊓ K) + rank (E ⊓ centralizer (K : Set (SpanAction.Actor s))) at hsum
    rw [hz,Representation.BinaryOffender.rank_bot,add_zero] at hsum
    have hrE : rank E = 2 := by
      change 1 < rank E at hm
      change rank (E ⊓ K) = 0 ∨ rank (E ⊓ K) = 2 at hr
      omega
    obtain ⟨_,_,hs,_⟩ := linear_cubic_nonabelian_opposite_cartan_split
      D h hH hK hnf hlinear hpsl c d hne g hg hgn
    change E = (E ⊓ K) ⊔ (E ⊓ centralizer (K : Set (SpanAction.Actor s))) at hs
    rw [hz,sup_bot_eq] at hs
    refine ⟨hrE,hs.le.trans inf_le_right,?_⟩
    intro a ha hn
    obtain ⟨ho,hd⟩ := hmove a ha hn
    refine ⟨ho,?_⟩
    change fixedCodim (SpanAction.representation s) (zpowers a) ≤ rank E + 1 at hd
    omega
  · exact Or.inl hz

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
