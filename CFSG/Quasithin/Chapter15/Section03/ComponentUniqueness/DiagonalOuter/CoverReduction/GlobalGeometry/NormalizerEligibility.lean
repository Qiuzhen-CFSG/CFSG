module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.ModelWitnesses
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.TransferGeometry
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.Quasithin.Rank

/-!
# Eligibility of the full normalizer of the central plane

The image of the cover's center is characteristic, so its full normalizer
contains I. This is a two-local subgroup outside M and contains Y₊S; hence
15.3.11(1) supplies the same Sylow subgroup S. The original C-component
belongs to the local family of the full normalizer by Definition 1.2.3.
Applying the proved deduction of 1.2.4 gives the actual larger C-component,
the quotient embedding alternatives, and normality relative to the full
normalizer.

Perfectness forces the larger component to centralize the four-group. The
nontrivial action of Y₊ therefore proves Y₊ ≰ L₁. A uniform local-cover
reduction can now be applied with all eligibility hypotheses established.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
proof of 15.3.38, printed p.1136; Definition 1.2.3 and Lemma 1.2.4, p.505.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
open Chapter1 Chapter1.Section02
universe u
variable {G : Type u} [Group G]

/-- A perfect subgroup of the normalizer of a four-group centralizes it. -/
theorem perfect_centralizes_four [Finite G] (B V : Subgroup G) [Group.IsPerfect B]
    [IsKleinFour V] (hBV : B ≤ normalizer (V : Set G)) :
    B ≤ centralizer (V : Set G) := by
  let e : V ≃ Fin 4 := Finite.equivFinOfCardEq IsKleinFour.card_four
  let π : MulAut V →* Equiv.Perm (Fin 4) :=
    e.permCongrHom.toMonoidHom.comp (MulAut.toPerm V)
  have hπ : Function.Injective π := e.permCongrHom.injective.comp
    (fun _ _ he => MulEquiv.ext (fun x => congrArg (fun f : Equiv.Perm V => f x) he))
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (MulAut V) := Group.isSolvable_of_isSolvable_injective hπ
  let ρ := V.normalizerMonoidHom.comp (inclusion hBV)
  let : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  have hr : Subsingleton ρ.range := by
    by_contra hn
    let : Nontrivial ρ.range := not_subsingleton_iff_nontrivial.mp hn
    exact Group.IsPerfect.not_isSolvable ρ.range inferInstance
  intro b hb v hv
  have he : ρ ⟨b, hb⟩ = 1 := congrArg Subtype.val
    (hr.elim (ρ.rangeRestrict ⟨b, hb⟩) 1)
  have hf := congrArg (fun a : MulAut V => (a ⟨v, hv⟩ : G)) he
  change b * v * b⁻¹ = v at hf
  exact (mul_inv_eq_iff_eq_mul.mp hf).symm

/-- This is the noncontainment needed at the larger component, derived
from its perfectness and the actual nontrivial action on V. -/
theorem yplus_not_le_perfect_normalizer [Finite G] (Yplus B V : Subgroup G)
    [Group.IsPerfect B] [IsKleinFour V]
    (hBV : B ≤ normalizer (V : Set G))
    (hY : ¬ Yplus ≤ centralizer (V : Set G)) : ¬ Yplus ≤ B :=
  fun h => hY (h.trans (perfect_centralizes_four B V hBV))

/-- Exactly the two earlier appendix inputs consumed by the existing proof
of 1.2.4; the quotient models and their hypotheses are retained. -/
structure EarlierEmbeddings (κ : GroupClass.{u}) : Prop where
  a312 : ∀ (X : Type u) [Group X] [Finite X],
    IsSQTK κ X → pCore 2 X = ⊥ → ∀ (T : Sylow 2 X) (B : Subgroup X),
    B ∈ ChapterA.Section03.localCComponents T → A312Conclusion B
  a38 : ∀ (X : Type u) [Group X] [Finite X],
    IsSQTK κ X → pCore 2 X = ⊥ → ∀ K : Subgroup X, K.IsCComponent →
    K.Normal ∨ (normalizer (K : Set X)).index = 2 ∧ NonnormalCComponentModel K

/-- The full normalizer is a genuine member of H₊. Its nontrivial two-core
comes from the central plane, not from upward monotonicity of O₂. -/
theorem normalizer_mem_outsideFamily
    {Yplus S M I L V : Subgroup G} [IsKleinFour V]
    (hI : I ∈ outsideFamily Yplus S M)
    (hIL : I ≤ normalizer (L : Set G))
    (hZ : (center L).map L.subtype = V) :
    I ≤ normalizer (V : Set G) ∧
      normalizer (V : Set G) ∈ outsideFamily Yplus S M := by
  have hIN : I ≤ normalizer (V : Set G) := by
    rw [← hZ]
    exact hIL.trans (normalizer_le_normalizer_characteristic_image L (center L))
  have hV : V ≠ ⊥ := by
    intro he
    have hc : Nat.card V = 4 := IsKleinFour.card_four
    rw [he] at hc
    norm_num at hc
  have hp : IsPGroup 2 V := IsPGroup.of_card
    (show Nat.card V = 2 ^ 2 by rw [IsKleinFour.card_four]; decide)
  have hn : IsTwoLocal (normalizer (V : Set G)) := ⟨V, hV, hp, rfl⟩
  exact ⟨hIN, ⟨⟨Chapter1.mem_H_of_isTwoLocal hn, hI.1.2.trans hIN⟩,
    fun hNM => hI.2 (hIN.trans hNM)⟩⟩

/-- Apply 1.2.4 only after constructing both the outside-family and local-family
memberships. The returned normality is intrinsic to N_G(V), and the embedding
alternatives concern the actual quotient images of the nested subgroups. -/
theorem normalizer_component_extension [Finite G]
    {κ : GroupClass.{u}} (earlier : EarlierEmbeddings κ)
    {Yplus S M I L V : Subgroup G} [IsKleinFour V]
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (hQ : ∀ H ∈ outsideFamily Yplus S M, IsSQTK κ (H ⧸ pCore 2 H))
    (hLI : L ≤ I) (hL : (L.subgroupOf I).IsCComponent)
    (hIL : I ≤ normalizer (L : Set G))
    (hZ : (center L).map L.subtype = V) :
    let N := normalizer (V : Set G)
    N ∈ outsideFamily Yplus S M ∧
      ∃ K : Subgroup N, K.IsCComponent ∧ L ≤ K.map N.subtype ∧ K.Normal ∧
        A312Embedding ((L.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)))
          (K.map (QuotientGroup.mk' (pCore 2 N))) := by
  let N := normalizer (V : Set G)
  obtain ⟨hIN, hN⟩ := normalizer_mem_outsideFamily hI hIL hZ
  obtain ⟨P, hP⟩ := hSylow N hN
  have hSI : S ≤ I := le_sup_right.trans hI.1.2
  have hSN : S ≤ N := hSI.trans hIN
  have hLN : L ≤ N := hLI.trans hIN
  have hlocal : L ∈ Chapter1.L G S :=
    mem_L_of_cComponent hI.1.1 (hSylow I hI) hLI hL
  have hLP : L.subgroupOf N ∈ Chapter1.L N (P : Subgroup N) := by
    have he : S.subgroupOf N = (P : Subgroup N) := by
      rw [← hP, subgroupOf, comap_map_eq_self_of_injective N.subtype_injective]
    rw [← he]
    exact (mem_LIn_iff_subgroupOf hSN hLN).mp ⟨hLN, hlocal⟩
  obtain ⟨K, hK, hLK, _, hemb, hnormal⟩ :=
    lemma_1_2_4_of_A_3_12_A_3_8 earlier.a312 earlier.a38 (hQ N hN) P hLP
  refine ⟨hN, K, hK, ?_, hnormal ?_, hemb⟩
  · simpa only [map_subgroupOf_eq_of_le hLN] using map_mono (f := N.subtype) hLK
  · intro x hx
    have hxL : (x : G) ∈ normalizer (L : Set G) :=
      hIL (hSI (hP ▸ mem_map.mpr ⟨x, hx, rfl⟩))
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp hxL y

/-- Reapply the local-cover reduction to the larger component with its
eligibility established. The reduction need only give the order of its center:
perfectness and containment identify the embedded center with the original V,
without making a new arbitrary choice of plane labels. -/
theorem normalizer_eq_of_uniform_cover_reduction [Finite G]
    {κ : GroupClass.{u}} (earlier : EarlierEmbeddings κ)
    (hG : IsSimpleQTKE κ G)
    {Yplus S M I L V D : Subgroup G} [IsKleinFour V]
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (hQ : ∀ H ∈ outsideFamily Yplus S M, IsSQTK κ (H ⧸ pCore 2 H))
    (hLI : L ≤ I) (hL : (L.subgroupOf I).IsCComponent)
    (hIL : I ≤ normalizer (L : Set G))
    (hZ : (center L).map L.subtype = V)
    (hLM : ¬ L ≤ M) (hrank : 2 ≤ primeRank 3 L)
    (hY : ¬ Yplus ≤ centralizer (V : Set G))
    (hgen : I = L ⊔ D ⊔ S)
    (reduce : ∀ H ∈ outsideFamily Yplus S M, ∀ B : Subgroup G,
      B ≤ H → (B.subgroupOf H).IsCComponent → (B.subgroupOf H).Normal →
      ¬ B ≤ M → primeRank 3 B = 2 → ¬ Yplus ≤ B →
      Nat.card (center B) = 4 ∧ Nonempty ((L ⧸ center L) ≃* (B ⧸ center B)) ∧
        H = B ⊔ D ⊔ S) :
    I = normalizer (V : Set G) := by
  let N := normalizer (V : Set G)
  obtain ⟨hN, K, hK, hLK, hKn, _⟩ :=
    normalizer_component_extension earlier hI hSylow hQ hLI hL hIL hZ
  let B := K.map N.subtype
  have hBN : B ≤ N := map_subtype_le _
  have hBK : B.subgroupOf N = K := by
    dsimp [B]
    rw [subgroupOf, comap_map_eq_self_of_injective N.subtype_injective]
  let : Group.IsPerfect K := hK.perfect
  let : Group.IsPerfect B := Group.IsPerfect.map N.subtype
  have hYB : ¬ Yplus ≤ B := yplus_not_le_perfect_normalizer Yplus B V hBN hY
  have htwo : IsTwoLocal N := by
    refine ⟨V, ?_, IsPGroup.of_card (n := 2)
      (by rw [IsKleinFour.card_four]; decide), rfl⟩
    intro he
    have hc : Nat.card V = 4 := IsKleinFour.card_four
    rw [he] at hc
    norm_num at hc
  have hB3 : primeRank 3 B = 2 := by
    have hB3N : primeRank 3 B ≤ primeRank 3 N := by
      rw [← primeRank_congr 3 (subgroupOfEquivOfLe hBN)]
      exact primeRank_subgroup_le 3 _
    exact le_antisymm (hB3N.trans
      ((hG.twoLocal_sqtk htwo).stronglyQuasithin 3 Nat.prime_three (by decide)))
      (hrank.trans (primeRank_mono 3 hLK))
  obtain ⟨hc, ⟨e⟩, hg⟩ := reduce N hN B hBN (hBK ▸ hK) (hBK ▸ hKn)
    (fun hBM => hLM (hLK.trans hBM)) hB3 hYB
  have hVB : V ≤ B := by
    rw [← hZ]
    exact (map_subtype_le _).trans hLK
  have hBC : B ≤ centralizer (V : Set G) := perfect_centralizes_four B V hBN
  have hVZ : V ≤ (center B).map B.subtype := by
    intro v hv
    refine mem_map.mpr ⟨⟨v, hVB hv⟩, mem_center_iff.mpr ?_, rfl⟩
    intro b
    exact Subtype.ext (hBC b.property v hv).symm
  have hzB : (center B).map B.subtype = V := by
    symm
    apply eq_of_le_of_card_ge hVZ
    rw [card_map_of_injective B.subtype_injective, hc, IsKleinFour.card_four]
  exact (normalizer_eq_of_cover_extension I L B V D S hLK hZ hzB e hgen hg).2

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
