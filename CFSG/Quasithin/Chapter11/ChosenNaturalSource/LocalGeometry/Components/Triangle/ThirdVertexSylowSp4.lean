module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ThirdVertexUnitary
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RudvalisOddRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.OddRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.OddRank
public import Theory.GroupTheory.CComponent.QuotientActionDetection

/-!
# The remaining Sylow and cubic-rank comparisons at the third vertex

The original K₀ is proper in I and normalized by both T and the order-nine
Cartan X. Its normalizer in I/O₂(I) is proper by C-component minimality,
contains a full Sylow and has order divisible by 45. The exhaustive native
Sylow-overgroup calculations exclude J₂, HS and Rudvalis: the two J₂
candidates respectively lack nine and five, and the HS and Rudvalis
candidates lack nine. The original Cartan's odd order survives the actual
two-core projection; no arbitrary quotient-rank monotonicity is used.

Three-rank two excludes both linear field-five carriers and the nonsplit
elementary odd extensions. Together with the preceding two-local comparison
and ThirdVertexUnitary, the literal common-Q consumer now leaves only
SL₃(4), Sp₄(4), G₂(4), M₂₂, its triple cover, M₂₃, J₄ and the odd nilpotent
SL₂(5)-extension row. This is a partial comparison, not source 11.1.2.

The remaining rows, common-normal existence, the source SL₃(4) exclusion,
maximal-faithful placement and both orientations remain with
qt-d-1222-natural-relative-components. Earlier flag and Cartan inputs retain
their existing producers and final discharge by
qt-d-1222-natural-local-geometry. All public predecessors are preserved.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
A.3.14 and 11.1.2, printed pp.49--50,762--764. Native sporadic subgroup
calculations retain their existing ATLAS attribution and checked coverage.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
public noncomputable section

private theorem no_fortyFive_j2
    (S : Sylow 2 Sporadic.LeechRelated.J2.Carrier)
    (N : Subgroup Sporadic.LeechRelated.J2.Carrier)
    (hSN : (S : Subgroup _) ≤ N) (hN : N ≠ ⊤) : ¬ 45 ∣ Nat.card N := by
  open Sporadic.LeechRelated.J2 in
  open ExceptionalParabolics SylowOvergroups in
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier S
    (SecondParabolic.sylow FirstParabolic.card_l₁)
  let c := MulAut.conj g
  have hS : (S : Subgroup _).map c.toMonoidHom =
      Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.s :=
    congrArg Sylow.toSubgroup hg
  have hn : N.map c.toMonoidHom ≠ ⊤ := by
    intro he
    apply hN
    apply map_injective (f := c.toMonoidHom) c.injective
    rw [he,map_top_of_surjective _ c.surjective]
  intro hd
  have hc : 45 ∣ Nat.card (N.map c.toMonoidHom) := by
    rwa [card_map_of_injective c.injective]
  open Sporadic.LeechRelated.J2 in
  open ExceptionalParabolics SylowOvergroups in
  rcases proper_overgroup_le (N.map c.toMonoidHom) (hS ▸ map_mono hSN) hn with h | h
  · have hh := hc.trans (card_dvd_of_le h)
    rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_l₁] at hh
    norm_num at hh
  · have hh := hc.trans (card_dvd_of_le h)
    rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.card_p₂] at hh
    norm_num at hh

private theorem no_nine_hs
    (S : Sylow 2 Sporadic.LeechRelated.HS.Carrier)
    (N : Subgroup Sporadic.LeechRelated.HS.Carrier)
    (hSN : (S : Subgroup _) ≤ N) (hN : N ≠ ⊤) : ¬ 9 ∣ Nat.card N := by
  open Sporadic.LeechRelated.HS in
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier S BlockNormalizer.baseSylow
  let c := MulAut.conj g
  have hS : (S : Subgroup _).map c.toMonoidHom =
      Sporadic.LeechRelated.HS.EvenLocalCandidates.subgroup :=
    congrArg Sylow.toSubgroup hg
  have hn : N.map c.toMonoidHom ≠ ⊤ := by
    intro he
    apply hN
    apply map_injective (f := c.toMonoidHom) c.injective
    rw [he,map_top_of_surjective _ c.surjective]
  intro hd
  have hc : 9 ∣ Nat.card (N.map c.toMonoidHom) := by
    rwa [card_map_of_injective c.injective]
  open Sporadic.LeechRelated.HS in
  rcases SylowOvergroups.proper_overgroup_le (N.map c.toMonoidHom)
    (hS ▸ map_mono hSN) hn with h | h
  · exact EvenLocalCandidates.central_localGroup_nine_not_dvd (hc.trans (card_dvd_of_le h))
  · exact EvenLocalCandidates.large_localGroup_nine_not_dvd 2 (by decide)
      (hc.trans (card_dvd_of_le h))

private theorem no_nine_ru (hO : pCore 2 Rudvalis.Model = ⊥)
    (S : Sylow 2 Rudvalis.Model) (N : Subgroup Rudvalis.Model)
    (hSN : (S : Subgroup _) ≤ N) (hN : N ≠ ⊤) : ¬ 9 ∣ Nat.card N := by
  obtain ⟨M,hM,hNM⟩ := (eq_top_or_exists_le_coatom N).resolve_left hN
  have hodd : ¬ 2 ∣ M.index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le (hSN.trans hNM)))
  have hcover := Rudvalis.SylowOvergroups.oddIndexMaximalCover_of_twoCore_of_radicalCover hO
    Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.rudvalis_oddIndexMaximalTwoCore
    Rudvalis.SylowOvergroups.oddIndexMaximalRadicalCover
  intro hd
  have hh := hd.trans (card_dvd_of_le hNM)
  rcases hcover M hM hodd with he | he
  · obtain ⟨e⟩ := he
    exact Rudvalis.SylowOvergroups.not_nine_dvd_max4_card
      ((Nat.card_congr e.toEquiv) ▸ hh)
  · obtain ⟨e⟩ := he
    exact Rudvalis.SylowOvergroups.not_nine_dvd_max6_card
      ((Nat.card_congr e.toEquiv) ▸ hh)

private theorem normalizer_data {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 A) (B X : Subgroup A)
    (htop : (⊤ : Subgroup A).IsCComponent)
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (hXB : X ≤ normalizer (B : Set A)) (hX : 9 ∣ Nat.card X)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    normalizer (B : Set A) ≠ ⊤ ∧ 45 ∣ Nat.card (normalizer (B : Set A)) := by
  let := FiveLocalFF.SolvableQuotients.local_perfect hB
  have hfive := FiveLocalFF.SolvableQuotients.five_dvd_card B eB
  have hne : B ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hfive
    norm_num at hfive
  refine ⟨fun he => htop.not_le_normalizer_of_perfect_lt
    (lt_of_le_of_ne le_top hproper) hne (by rw [he]),?_⟩
  exact (by decide : Nat.Coprime 9 5).mul_dvd_of_dvd_of_dvd
    (hX.trans (card_dvd_of_le hXB)) (hfive.trans (card_dvd_of_le B.le_normalizer))

private theorem transport_obstruction {A M : Type*} [Group A] [Finite A] [Group M]
    (e : A ≃* M) (S : Sylow 2 A) (N : Subgroup A)
    (hSN : (S : Subgroup A) ≤ N) (hN : N ≠ ⊤) (hc : 45 ∣ Nat.card N)
    (h : ∀ (P : Sylow 2 M) (J : Subgroup M),
      (P : Subgroup M) ≤ J → J ≠ ⊤ → ¬ 45 ∣ Nat.card J) : False := by
  apply h (S.mapSurjective (f := e.toMonoidHom) e.surjective) (N.map e.toMonoidHom)
    (map_mono hSN) ?_ ?_
  · intro he
    apply hN
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [he,map_top_of_surjective _ e.surjective]
  · rwa [card_map_of_injective e.injective]

/-- The actual marked proper local and its order-nine normalizing subgroup
exclude J₂, HS and Rudvalis. The Rudvalis two-core hypothesis is intrinsic. -/
theorem marked_local_not_three_sporadics {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 A) (B X : Subgroup A)
    (htop : (⊤ : Subgroup A).IsCComponent) (hO : pCore 2 A = ⊥)
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (hSB : (S : Subgroup A) ≤ normalizer (B : Set A))
    (hXB : X ≤ normalizer (B : Set A)) (hX : 9 ∣ Nat.card X)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    ¬ (Nonempty (A ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (A ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (A ≃* Rudvalis.Model)) := by
  obtain ⟨hn,hc⟩ := normalizer_data S B X htop hB hproper hXB hX eB
  intro hm
  rcases hm with he | he | he
  · obtain ⟨e⟩ := he
    exact transport_obstruction e S _ hSB hn hc no_fortyFive_j2
  · obtain ⟨e⟩ := he
    exact transport_obstruction e S _ hSB hn hc (fun P J hp hj hd =>
      no_nine_hs P J hp hj ((by decide : 9 ∣ 45).trans hd))
  · obtain ⟨e⟩ := he
    have hz : pCore 2 Rudvalis.Model = ⊥ := by
      rw [←pCore_map_iso 2 e,hO,Subgroup.map_bot]
    exact transport_obstruction e S _ hSB hn hc (fun P J hp hj hd =>
      no_nine_ru hz P J hp hj ((by decide : 9 ∣ 45).trans hd))

private theorem nine_dvd_image {A H : Type*} [Group A] [Finite A] [Group H]
    (q : A →* H) (hk : IsPGroup 2 q.ker) (X : Subgroup A) (hX : Nat.card X = 9) :
    9 ∣ Nat.card (X.map q) := by
  let f := q.subgroupMap X
  have hker : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  obtain ⟨n,hn⟩ := hker.exists_card_eq
  have hcop : Nat.Coprime 9 (Nat.card f.ker) := by
    rw [hn]
    exact (by decide : Nat.Coprime 9 2).pow_right n
  have he := f.ker.card_mul_index
  rw [index_eq_card,Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective X)).toEquiv,hX] at he
  exact hcop.dvd_of_dvd_mul_left (he.symm ▸ dvd_refl 9)

/-- The original local subgroup and Cartan survive the literal two-core
quotient and exclude the three sporadic carriers there. -/
theorem local_quotient_not_three_sporadics
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {B I X : Subgroup G}
    (hB : B ∈ localCComponents T) (hI : I ∈ localCComponents T) (hBI : B < I)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hXI : X ≤ I) (hXB : X ≤ normalizer (B : Set G)) (hX : Nat.card X = 9)
    (hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4) :
    ¬ (Nonempty ((I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty ((I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty ((I ⧸ pCore 2 I) ≃* Rudvalis.Model)) := by
  obtain ⟨S,hS,hBS⟩ := BinaryIntrinsic.local_in_local_overgroup T hB hI hBI.le
  have htop : (⊤ : Subgroup I).IsCComponent := by
    simpa only [subgroupOf_self] using
      hI.subgroupOf_of_le (show I ≤ I from le_rfl) (show I ≤ I ⊔ T from le_sup_left)
  let q := QuotientGroup.mk' (pCore 2 I)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  let : Group.IsNilpotent q.ker := hk.isNilpotent
  let : Group.IsSolvable q.ker := inferInstance
  have hb := Chapter1.Section02.localCComponents_map_of_solvable_ker hBS q
  have hbp : (B.subgroupOf I).map q ≠ ⊤ := by
    intro he
    have he' : (B.subgroupOf I).map q = (⊤ : Subgroup I).map q := by
      rw [he,map_top_of_surjective q hq]
    have ht := local_cComponent_eq_of_map_eq hBS htop le_top q
      (hk.le_sylow_of_normal S) he'
    exact hBI.not_ge (subgroupOf_eq_top.mp ht)
  have htopq : (⊤ : Subgroup (I ⧸ pCore 2 I)).IsCComponent := by
    simpa only [map_top_of_surjective q hq] using
      cComponent_map_of_solvable_ker htop q hq
  have hsB : (S : Subgroup I) ≤ normalizer (B.subgroupOf I : Set I) := by
    rw [hS,←subgroupOf_normalizer_eq hBI.le]
    exact comap_mono hTB
  have hxB : X.subgroupOf I ≤ normalizer (B.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hBI.le]
    exact comap_mono hXB
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmB
  obtain ⟨ef⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let b := subgroupOfEquivOfLe hBI.le
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  obtain ⟨eb⟩ := FiveLocalFF.SolvableQuotients.section_map q (B.subgroupOf I) hBS
    (bq.trans (e.trans ef))
  exact marked_local_not_three_sporadics (S.mapSurjective hq)
    ((B.subgroupOf I).map q) ((X.subgroupOf I).map q) htopq
    (pCore_quotient_pCore_eq_bot 2) hb hbp
    ((map_mono hsB).trans (le_normalizer_map q))
    ((map_mono hxB).trans (le_normalizer_map q))
    (nine_dvd_image q hk (X.subgroupOf I)
      ((Nat.card_congr (subgroupOfEquivOfLe hXI).toEquiv).trans hX)) eb

open scoped MatrixGroups

/-- Neither linear field-five carrier has the third vertex's three-rank. -/
theorem rank_two_not_linear_three_five {A : Type*} [Group A] [Finite A]
    (hr : 2 ≤ primeRank 3 A) :
    ¬ (ClassicalGroup.IsPSL A 3 5 ∨ Chapter1.Section02.LocalModels.IsSL A 3 5) := by
  intro hm
  have hcard : Nat.card A = 372000 := by
    rcases hm with hm | hm
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF]
      norm_num
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      rw [Nat.card_congr e.toEquiv,card_eq_card_quotient_mul_card_subgroup (center SL(3,F)),
        Atlas.ExceptionalSupport.card_sl_center]
      change Nat.card PSL(3,F) * Nat.gcd 3 (Nat.card F - 1) = _
      rw [Matrix.PSL3.LinearThree.card_projective_mul_scalar,hF]
      norm_num
  have hb : primeRank 3 A ≤ 1 := primeRank_le_of_prime_pow_not_dvd (by rw [hcard]; decide)
  omega

private theorem prime_sl_two_rank {A : Type*} [Group A] [Finite A] {p : ℕ}
    (hp : p.Prime) (hm : Source.IsSL A 2 p) : primeRank 3 A ≤ 1 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,hF,ZMod.card])
  rw [primeRank_congr 3 (e.trans (GorensteinWalter.sl2RingEquiv a))]
  let P : Sylow 3 SL(2,ZMod p) := Classical.choice inferInstance
  exact P.primeRank_le_one_of_isCyclic
    (Matrix.SpecialLinearGroup.isCyclic_of_odd_pGroup_injective_primeField
      P.isPGroup' (by decide : 3 ≠ 2) (P : Subgroup SL(2,ZMod p)).subtype Subtype.val_injective)

/-- A prime-square kernel at an exceptional prime loses no cubic rank.
This excludes the actual nonsplit elementary extension as well. -/
theorem rank_two_not_elementary_extension {A : Type*} [Group A] [Finite A]
    (hr : 2 ≤ primeRank 3 A) {p : ℕ} (hp : Source.ExceptionalPrime p) :
    ¬ Chapter1.Section02.LocalModels.HasExtension A
      (Chapter1.Section02.LocalModels.ElementaryModel p 2) (fun Q _ => Source.IsSL Q 2 p) := by
  rintro ⟨N,hN,⟨eN⟩,hm⟩
  let := hN
  have hcard : Nat.card N = p ^ 2 := by
    rw [Nat.card_congr eN.toEquiv]
    change Nat.card (Fin 2 → ZMod p) = p ^ 2
    rw [Nat.card_fun]
    simp only [Nat.card_fin,Nat.card_zmod]
  have hlarge : 11 ≤ p := by obtain ⟨_,hf,h8⟩ := hp; omega
  have hcop : Nat.Coprime 3 (Nat.card N) := by
    rw [hcard]
    exact ((Nat.coprime_primes Nat.prime_three hp.1).mpr (by omega)).pow_right 2
  have hb := (primeRank_le_of_coprime_ker 3 (QuotientGroup.mk' N)
    (by simpa only [QuotientGroup.ker_mk'] using hcop)).trans (prime_sl_two_rank hp.1 hm)
  omega

open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource Representation
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m))

/-- The original common-Q join has only the three desired Lie rows or
the remaining Mathieu, Janko-four and nilpotent-extension rows. The marked
locals and cubic rank exclude every removed row. -/
theorem sp4_triangle_join_sylow_sieve_of_common_normal
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let I := K₀ ⊔ f.Li 1
    let A := I ⧸ pCore 2 I
    Source.IsSL A 3 4 ∨ Source.IsSp A 2 4 ∨ ClassificationModels.IsG2At A 4 ∨
      Nonempty (A ≃* Sporadic.Mathieu.M22) ∨ Chapter1.Section02.LocalModels.IsM22Cover A ∨
      Nonempty (A ≃* Sporadic.Mathieu.M23) ∨ Nonempty (A ≃* Janko4.Model) ∨
      Chapter1.Section02.LocalModels.HasExtension A
        (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
        (fun J _ => Source.IsSL J 2 5) := by
  intro I A
  obtain ⟨_,hIL,_,_,_,hr,hmark⟩ := sp4_triangle_marked_locals_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  obtain ⟨hb,hbx,hnx,hmb,_,_⟩ := hmark K₀ (.inl rfl)
  obtain ⟨hc,_,_,hmc,_,_⟩ := hmark (f.Li 1) (.inr rfl)
  have hunitary := local_join_not_unitary_five T hK₀.1
    (flag_mem_local_of_model D S f 1 hm₂).1 hIL.1 hb.le hc.le hTK₀
    (f.sylow_normalizes_Li 1) rfl hmb hmc
  have hcx : Nat.card X = 9 := by
    rw [(Coordinates.sp4 m).cartan_card hX,hfour]
    norm_num
  have hspor := local_quotient_not_three_sporadics T hK₀.1 hIL.1 hb hTK₀
    ((show X ≤ K₀ ⊔ X from le_sup_right).trans hbx) hnx hcx hmb
  obtain ⟨_,hseven,hm⟩ := sp4_triangle_join_comparison_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  obtain ⟨_,_,_,_,hprime,h25,hj1⟩ := sp4_triangle_join_remaining_models_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  rcases hm with hm | hm | hm | hm
  · exact .inl hm
  · exact .inr (.inl hm)
  · exact .inr (.inr (.inl hm))
  · apply Or.inr; apply Or.inr; apply Or.inr
    cases hm with
    | alternating he => exact (hseven (.inl he)).elim
    | alternatingCover he => exact (hseven (.inr he)).elim
    | primeLinear p hp he => exact (hprime p hp.1 he).elim
    | linearTwentyFive he => exact (h25 he).elim
    | j1 he => exact (hj1 he).elim
    | three u he =>
      cases u with
      | false => exact (rank_two_not_linear_three_five hr.ge he).elim
      | true => exact (hunitary he).elim
    | m22 he => exact .inl he
    | m22Cover he => exact .inr (.inl he)
    | m23 he => exact .inr (.inr (.inl he))
    | j4 he => exact .inr (.inr (.inr (.inl he)))
    | j2 he => exact (hspor (.inl he)).elim
    | hs he => exact (hspor (.inr (.inl he))).elim
    | ru he => exact (hspor (.inr (.inr he))).elim
    | nilpotentExtension he => exact .inr (.inr (.inr (.inr he)))
    | elementaryExtension p hp he => exact (rank_two_not_elementary_extension hr.ge hp he).elim

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
