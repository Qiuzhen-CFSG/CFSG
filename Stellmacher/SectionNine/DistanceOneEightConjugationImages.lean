module

public import Stellmacher.SectionNine.DistanceOneReduction
public import Stellmacher.SectionNine.CubicLocalAction
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Theory.GroupTheory.IndexTwoIntersection
public import Theory.GroupTheory.TwoLocalConjugationImages

/-!
# The common Sylow subgroup for the elementary-eight normalizers

At a length-one critical edge, the local conclusion of (9.1) gives a terminal
SL₂(2) quotient and an edge Sylow of order 128. The cubic local action shows
that the whole edge stabilizer is this Sylow. Consequently the terminal
stabilizer has order 384. Each supplied S₄ normalizer quotient has kernel of
order eight, so both local normalizers have order 192. Intersecting the
index-two terminal normalizer with the edge Sylow gives the same order-64
Sylow subgroup in both local normalizers.

If the centralizer in the original ambient group is a two-group, injectivity
of the graph-group embedding makes each local conjugation kernel a normal
two-subgroup. Both kernels therefore lie in the common Sylow and hence in
the terminal stabilizer. Its supplied self-centralizer equality identifies
both kernels with U. Mapping the common Sylow gives an actual order-64
two-subgroup of the ambient normalizer inside the terminal stabilizer image.

The principal theorem maps both local normalizers into the ambient group,
transports their S₄ quotient models and kernels, and invokes the independent
Sylow-bound image-separation theorem. The two normalizers intersect in order
64; equal conjugation images would put their product in an overgroup of order
at most 384, contrary to its order 576. The resulting distinct S₄ subgroups
belong to the actual normalizer conjugation range. No ambient
self-centralization is assumed or concluded.

Source: Stellmacher (9.1)(c), Journal of Algebra 190
(1997), p.48 / PDF p.38, final paragraph of the proof, in
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Stellmacher.Later Stellmacher.SectionsFiveToSeven
open Stellmacher.SectionsFiveToSeven.SevenSix

private theorem quotient_model_card
    {G M : Type*} [Group G] [Finite G] [Group M] [Finite M]
    (K U : Subgroup G) (hUK : U ≤ K) (hmodel : QuotientIsModel K U M) :
    Nat.card K = Nat.card M * Nat.card U := by
  obtain ⟨projection, hsurj, hker⟩ := hmodel
  have hcard := projection.ker.index_mul_card
  rw [Subgroup.index_ker, projection.range_eq_top_of_surjective hsurj,
    Subgroup.card_top, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv] at hcard
  exact hcard.symm

private theorem map_quotient_model
    {H G M : Type*} [Group H] [Finite H] [Group G] [Finite G] [Group M]
    (e : G →* H) (he : Function.Injective e) (K U : Subgroup G)
    (hUK : U ≤ K) (hmodel : QuotientIsModel K U M) :
    QuotientIsModel (K.map e) (U.map e) M := by
  have _ := hUK
  obtain ⟨f, hf, hker⟩ := hmodel
  let eqv := K.equivMapOfInjective e he
  let g : K.map e →* M := f.comp eqv.symm.toMonoidHom
  refine ⟨g, hf.comp eqv.symm.surjective, ?_⟩
  apply Subgroup.ext
  intro x
  change eqv.symm x ∈ f.ker ↔ _
  rw [hker]
  change ((eqv.symm x : K) : G) ∈ U ↔ (x : H) ∈ U.map e
  have hx : e ((eqv.symm x : K) : G) = (x : H) :=
    congrArg Subtype.val (eqv.apply_symm_apply x)
  constructor
  · intro h
    exact ⟨_, h, hx⟩
  · rintro ⟨y, hy, heq⟩
    rwa [he (hx.trans heq.symm)]

private theorem sylow_of_card_64
    {G : Type*} [Group G] [Finite G] (R K : Subgroup G)
    (hle : R ≤ K) (hR : Nat.card R = 64) (hK : Nat.card K = 192) :
    IsSylowTwoIn R K := by
  have hcard : Nat.card (R.subgroupOf K) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hR]
  have hp : IsPGroup 2 (R.subgroupOf K) := IsPGroup.of_card (n := 6) hcard
  have hindex : (R.subgroupOf K).index = 3 := by
    have heq := (R.subgroupOf K).card_mul_index
    rw [hcard, hK] at heq
    omega
  refine ⟨hle, hp.toSylow (by rw [hindex]; decide), ?_⟩
  exact Subgroup.map_subgroupOf_eq_of_le hle

public theorem distance_one_local_normalizer_sylow_data
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlen : ctx.criticalPath.length = 1)
    (hlocal : DistanceOneLocalConclusion ctx)
    (U : Subgroup G)
    (hUcard : Nat.card U = 8)
    (hUa : U ≤ GAt ctx.Γ ctx.criticalPath.a)
    (hUd : U ≤ GAt ctx.Γ ctx.criticalPath.a')
    (hmodela : QuotientIsModel
      (GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.normalizer (U : Set G)) U
      (Equiv.Perm (Fin 4)))
    (hmodeld : QuotientIsModel
      (GAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.normalizer (U : Set G)) U
      (Equiv.Perm (Fin 4))) :
    let initial := GAt ctx.Γ ctx.criticalPath.a
    let terminal := GAt ctx.Γ ctx.criticalPath.a'
    let normalizer := Subgroup.normalizer (U : Set G)
    let R := T ⊓ normalizer
    Nat.card terminal = 384 ∧ initial ⊓ terminal = T ∧
      Nat.card ↥(initial ⊓ normalizer) = 192 ∧
      Nat.card ↥(terminal ⊓ normalizer) = 192 ∧ Nat.card R = 64 ∧
      IsSylowTwoIn R (initial ⊓ normalizer) ∧
      IsSylowTwoIn R (terminal ⊓ normalizer) := by
  classical
  let initial := GAt ctx.Γ ctx.criticalPath.a
  let terminal := GAt ctx.Γ ctx.criticalPath.a'
  let normalizer := Subgroup.normalizer (U : Set G)
  let R := T ⊓ normalizer
  change Nat.card terminal = 384 ∧ initial ⊓ terminal = T ∧
    Nat.card ↥(initial ⊓ normalizer) = 192 ∧
    Nat.card ↥(terminal ⊓ normalizer) = 192 ∧ Nat.card R = 64 ∧
    IsSylowTwoIn R (initial ⊓ normalizer) ∧
    IsSylowTwoIn R (terminal ⊓ normalizer)
  have hfirst : ctx.criticalPath.firstStep = ctx.criticalPath.a' := by
    calc
      ctx.criticalPath.firstStep = ctx.criticalPath.path ⟨1, by omega⟩ :=
        ctx.criticalPath.path_first.symm
      _ = ctx.criticalPath.path ⟨ctx.criticalPath.length,
          Nat.lt_succ_self _⟩ := by congr 1; apply Fin.ext; simp [hlen]
      _ = ctx.criticalPath.a' := ctx.criticalPath.path_end
  have hadj := ctx.criticalPath.firstStep_adj
  rw [hfirst] at hadj
  have hsylow := edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath
  rw [hfirst] at hsylow
  have hTedge : T ≤ initial ⊓ terminal := le_inf hsylow.1.1 hsylow.2.1
  have hedge := (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven
    ctx.criticalPath.a' hlocal.2.1).edge_card ctx.criticalPath.a
      (ctx.Γ.adjacent_symm hadj)
  have hcorep : IsPGroup 2 (QAt ctx.Γ ctx.criticalPath.a') := by
    change IsPGroup 2 (ctx.Γ.twoCoreAt ctx.criticalPath.a')
    rw [ctx.Γ.twoCoreAt_def]
    exact pCore_isPGroup.map _
  obtain ⟨exponent, hexponent⟩ := hcorep.exists_card_eq
  have hedgep : IsPGroup 2 ↥(initial ⊓ terminal) := by
    apply IsPGroup.of_card (n := exponent + 1)
    rw [inf_comm]
    change Nat.card ↥(terminal ⊓ initial) = _ at hedge ⊢
    rw [hedge, hexponent, pow_succ, mul_comm]
  have hedgeT : initial ⊓ terminal = T := by
    obtain ⟨_, sylow, hmap⟩ := hsylow.2
    have hsle : (sylow : Subgroup terminal) ≤
        (initial ⊓ terminal).subgroupOf terminal := by
      intro actor hactor
      apply hTedge
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hactor
    have heqp := sylow.is_maximal'
      (hedgep.of_equiv (Subgroup.subgroupOfEquivOfLe
        (show initial ⊓ terminal ≤ terminal from inf_le_right)).symm) hsle
    calc
      initial ⊓ terminal = ((initial ⊓ terminal).subgroupOf terminal).map
          terminal.subtype := (Subgroup.map_subgroupOf_eq_of_le inf_le_right).symm
      _ = T := by rw [heqp, hmap]
  have hTcard : Nat.card T = 128 := hlocal.2.2.1
  have hcorecard : Nat.card (QAt ctx.Γ ctx.criticalPath.a') = 64 := by
    change Nat.card ↥(terminal ⊓ initial) = 2 * _ at hedge
    rw [inf_comm, hedgeT, hTcard] at hedge
    omega
  have hcorele : QAt ctx.Γ ctx.criticalPath.a' ≤ terminal := by
    change ctx.Γ.twoCoreAt ctx.criticalPath.a' ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hterminal : Nat.card terminal = 384 := by
    rw [quotient_model_card terminal _ hcorele hlocal.2.1, hcorecard,
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card
        (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)]
  have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hNa : Nat.card ↥(initial ⊓ normalizer) = 192 := by
    rw [quotient_model_card _ U (le_inf hUa U.le_normalizer) hmodela,
      hperm, hUcard]
  have hNd : Nat.card ↥(terminal ⊓ normalizer) = 192 := by
    rw [quotient_model_card _ U (le_inf hUd U.le_normalizer) hmodeld,
      hperm, hUcard]
  let localNormalizer := (terminal ⊓ normalizer).subgroupOf terminal
  let localSylow := T.subgroupOf terminal
  have hlocalNormalizerCard : Nat.card localNormalizer = 192 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show terminal ⊓ normalizer ≤ terminal from inf_le_left)).toEquiv, hNd]
  have hlocalSylowCard : Nat.card localSylow = 128 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsylow.2.1).toEquiv, hTcard]
  have hindex : localNormalizer.index = 2 := by
    have heq := localNormalizer.card_mul_index
    rw [hlocalNormalizerCard, hterminal] at heq
    omega
  have hcross : ¬ localSylow ≤ localNormalizer := by
    intro hle
    have hdiv := Subgroup.card_dvd_of_le hle
    rw [hlocalSylowCard, hlocalNormalizerCard] at hdiv
    norm_num at hdiv
  have hrestricted := localNormalizer.subgroupOf_index_eq_two localSylow hindex hcross
  let hequiv : (localNormalizer.subgroupOf localSylow) ≃* R := {
    toFun actor := ⟨actor.val.val.val, actor.val.property, actor.property.2⟩
    invFun actor := ⟨⟨⟨actor.val, hsylow.2.1 actor.property.1⟩,
      actor.property.1⟩, hsylow.2.1 actor.property.1, actor.property.2⟩
    left_inv actor := by rfl
    right_inv actor := by rfl
    map_mul' first second := by rfl }
  have hRcard : Nat.card R = 64 := by
    have heq := (localNormalizer.subgroupOf localSylow).card_mul_index
    rw [hrestricted, hlocalSylowCard, Nat.card_congr hequiv.toEquiv] at heq
    omega
  exact ⟨hterminal, hedgeT, hNa, hNd, hRcard,
    sylow_of_card_64 R _ (inf_le_inf hsylow.1.1 le_rfl) hRcard hNa,
    sylow_of_card_64 R _ (inf_le_inf hsylow.2.1 le_rfl) hRcard hNd⟩

private theorem centralizer_le_common_sylow
    {G : Type*} [Group G] [Finite G] (U K R : Subgroup G)
    (hKN : K ≤ Subgroup.normalizer (U : Set G))
    (hC : IsPGroup 2 (Subgroup.centralizer (U : Set G)))
    (hR : IsSylowTwoIn R K) :
    K ⊓ Subgroup.centralizer (U : Set G) ≤ R := by
  let action := U.normalizerMonoidHom.comp (Subgroup.inclusion hKN)
  have hker : action.ker = (Subgroup.centralizer (U : Set G)).subgroupOf K := by
    rw [← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker]
    rfl
  have hkp : IsPGroup 2 action.ker := by
    rw [hker]
    exact hC.comap_of_injective K.subtype K.subtype_injective
  obtain ⟨_, sylow, hmap⟩ := hR
  have hle := hkp.le_sylow_of_normal sylow
  rintro actor ⟨hactor, hcentral⟩
  rw [← hmap]
  refine ⟨⟨actor, hactor⟩, hle ?_, rfl⟩
  rw [hker]
  exact hcentral

public theorem distance_one_eight_common_sylow_and_kernels
    {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
    (embedding : G →* H) (hinj : Function.Injective embedding)
    {T A B : Subgroup G} (ctx : SectionNineLocalContext G T A B)
    (hlen : ctx.criticalPath.length = 1)
    (hlocal : DistanceOneLocalConclusion ctx) (U : Subgroup G)
    (hUcard : Nat.card U = 8)
    (hUa : U ≤ GAt ctx.Γ ctx.criticalPath.a)
    (hUd : U ≤ GAt ctx.Γ ctx.criticalPath.a')
    (hmodela : QuotientIsModel
      (GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.normalizer (U : Set G)) U
      (Equiv.Perm (Fin 4)))
    (hmodeld : QuotientIsModel
      (GAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.normalizer (U : Set G)) U
      (Equiv.Perm (Fin 4)))
    (hself : GAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.centralizer (U : Set G) = U)
    (hC : IsPGroup 2 (Subgroup.centralizer (U.map embedding : Set H))) :
    let initial := GAt ctx.Γ ctx.criticalPath.a
    let terminal := GAt ctx.Γ ctx.criticalPath.a'
    let normalizer := Subgroup.normalizer (U : Set G)
    let centralizer := Subgroup.centralizer (U : Set G)
    (initial ⊓ normalizer) ⊓ centralizer = U ∧
      (terminal ⊓ normalizer) ⊓ centralizer = U ∧
      ∃ R : Subgroup H, R ≤ Subgroup.normalizer (U.map embedding : Set H) ∧
        R ≤ terminal.map embedding ∧ IsPGroup 2 R ∧ Nat.card R = 64 := by
  let initial := GAt ctx.Γ ctx.criticalPath.a
  let terminal := GAt ctx.Γ ctx.criticalPath.a'
  let normalizer := Subgroup.normalizer (U : Set G)
  let centralizer := Subgroup.centralizer (U : Set G)
  let R := T ⊓ normalizer
  obtain ⟨_, _, _, _, hRcard, hRa, hRd⟩ :=
    distance_one_local_normalizer_sylow_data ctx hlen hlocal U hUcard
      hUa hUd hmodela hmodeld
  have hcentralmap : centralizer.map embedding ≤
      Subgroup.centralizer (U.map embedding : Set H) := by
    simpa only [Subgroup.coe_map] using
      Subgroup.map_centralizer_le_centralizer_image (U : Set G) embedding
  have hCG : IsPGroup 2 centralizer :=
    (hC.to_le hcentralmap).of_equiv (centralizer.equivMapOfInjective embedding hinj).symm
  have hUC : U ≤ centralizer := hself.ge.trans inf_le_right
  have hRterminal : R ≤ terminal := hRd.1.trans inf_le_left
  have hKa : (initial ⊓ normalizer) ⊓ centralizer = U := by
    apply le_antisymm
    · have hle := centralizer_le_common_sylow U (initial ⊓ normalizer) R
        inf_le_right hCG hRa
      intro actor hactor
      exact hself.le ⟨hRterminal (hle hactor), hactor.2⟩
    · exact le_inf (le_inf hUa U.le_normalizer) hUC
  have hKd : (terminal ⊓ normalizer) ⊓ centralizer = U := by
    apply le_antisymm
    · exact (inf_le_inf inf_le_left le_rfl).trans hself.le
    · exact le_inf (le_inf hUd U.le_normalizer) hUC
  refine ⟨hKa, hKd, R.map embedding, ?_, Subgroup.map_mono hRterminal,
    (IsPGroup.of_card (n := 6) hRcard).map embedding, ?_⟩
  · exact (Subgroup.map_mono (show R ≤ normalizer from inf_le_right)).trans
      (U.le_normalizer_map embedding)
  · rw [Subgroup.card_map_of_injective hinj]
    exact hRcard

end Stellmacher.SectionNine

namespace Stellmacher.SectionNine

open Stellmacher.Later Stellmacher.SectionsFiveToSeven

universe u

public theorem distance_one_eight_conjugation_images
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlen : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext)
    (hS : S = (S0 : Subgroup H))
    (U : Subgroup G) (hU : U ≤ conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a'))
    (hElem : IsElementaryAbelian 2 U) (hUcard : Nat.card U = 8)
    (hZ : ZAt ctx.Γ ctx.criticalPath.a' ≤ U)
    (hNorm : NormalIn U (EAt ctx.Γ ctx.criticalPath.a'))
    (hUa : U ≤ GAt ctx.Γ ctx.criticalPath.a)
    (hUd : U ≤ GAt ctx.Γ ctx.criticalPath.a')
    (hmodela : QuotientIsModel
      (GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.normalizer (U : Set G)) U
      (Equiv.Perm (Fin 4)))
    (hmodeld : QuotientIsModel
      (GAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.normalizer (U : Set G)) U
      (Equiv.Perm (Fin 4)))
    (hself : GAt ctx.Γ ctx.criticalPath.a' ⊓
      Subgroup.centralizer (U : Set G) = U)
    (hC : IsPGroup 2 (Subgroup.centralizer (U.map embedding : Set H))) :
    ∃ R : Subgroup H, R ≤ Subgroup.normalizer (U.map embedding : Set H) ∧
      R ≤ (GAt ctx.Γ ctx.criticalPath.a').map embedding ∧
      IsPGroup 2 R ∧ Nat.card R = 64 ∧
      ∃ X Y : Subgroup (U.map embedding).normalizerMonoidHom.range,
        X ≠ Y ∧ Nonempty (X ≃* Equiv.Perm (Fin 4)) ∧
          Nonempty (Y ≃* Equiv.Perm (Fin 4)) := by
  -- These inputs remain in the original context-facing interface.
  have _ := hfaithful
  have _ := hU
  have _ := hElem
  have _ := hZ
  have _ := hNorm
  let initial := GAt ctx.Γ ctx.criticalPath.a
  let terminal := GAt ctx.Γ ctx.criticalPath.a'
  let normalizer := Subgroup.normalizer (U : Set G)
  have hdata := distance_one_eight_common_sylow_and_kernels embedding
    ctx.embedding_injective ctx.toLocalContext hlen hlocal U hUcard hUa hUd
      hmodela hmodeld hself hC
  obtain ⟨hKa, hKd, R, hRN, hRD, hRp, hRcard⟩ := hdata
  let K := (initial ⊓ normalizer).map embedding
  let L := (terminal ⊓ normalizer).map embedding
  have hKcard : Nat.card K = 192 := by
    rw [Subgroup.card_map_of_injective ctx.embedding_injective]
    exact (distance_one_local_normalizer_sylow_data ctx.toLocalContext hlen hlocal
      U hUcard hUa hUd hmodela hmodeld).2.2.1
  have hLcard : Nat.card L = 192 := by
    rw [Subgroup.card_map_of_injective ctx.embedding_injective]
    exact (distance_one_local_normalizer_sylow_data ctx.toLocalContext hlen hlocal
      U hUcard hUa hUd hmodela hmodeld).2.2.2.1
  have hKle : K ≤ Subgroup.normalizer (U.map embedding : Set H) :=
    (Subgroup.map_mono (show initial ⊓ normalizer ≤ normalizer from inf_le_right)).trans
      (U.le_normalizer_map embedding)
  have hLle : L ≤ Subgroup.normalizer (U.map embedding : Set H) :=
    (Subgroup.map_mono (show terminal ⊓ normalizer ≤ normalizer from inf_le_right)).trans
      (U.le_normalizer_map embedding)
  have hcentralmap : (Subgroup.centralizer (U : Set G)).map embedding ≤
      Subgroup.centralizer (U.map embedding : Set H) := by
    simpa only [Subgroup.coe_map] using
      Subgroup.map_centralizer_le_centralizer_image (U : Set G) embedding
  have hUC : U ≤ Subgroup.centralizer (U : Set G) := hself.ge.trans inf_le_right
  have hKC : K ⊓ Subgroup.centralizer (U.map embedding : Set H) = U.map embedding := by
    apply le_antisymm
    · rintro x ⟨⟨y, hy, rfl⟩, hx⟩
      apply Subgroup.mem_map_of_mem embedding
      apply hKa.le
      refine ⟨hy, ?_⟩
      change y ∈ Subgroup.centralizer (U : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      apply ctx.embedding_injective
      simpa using Subgroup.mem_centralizer_iff.mp hx
        (embedding z) (Subgroup.mem_map_of_mem embedding hz)
    · exact le_inf (Subgroup.map_mono (le_inf hUa U.le_normalizer))
        ((Subgroup.map_mono hUC).trans hcentralmap)
  have hLC : L ⊓ Subgroup.centralizer (U.map embedding : Set H) = U.map embedding := by
    apply le_antisymm
    · rintro x ⟨⟨y, hy, rfl⟩, hx⟩
      apply Subgroup.mem_map_of_mem embedding
      apply hKd.le
      refine ⟨hy, ?_⟩
      change y ∈ Subgroup.centralizer (U : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      apply ctx.embedding_injective
      simpa using Subgroup.mem_centralizer_iff.mp hx
        (embedding z) (Subgroup.mem_map_of_mem embedding hz)
    · exact le_inf (Subgroup.map_mono (le_inf hUd U.le_normalizer))
        ((Subgroup.map_mono hUC).trans hcentralmap)
  have hKL : Nat.card ↥(K ⊓ L) = 64 := by
    rw [← Subgroup.map_inf _ _ embedding ctx.embedding_injective]
    rw [Subgroup.card_map_of_injective ctx.embedding_injective]
    have horders := distance_one_local_normalizer_sylow_data ctx.toLocalContext hlen hlocal
      U hUcard hUa hUd hmodela hmodeld
    have hinter : (initial ⊓ normalizer) ⊓ (terminal ⊓ normalizer) =
        T ⊓ normalizer := by
      rw [inf_inf_inf_comm, inf_idem]
      exact congrArg (· ⊓ normalizer) horders.2.1
    rw [hinter]
    exact horders.2.2.2.2.1
  have hmodK := map_quotient_model embedding ctx.embedding_injective
    (initial ⊓ normalizer) U (le_inf hUa U.le_normalizer) hmodela
  have hmodL := map_quotient_model embedding ctx.embedding_injective
    (terminal ⊓ normalizer) U (le_inf hUd U.le_normalizer) hmodeld
  have hS0card : Nat.card S0 = 128 := by
    have hScard : Nat.card S = Nat.card T := by
      rw [← ctx.map_S, Subgroup.card_map_of_injective ctx.embedding_injective]
    rw [hS] at hScard
    exact hScard.trans hlocal.2.2.1
  have hmapcard : Nat.card (U.map embedding) = 8 := by
    rw [Subgroup.card_map_of_injective ctx.embedding_injective, hUcard]
  obtain ⟨X, Y, hXY, hX, hY⟩ :=
    two_symmetric_four_conjugation_images_of_sylow_bound S0 hS0card
      (U.map embedding) K L hmapcard hKcard hLcard hKL
      (Subgroup.map_mono (le_inf hUa U.le_normalizer))
      (Subgroup.map_mono (le_inf hUd U.le_normalizer)) hKle hLle hC hKC hLC
      hmodK hmodL
  exact ⟨R, hRN, hRD, hRp, hRcard, X, Y, hXY, hX, hY⟩

end Stellmacher.SectionNine
