module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSevenMathieu
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFourPlacement
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension
public import CFSG.Quasithin.MainConverse.SporadicLocal.J4
/-!
# A₇ sections cannot enlarge into J₄

The full-Sylow minimal elementary-pair catalogue puts the original pair
inside max1 or an involution centralizer. In max1 its actual M₂₄ quotient
is excluded. The first involution centralizer has a normal subgroup with
solvable kernel and quotient M₂₂; perfectness places the smaller local
subgroup there, and the Sylow intersection remains full. The second
centralizer lies inside max1. No arbitrary maximal-overgroup classification
or replacement of a central cover by its simple quotient is used.
Source: Aschbacher–Smith A.3.12(17), pp.47–48, and 1.2.8, pp.506–507.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenJankoFour
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings AlternatingSevenSection
open Janko4 Janko4.Cardinality Janko4.LocalStructure Janko4.OuterReduction.OddIndex
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
local notation "M" => max1Subgroup matrixA_mul_self matrixB_pow_four
local notation "K" => localKernel matrixA_mul_self matrixB_pow_four

private theorem normal_le_of_simple_quotient
    {G : Type*} [Group G] {p : ℕ}
    (Q : Subgroup G) [Q.Normal] [IsSimpleGroup (G ⧸ Q)]
    (hQ : IsPGroup p Q) (hp : IsPPerfect p G)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊤) : N ≤ Q := by
  let q := QuotientGroup.mk' Q
  have hnmap : (N.map q).Normal :=
    (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective Q)
  rcases hnmap.eq_bot_or_eq_top with hz | ht
  · simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff N).mp hz
  · exfalso
    apply hN
    apply hp N inferInstance
    let f := (QuotientGroup.mk' N).comp Q.subtype
    apply hQ.of_surjective f
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨n, hn, he⟩ := mem_map.mp (show q x ∈ N.map q by rw [ht]; trivial)
    have hnx : n⁻¹ * x ∈ Q := QuotientGroup.eq.mp he
    refine ⟨⟨n⁻¹ * x, hnx⟩, ?_⟩
    change QuotientGroup.mk' N (n⁻¹ * x) = QuotientGroup.mk' N x
    have hn' : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [map_mul, map_inv, hn', inv_one, one_mul]

/-- Every nontrivial image of the marked two-perfect extension has order divisible by five. -/
private theorem five_dvd_card_range {J H : Type*} [Group J] [Finite J] [Group H]
    (hp : IsPPerfect 2 J) (e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 7))
    (f : J →* H) (hf : f ≠ 1) : 5 ∣ Nat.card f.range := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (J ⧸ pCore 2 J) := e.isSimpleGroup
  have hker : f.ker ≠ ⊤ := by
    intro h
    apply hf
    ext x
    exact MonoidHom.mem_ker.mp (h ▸ mem_top x)
  have hle : f.ker ≤ pCore 2 J :=
    normal_le_of_simple_quotient (pCore 2 J) pCore_isPGroup hp f.ker hker
  let q := QuotientGroup.map f.ker (pCore 2 J) (MonoidHom.id J) hle
  have hq : Function.Surjective q :=
    QuotientGroup.map_surjective_of_surjective f.ker (pCore 2 J) (MonoidHom.id J)
      (QuotientGroup.mk'_surjective (pCore 2 J)) hle
  have hd : Nat.card (J ⧸ pCore 2 J) ∣ Nat.card f.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact card_dvd_of_surjective q hq
  have hc : Nat.card (J ⧸ pCore 2 J) = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [hc] at hd
  exact dvd_trans (by decide : 5 ∣ 2520) hd

/-- A two-group moved by the marked two-perfect extension has at least sixteen elements. -/
private theorem sixteen_le_card_of_nontrivial_action
    {J V : Type*} [Group J] [Finite J] [Group V] [Finite V]
    (hp : IsPPerfect 2 J) (e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 7))
    (ρ : J →* MulAut V) (hρ : ρ ≠ 1) (hV : IsPGroup 2 V) :
    16 ≤ Nat.card V := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ρ.range) 5
    (five_dvd_card_range hp e ρ hρ)
  let B := zpowers a
  have hB : Nat.card B = 5 := (Nat.card_zpowers a).trans ha
  have hnot : FixedPoints.subgroup B V ≠ ⊤ := by
    intro htop
    have he : a = 1 := by
      apply Subtype.ext
      apply MulEquiv.ext
      intro v
      have hv : v ∈ FixedPoints.subgroup B V := htop ▸ mem_top v
      exact hv ⟨a, mem_zpowers a⟩
    simp [he] at ha
  exact Theory.GroupAction.sixteen_le_card_of_five_action_nontrivial hB hV hnot

private theorem small_elementary_action_trivial {B A : Type*} [Group B] [Finite B]
    [Group.IsPerfect B] [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))
    (hA : Nat.card A ≤ 8) (f : B →* MulAut A) : f = 1 := by
  have hp : IsPPerfect 2 B := by
    intro N hN hquot
    let := hN
    have hs : Subsingleton (B ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (B ⧸ N) hquot.isNilpotent
    apply eq_top_iff.mpr
    intro b _
    exact (QuotientGroup.eq_one_iff b).mp (Subsingleton.elim _ _)
  by_contra hf
  have hh := sixteen_le_card_of_nontrivial_action
    hp eB f hf (IsElementaryAbelian.isPGroup 2 A)
  omega

/-- No local C-component normalized by a full Sylow of the native max1
carrier has two-core quotient A₇. No module recognition is required. -/
theorem max1_not_section (S : Sylow 2 M) (B : Subgroup M)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup M) ≤ normalizer (B : Set M))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)) : False := by
  let := Exceptional.local_perfect hl
  let q := (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).toMonoidHom.comp
    (QuotientGroup.mk' K)
  have hq : Function.Surjective q :=
    (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).surjective.comp
      (QuotientGroup.mk'_surjective K)
  have hk : q.ker = K := by
    rw [MonoidHom.ker_comp_of_injective _ _
      (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).injective,
      QuotientGroup.ker_mk']
  let : Group.IsSolvable q.ker := by
    rw [hk]
    let := localKernel_elementary matrixA_mul_self matrixB_pow_four
    let : Group.IsNilpotent K := (IsElementaryAbelian.isPGroup 2 K).isNilpotent
    infer_instance
  exact AlternatingSevenMathieu.not_mathieuTwentyFour (S.mapSurjective hq) (B.map q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl q)
    ((map_mono (f := q) hn).trans (B.le_normalizer_map q))
    (section_map B ⟨eB⟩ q) (MulEquiv.refl _)

/-- The actual pair consisting of the source local subgroup and its full
normalizing Sylow cannot both lie in literal max1. -/
private theorem not_pair_le_max1 (S : Sylow 2 Model) (B : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))
    (hBM : B ≤ M) (hSM : (S : Subgroup Model) ≤ M) : False := by
  let := Exceptional.local_perfect hl
  let d := subgroupOfEquivOfLe hBM
  apply max1_not_section (S.subtype hSM) (B.subgroupOf M)
    (local_restrict hl hBM) _
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans eB)
  intro s hs
  apply mem_normalizer_iff.mpr
  intro b
  exact mem_normalizer_iff.mp (hn hs) (b : Model)

/-- The same exclusion through an actual ambient equivalence, including a
chosen conjugation of max1. -/
private theorem not_pair_map_le_max1 {G : Type*} [Group G] [Finite G]
    (f : G ≃* Model) (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))
    (hBM : B.map f.toMonoidHom ≤ M)
    (hSM : (S : Subgroup G).map f.toMonoidHom ≤ M) : False := by
  let := Exceptional.local_perfect hl
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot f.injective]
    infer_instance
  exact not_pair_le_max1 (S.mapSurjective (f := f.toMonoidHom) f.surjective)
    (B.map f.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom)
    ((map_mono (f := f.toMonoidHom) hn).trans (B.le_normalizer_map f.toMonoidHom))
    (section_map B ⟨eB⟩ f.toMonoidHom).some hBM hSM

private noncomputable def markedSylow : Sylow 2 Model :=
  twoSubgroup_isPGroup.toSylow (by
    rw [twoSubgroup,index_map_subtype,localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)

private theorem fixed_even_centralizer (B E : Subgroup Model)
    (hl : B ∈ localCComponents markedSylow)
    (hnB : twoSubgroup ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))
    (hES : E ≤ twoSubgroup) (hne : E ≠ ⊥) (he : IsElementaryAbelian 2 E)
    (hBE : B ≤ normalizer (E : Set Model))
    (hSE : twoSubgroup ≤ normalizer (E : Set Model)) :
    2 ∣ Nat.card (centralizer (B : Set Model)) := by
  rcases FiveLocalFF.JankoFour.fixed_pair_minimal_alternative (B ⊔ twoSubgroup) E hES hne he le_sup_right
    (sup_le hBE hSE) with hmax | ⟨A,hA,hAE,heA,hcard,hHA⟩
  · exact (not_pair_le_max1 markedSylow B hl hnB eB
      (le_sup_left.trans hmax) (le_sup_right.trans hmax)).elim
  · let := heA
    let := FiveLocalFF.SolvableQuotients.local_perfect hl
    have hBA := le_sup_left.trans hHA
    let f := A.normalizerMonoidHom.comp (inclusion hBA)
    have hf : f = 1 := small_elementary_action_trivial eB hcard f
    have hBC : B ≤ centralizer (A : Set Model) := by
      intro b hb
      have hk : inclusion hBA ⟨b,hb⟩ ∈ A.normalizerMonoidHom.ker := by
        change f ⟨b,hb⟩ = 1
        rw [hf]
        rfl
      rwa [normalizerMonoidHom_ker] at hk
    have hAC : A ≤ centralizer (B : Set Model) := le_centralizer_iff.mp hBC
    have h2 : 2 ∣ Nat.card A := by
      obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
      have hn0 : n ≠ 0 := by
        intro hn0
        rw [hn0,pow_zero] at hn
        exact hA (A.eq_bot_of_card_eq hn)
      rw [hn]
      exact dvd_pow_self 2 hn0
    exact h2.trans (card_dvd_of_injective (inclusion hAC) (inclusion_injective hAC))

/-- A nonzero normal elementary subgroup shared by the original local A7
and its full Sylow forces even centralizer in the actual J4 carrier. -/
private theorem even_centralizer_of_normal_elementary (S : Sylow 2 Model) (B E : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hnB : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))
    (hES : E ≤ (S : Subgroup Model)) (hne : E ≠ ⊥) (he : IsElementaryAbelian 2 E)
    (hBE : B ≤ normalizer (E : Set Model))
    (hSE : (S : Subgroup Model) ≤ normalizer (E : Set Model)) :
    2 ∣ Nat.card (centralizer (B : Set Model)) := by
  let := Exceptional.local_perfect hl
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model S markedSylow
  let f := MulAut.conj g
  have hS : (S : Subgroup Model).map f.toMonoidHom = twoSubgroup :=
    congrArg Sylow.toSubgroup hg
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot f.injective]
    infer_instance
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom
  have hn' := (map_mono (f := f.toMonoidHom) hnB).trans (B.le_normalizer_map f.toMonoidHom)
  have hSE' := (map_mono (f := f.toMonoidHom) hSE).trans (E.le_normalizer_map f.toMonoidHom)
  have hES' := map_mono (f := f.toMonoidHom) hES
  rw [hS] at hl' hn' hSE' hES'
  let := he
  have h := fixed_even_centralizer (B.map f.toMonoidHom) (E.map f.toMonoidHom)
    hl' hn' (section_map B ⟨eB⟩ f.toMonoidHom).some hES'
    (fun hz => hne ((map_eq_bot_iff_of_injective _ f.injective).mp hz))
    (IsElementaryAbelian.map f.toMonoidHom)
    ((map_mono (f := f.toMonoidHom) hBE).trans (E.le_normalizer_map f.toMonoidHom)) hSE'
  have hc : (centralizer (B : Set Model)).map f.toMonoidHom =
      centralizer (B.map f.toMonoidHom : Set Model) := by
    rw [map_centralizer_equiv]
    rfl
  rw [←hc,card_map_of_injective f.injective] at h
  exact h

/-- The same original pair lies in an actual involution centralizer. -/
private theorem involution_centralizer_placement (S : Sylow 2 Model) (B E : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hnB : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))
    (hES : E ≤ (S : Subgroup Model)) (hne : E ≠ ⊥) (he : IsElementaryAbelian 2 E)
    (hBE : B ≤ normalizer (E : Set Model))
    (hSE : (S : Subgroup Model) ≤ normalizer (E : Set Model)) :
    ∃ z : Model, orderOf z = 2 ∧ B ⊔ (S : Subgroup Model) ≤ centralizer ({z} : Set Model) :=
  exists_involution_centralizing_normalizing_two_group B (S : Subgroup Model) S.isPGroup'
    hnB (even_centralizer_of_normal_elementary S B E hl hnB eB hES hne he hBE hSE)

/-- The nontrivial original two-core supplies the normal elementary input,
so no additional seed or irreducibility hypothesis is needed for placement. -/
private theorem involution_centralizer_placement_of_core (S : Sylow 2 Model) (B : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))
    (hc : pCore 2 B ≠ ⊥) :
    ∃ z : Model, orderOf z = 2 ∧ B ⊔ (S : Subgroup Model) ≤ centralizer ({z} : Set Model) := by
  obtain ⟨N,hN,hBN,hSN⟩ := FiveLocalFF.SolvableQuotients.exists_maximal_two_local S B hn hc
  obtain ⟨R,hR,hnR,heR,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le S hN hSN
  let E := R.map (S : Subgroup Model).subtype
  have he : IsElementaryAbelian 2 E := by
    let := heR
    exact IsElementaryAbelian.map _
  have hne : E ≠ ⊥ := fun hz => hR ((map_eq_bot_iff_of_injective _ Subtype.val_injective).mp hz)
  exact involution_centralizer_placement S B E hl hn eB (map_subtype_le R) hne he
    (hNR ▸ hBN) (hNR ▸ hSN)

private theorem second_seed_conjugacy :
    IsConj (InvolutionCentralizers.Second.seed : Model) ((a*b*a*b*b)^5) := by
  obtain ⟨g,hg⟩ := Simplicity.Max1Fusion.seed_fuses_second matrixA_mul_self matrixB_pow_four
  have ha : Simplicity.a matrixA_mul_self = a := by apply toMatrix_injective; rfl
  have hb : Simplicity.b matrixB_pow_four = b := by apply toMatrix_injective; rfl
  rw [ha,hb] at hg
  have hw : Simplicity.word a b "ababb" = a*b*a*b*b := by
    simp [Simplicity.word,mul_assoc]
  rw [hw] at hg
  exact isConj_iff.mpr ⟨g,hg.symm⟩

private theorem centralizer_map_of_conj {x y : Model} (g : Model)
    (hg : g*x*g⁻¹=y) :
    (centralizer ({x} : Set Model)).map (MulAut.conj g).toMonoidHom =
      centralizer ({y} : Set Model) := by
  rw [map_centralizer_equiv,Set.image_singleton]
  exact congrArg (fun z => centralizer ({z} : Set Model)) hg

/-- Every original full-Sylow local A7 section with nontrivial two-core is
carried into the literal first involution centralizer by ambient conjugation.
The second class is excluded through literal containment in max1. -/
private theorem first_centralizer_placement (S : Sylow 2 Model) (B : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))
    (hc : pCore 2 B ≠ ⊥) :
    ∃ g : Model,
      B.map (MulAut.conj g).toMonoidHom ≤ InvolutionCentralizers.First.centralizer ∧
      (S : Subgroup Model).map (MulAut.conj g).toMonoidHom ≤
        InvolutionCentralizers.First.centralizer := by
  obtain ⟨z,hz,hpair⟩ := involution_centralizer_placement_of_core S B hl hn eB hc
  rcases OuterReduction.involution_isConj_of_max1_odd_index
    OuterReduction.max1_odd_index_unconditional hz with h | h
  · obtain ⟨g,hg⟩ := isConj_iff.mp h.symm
    have hmap := map_mono (f := (MulAut.conj g).toMonoidHom) hpair
    rw [centralizer_map_of_conj g hg,Subgroup.map_sup] at hmap
    exact ⟨g,le_sup_left.trans hmap,le_sup_right.trans hmap⟩
  · obtain ⟨g,hg⟩ := isConj_iff.mp (second_seed_conjugacy.trans h).symm
    have hmap := map_mono (f := (MulAut.conj g).toMonoidHom) hpair
    rw [centralizer_map_of_conj g hg,Subgroup.map_sup] at hmap
    have hBM := (le_sup_left.trans hmap).trans InvolutionCentralizers.Second.ambient_le_max1
    have hSM := (le_sup_right.trans hmap).trans InvolutionCentralizers.Second.ambient_le_max1
    exact (not_pair_map_le_max1 (MulAut.conj g) S B hl hn eB hBM hSM).elim

open InvolutionCentralizers.First.QuotientExtension in
private theorem first_kernel_solvable : Group.IsSolvable mathieuProjection.ker := by
  let : Group.IsSolvable R := by
    apply (Group.isSolvable_iff_subgroup_quotient (Q.subgroupOf R)).mpr
    have hp : IsPGroup 2 (Q.subgroupOf R) := pCore_isPGroup.comap_subtype
    let : Group.IsNilpotent (Q.subgroupOf R) := hp.isNilpotent
    exact ⟨inferInstance, Group.isSolvable_of_isSolvable_injective (f := RQuotientEquivC3.toMonoidHom) RQuotientEquivC3.injective⟩
  rw [mathieuProjection_ker]
  exact Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe R_le_H).toMonoidHom)
    (subgroupOfEquivOfLe R_le_H).injective

open InvolutionCentralizers.First.QuotientExtension in
/-- Perfectness retains the actual full covering subgroup in the first
centralizer; its literal M₂₂ projection excludes the original A₇ pair. -/
theorem first_centralizer_not_section
    (S : Sylow 2 InvolutionCentralizers.First.centralizer)
    (B : Subgroup InvolutionCentralizers.First.centralizer)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup InvolutionCentralizers.First.centralizer) ≤ normalizer (B : Set InvolutionCentralizers.First.centralizer))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)) : False := by
  let := Exceptional.local_perfect hl
  let : Group.IsSolvable (InvolutionCentralizers.First.centralizer ⧸ Janko4.InvolutionCentralizers.First.QuotientExtension.H) :=
    Group.isSolvable_of_isSolvable_injective (f := centralizerQuotientEquivC2.toMonoidHom) centralizerQuotientEquivC2.injective
  have hBH : B ≤ Janko4.InvolutionCentralizers.First.QuotientExtension.H := (le_solvableResidual_of_isPerfect B).trans
    (solvableResidual_le_of_solvable_quotient Janko4.InvolutionCentralizers.First.QuotientExtension.H)
  obtain ⟨T,hT⟩ := S.exists_subgroupOf_eq_of_normal Janko4.InvolutionCentralizers.First.QuotientExtension.H
  let D := B.subgroupOf Janko4.InvolutionCentralizers.First.QuotientExtension.H
  have hlD : D ∈ localCComponents T := by
    rw [hT]
    exact local_restrict hl hBH
  have hnD : (T : Subgroup Janko4.InvolutionCentralizers.First.QuotientExtension.H) ≤ normalizer (D : Set Janko4.InvolutionCentralizers.First.QuotientExtension.H) := by
    rw [hT]
    intro s hs
    apply mem_normalizer_iff.mpr
    intro b
    exact mem_normalizer_iff.mp (hn hs) (b : InvolutionCentralizers.First.centralizer)
  let d := subgroupOfEquivOfLe hBH
  have hD : Nonempty ((D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 7)) :=
    ⟨(QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans eB⟩
  let := first_kernel_solvable
  obtain ⟨hl',hn',h'⟩ := local_section_map hlD hnD hD mathieuProjection
  exact AlternatingSevenMathieu.not_mathieuTwentyTwo
    (T.mapSurjective mathieuProjection_surjective) (D.map mathieuProjection)
    hl' hn' h' (MulEquiv.refl _)

private theorem native_not_section (S : Sylow 2 Model) (B : Subgroup Model)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) : False := by
  by_cases hc : pCore 2 B = ⊥
  · have hs := sylow_card_dvd_of_core_eq_bot S B hl hn h hc
      (MainConverse.SporadicLocal.j4_evenCharacteristic S)
    have hd : 32 ∣ Nat.card Model := by
      rw [Janko4.Cardinality.Thompson.model_card]
      decide
    have hh := (S.pow_dvd_card_of_pow_dvd_card (n := 5) hd).trans hs
    norm_num at hh
  · obtain ⟨g,hBC,hSC⟩ := first_centralizer_placement S B hl hn h.some hc
    let f := MulAut.conj g
    let : Group.IsSolvable f.toMonoidHom.ker := by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr f.injective]
      infer_instance
    obtain ⟨hl',hn',h'⟩ := local_section_map hl hn h f.toMonoidHom
    let T := S.mapSurjective (f := f.toMonoidHom) f.surjective
    let C := InvolutionCentralizers.First.centralizer
    let d := subgroupOfEquivOfLe hBC
    apply first_centralizer_not_section (T.subtype hSC) ((B.map f.toMonoidHom).subgroupOf C)
      (local_restrict hl' hBC) _
      ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans h'.some)
    intro s hs
    apply mem_normalizer_iff.mpr
    intro b
    exact mem_normalizer_iff.mp (hn' hs) (b : Model)

/-- The original full-Sylow-normalized A₇ section excludes J₄, using only
its actual two-local pair placement and full quotient maps. -/
theorem not_jankoFour {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (B : Subgroup G) (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (e : G ≃* Model) : False := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
    infer_instance
  obtain ⟨hl',hn',h'⟩ := local_section_map hl hn h e.toMonoidHom
  exact native_not_section (S.mapSurjective e.surjective) (B.map e.toMonoidHom) hl' hn' h'

/-- Apply the exclusion to the literal maximal-local-overcomponent quotient. -/
theorem local_overcomponent_not_jankoFour {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) {X L : Subgroup G}
    (hX : X ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hL : L ∈ Chapter1.L G (T : Subgroup G)) (hXL : X ≤ L)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7))) :
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Model) := by
  rintro ⟨e⟩
  exact not_model_of_local_overcomponent not_jankoFour T hX hn hL hXL h e

end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenJankoFour
