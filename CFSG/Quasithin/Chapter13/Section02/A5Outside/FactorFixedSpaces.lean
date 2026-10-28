module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.FactorStabilizers
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.FixedLines
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.KleinFourLines
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# The original two factor fixed lines

Each natural factor of the outside group has a line fixed by the Baumann
image. The Sylow group exchanges the factors, so neither line contains a
nonidentity vector fixed by the whole Sylow group. The alpha identity
therefore places both lines in the original plane V₂, disjoint from V₁.
Their orders and disjointness show that they generate V₂; the product of
their nonidentity elements generates its third line V₁.

The quotient-action displacements are identified with the literal
commutator subgroups in H. Thus the lines are precisely C_[U_H,Hᵢ](Baum(T)),
with the actual quotient preimages Hᵢ. Their point centralizers and the
factor normalizers in T are Baum(T). The last theorem applies this to
H∨O²(N_L(T∩L)) with trivial two-core. The preceding Baumann-normalizer,
solvability and Borel centralization hypotheses remain explicit.

Source: Aschbacher–Smith 13.2.8(6),13.2.11(3)–(4) and the opening of
13.2.12, printed pp.880–882 (1 March 2004 manuscript).
-/

public section

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

private theorem moved_fixed_subgroup
    {K Q : Type*} [Group K] [Group Q]
    (U : Subgroup K) [U.Normal] [IsElementaryAbelian 2 U]
    (q : K →* Q) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set K)) (A : Subgroup Q) (B : Subgroup K) :
    ((subspaceCommutator (NormalElementaryQuotient.representation U q hq hk) ⊤ A ⊓
      fixedSpace (NormalElementaryQuotient.representation U q hq hk) (B.map q)
        : Submodule (ZMod 2) (Additive U)).toAddSubgroup.toSubgroup').map U.subtype =
      ⁅U, A.comap q⁆ ⊓ centralizer (B : Set K) := by
  have hmap : (A.comap q).map q = A := map_comap_eq_self_of_surjective hq A
  have hm := NormalElementaryQuotient.commutatorSpace_eq U q hq hk (A.comap q)
  rw [hmap] at hm
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    change Additive.ofMul u ∈ subspaceCommutator
      (NormalElementaryQuotient.representation U q hq hk) ⊤ A ⊓
        fixedSpace (NormalElementaryQuotient.representation U q hq hk) (B.map q) at hu
    refine ⟨?_, (NormalElementaryQuotient.mem_fixedSpace_image U q hq hk B _).mp hu.2⟩
    have hv := hu.1
    rw [← hm] at hv
    exact hv
  · intro hx
    refine ⟨⟨x, (commutator_le_left U _) hx.1⟩, ?_, rfl⟩
    constructor
    · rw [← hm]
      exact hx.1
    · exact (NormalElementaryQuotient.mem_fixedSpace_image U q hq hk B _).mpr hx.2

theorem source_solvable_paired_fixed_lines
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    let S := T.subtype hH.1.1.2
    let U := (omegaOrbit T H).subgroupOf H
    let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ c : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      c.count = 2 ∧
      (∀ i j, ∃ t : S, (c.factor i).map (MulAut.conj (q t)).toMonoidHom = c.factor j) ∧
      let E := fun i => ((AddSubgroup.toSubgroup'
        (c.toSolvableFFFactors.factorFixedSpace
          ((ChapterB.baumann (S : Subgroup H)).map q) i).toAddSubgroup).map U.subtype).map H.subtype
      (∀ i, Nat.card (E i) = 2 ∧ E i ≤ V₂ ∧ Disjoint (E i) V₁) ∧
      (∀ i j, i ≠ j → Disjoint (E i) (E j) ∧ E i ⊔ E j = V₂ ∧
        ∀ a ∈ E i, a ≠ 1 → ∀ b ∈ E j, b ≠ 1 → zpowers (a * b) = V₁) ∧
      (∀ i, (T : Subgroup G) ⊓ normalizer (((c.factor i).comap q).map H.subtype : Set G) =
        ChapterB.baumann (T : Subgroup G)) := by
  let S := T.subtype hH.1.1.2
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨c,hc,ht,hn⟩ := source_solvable_paired_factor_normalizers d hH hB hZ hs hz
  let D := c.toSolvableFFFactors
  let A := (ChapterB.baumann (S : Subgroup H)).map q
  let F := fun i => D.factorFixedSpace A i
  let E := fun i => ((AddSubgroup.toSubgroup' (F i).toAddSubgroup).map U.subtype).map H.subtype
  obtain ⟨_,_,hp,_,hj⟩ := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
  have hUT : U ≤ (S : Subgroup H) :=
    hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)
  obtain ⟨hJq,hBq⟩ := ChapterE.ThompsonAction.solvable_pair_images_of_factors S hp U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    hU.quotient_pCore_eq_bot hUT hj c hc ht
  let O := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  obtain ⟨P,hP⟩ := (S.mapSurjective (QuotientGroup.mk'_surjective C)).exists_sylow_map_eq_inf_of_normal O
  have hPA : (P : Subgroup O).map O.subtype = A := hP.trans hBq.symm
  have hcard (i) : Nat.card (E i) = 2 := by
    rw [card_map_of_injective H.subtype_injective,card_map_of_injective U.subtype_injective]
    change Nat.card (F i) = 2
    dsimp [F]
    rw [← hPA]
    exact D.factorFixedSpace_card P i
  have hSm : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hH.1.1.2
  have hJm : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hSm]
  have hle (i) : E i ≤ V₂ := by
    rw [← source_alpha_eq_flag_plane d hH hB hZ hs hz,
      source_alpha_eq_omegaOrbit_fixed d hH hB hZ hs hz]
    rintro x ⟨y,⟨u,hu,rfl⟩,rfl⟩
    have hfix : Additive.ofMul u ∈ fixedSpace ρ
        ((elementaryAbelianMaxJ (S : Subgroup H)).map q) := by
      rw [hJq,← hBq]
      exact hu.2
    have hcu := (NormalElementaryQuotient.mem_fixedSpace_image U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      (elementaryAbelianMaxJ (S : Subgroup H)) (Additive.ofMul u)).mp hfix
    refine ⟨u.property,?_⟩
    intro t ht
    rw [← hJm] at ht
    obtain ⟨t,ht,rfl⟩ := ht
    exact congrArg H.subtype (hcu t ht)
  have hdisj (i j) (hij : i ≠ j) : Disjoint (E i) (E j) := by
    apply disjoint_map H.subtype_injective
    apply disjoint_map U.subtype_injective
    apply Subgroup.disjoint_def.mpr
    intro u hui huj
    exact Additive.ofMul.injective (Submodule.disjoint_def.mp
      (D.factorFixedSpace_disjoint A hij) (Additive.ofMul u) hui huj)
  have hline (i) : Disjoint (E i) V₁ := by
    apply Subgroup.disjoint_def.mpr
    rintro x ⟨y,⟨u,hu,rfl⟩,rfl⟩ hx
    have hxu : ((u : H) : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
      rwa [source_omegaCenter_eq_flag_line d hH hB hZ hs hz]
    have hcu : (u : H) ∈ centralizer (S : Set H) := by
      intro t ht
      apply Subtype.ext
      exact ((mem_omegaOneCenterAmbient_iff _ _).mp hxu).2.2 (t : G)
        (hSm ▸ mem_map_of_mem H.subtype ht)
    have hfix := (NormalElementaryQuotient.mem_fixedSpace_image U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      (S : Subgroup H) (Additive.ofMul u)).mpr hcu
    obtain ⟨k,hk⟩ := exists_ne ((finCongr hc) i)
    let j := (finCongr hc).symm k
    have hji : j ≠ i := fun he => hk (by simpa [j] using congrArg (finCongr hc) he)
    obtain ⟨t,hit⟩ := ht i j
    have hperm : D.factorConjugation (q t) i = j := D.factor_injective
      ((D.factor_map_conj (q t) i).symm.trans hit)
    have huj := D.action_mem_factor_support (q t) i hu.1
    rw [hperm] at huj
    have hfixed : ρ (q t) (Additive.ofMul u) = Additive.ofMul u :=
      hfix ⟨q t,mem_map_of_mem q t.property⟩
    change ρ (q t) (Additive.ofMul u) ∈ subspaceCommutator ρ ⊤ (D.factor j) at huj
    rw [hfixed] at huj
    have hu0 := Submodule.disjoint_def.mp (D.supports_independent.pairwiseDisjoint hji.symm)
      (Additive.ofMul u) hu.1 huj
    exact congrArg (fun w : Additive U => ((w.toMul : H) : G)) hu0
  refine ⟨c,hc,ht,fun i => ⟨hcard i,hle i,hline i⟩,?_,hn⟩
  intro i j hij
  have hcomm : E j ≤ centralizer (E i : Set G) := by
    let := d.elementary
    intro x hx y hy
    exact congrArg V.subtype (mul_comm
      (⟨y,d.flag.two_le_V (hle i hy)⟩ : V) (⟨x,d.flag.two_le_V (hle j hx)⟩ : V))
  have hn := hcomm.trans (Subgroup.centralizer_le_normalizer _)
  have hjoin : E i ⊔ E j = V₂ := by
    apply eq_of_le_of_card_ge (sup_le (hle i) (hle j))
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn (hdisj i j hij),
      hcard,hcard,d.flag.two_card]
  refine ⟨hdisj i j hij,hjoin,?_⟩
  intro a ha ha1 b hb hb1
  exact zpowers_mul_eq_third_line (E i) (E j) V₁ (hcard i) (hcard j)
    d.flag.one_card (hline i) (hline j) (hjoin ▸ d.flag.one_le_two) hn
    a b ha ha1 hb hb1

/-- The same lines are the fixed points of the literal commutator factors in H. -/
theorem source_solvable_paired_original_fixed_lines
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    let S := T.subtype hH.1.1.2
    let U := (omegaOrbit T H).subgroupOf H
    let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ c : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      c.count = 2 ∧
      (∀ i j, ∃ t : S, (c.factor i).map (MulAut.conj (q t)).toMonoidHom = c.factor j) ∧
      let E := fun i => (⁅U, (c.factor i).comap q⁆ ⊓
        centralizer (ChapterB.baumann (S : Subgroup H) : Set H)).map H.subtype
      (∀ i, Nat.card (E i) = 2 ∧ E i ≤ V₂ ∧ Disjoint (E i) V₁) ∧
      (∀ i j, i ≠ j → Disjoint (E i) (E j) ∧ E i ⊔ E j = V₂ ∧
        ∀ a ∈ E i, a ≠ 1 → ∀ b ∈ E j, b ≠ 1 → zpowers (a * b) = V₁) ∧
      (∀ i, (T : Subgroup G) ⊓ normalizer (((c.factor i).comap q).map H.subtype : Set G) =
        ChapterB.baumann (T : Subgroup G)) ∧
      ∀ i a, a ∈ E i → a ≠ 1 →
        (T : Subgroup G) ⊓ centralizer ({a} : Set G) = ChapterB.baumann (T : Subgroup G) := by
  let S := T.subtype hH.1.1.2
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨c, hc, ht, he, hj, hn⟩ := source_solvable_paired_fixed_lines d hH hB hZ hs hz
  simp only [ChapterB.SolvableFFFactors.factorFixedSpace, moved_fixed_subgroup] at he hj
  refine ⟨c, hc, ht, he, hj, hn, ?_⟩
  intro i a ha ha1
  have haV : a ∈ V₂ := (he i).2.1 ha
  have haV₁ : a ∉ V₁ := fun h => ha1 (Subgroup.disjoint_def.mp (he i).2.2 ha h)
  exact (source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz a haV haV₁).symm

/-- The original contrary core-free join supplies the center-free hypothesis. -/
theorem source_coreFree_borel_join_original_fixed_lines
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hL₁Z : borelResidual T L ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥) :
    let S := T.subtype hH.1.1.2
    let U := (omegaOrbit T H).subgroupOf H
    let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ c : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      c.count = 2 ∧
      (∀ i j, ∃ t : S, (c.factor i).map (MulAut.conj (q t)).toMonoidHom = c.factor j) ∧
      let E := fun i => (⁅U, (c.factor i).comap q⁆ ⊓
        centralizer (ChapterB.baumann (S : Subgroup H) : Set H)).map H.subtype
      (∀ i, Nat.card (E i) = 2 ∧ E i ≤ V₂ ∧ Disjoint (E i) V₁) ∧
      (∀ i j, i ≠ j → Disjoint (E i) (E j) ∧ E i ⊔ E j = V₂ ∧
        ∀ a ∈ E i, a ≠ 1 → ∀ b ∈ E j, b ≠ 1 → zpowers (a * b) = V₁) ∧
      (∀ i, (T : Subgroup G) ⊓ normalizer (((c.factor i).comap q).map H.subtype : Set G) =
        ChapterB.baumann (T : Subgroup G)) ∧
      ∀ i a, a ∈ E i → a ≠ 1 →
        (T : Subgroup G) ⊓ centralizer ({a} : Set G) = ChapterB.baumann (T : Subgroup G) :=
  source_solvable_paired_original_fixed_lines d hH hB hZ hs
    (source_center_eq_bot_of_borel_join_core_eq_bot d hH hL₁Z hcore)

end CFSG.Quasithin.Chapter13.Section02.A5Outside
