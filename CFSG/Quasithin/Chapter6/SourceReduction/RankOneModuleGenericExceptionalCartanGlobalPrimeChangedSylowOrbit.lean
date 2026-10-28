module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeChangedSylowRemainder

/-!
# The changed orbit and the original residual in source 5.2.2

Let U be the ambient changed Sylow and K₀ = ⟨R^U⟩. A subgroup containing
R inside G₀T₀B cannot be invariant under both T and U. Indeed, in the
intersection of its normalizer with N_G(T₀), Hall-preserving Sylow conjugacy
fixes the actual Cartan A and its prime subgroup D while sending T to U.
It would send R into G₀T₀B, contradicting the proved conjugate escape.

Consequently T does not normalize K₀, the changed residual differs from
O²(H), and K₀ is properly contained in the common normal component orbit.
The same selected source pair carries all these conclusions. Thus proving
the source orbit equality would already exclude the larger changed Sylow;
no additional changed local-input assumptions are needed for that step.
The orbit equality, the remaining smaller containing cases, compatible
zero-core recognition and higher-field normalization are not asserted here.

Source: Aschbacher–Smith 5.2.2, printed pp.648–649 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

private theorem LocalData.changedSylow_invariant_not_le_extension
    {T U : Sylow 2 G} {L W H A B D R Y : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    (hU : (U : Subgroup G) =
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    (hRY : R ≤ Y) (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hUY : (U : Subgroup G) ≤ normalizer (Y : Set G)) :
    ¬ Y ≤ extension T L H B D R := by
  intro hKE
  let N := normalizer (normalizingSylow T R : Set G) ⊓
    normalizer (Y : Set G)
  have hTU : normalizingSylow T R ≤ (U : Subgroup G) := hTP.trans_eq hU.symm
  have hTN : (T : Subgroup G) ≤ N := le_inf
    (d.overgroup_two_subgroup_normalizes hH.1.1.2 c hd hz T.isPGroup' inf_le_left)
    hTY
  have hUN : (U : Subgroup G) ≤ N := le_inf
    (d.overgroup_two_subgroup_normalizes hH.1.1.2 c hd hz U.isPGroup' hTU) hUY
  have hUL : (T : Subgroup G) ⊓ L ≤ (U : Subgroup G) := by
    rw [←d.S_intersection_left]
    exact inf_le_left.trans ((d.sourceS_le_normalizingSylow h hH).trans hTU)
  obtain ⟨Q,hQ⟩ := exists_sylow_localBorel T L h.sylow_normalizes
  obtain ⟨x,hxN,hxA,hxT⟩ := OddHall.sylow_conjugate_fixing_hall
    N (localBorel T L) ((T : Subgroup G) ⊓ L) A T U hTN hUN hUL
    (inf_le_left.trans (d.normalizingSylow_normalizer_preserves_borel h hH c hd hz))
    (localBorel_isSolvable h.exponent h.linear h.sylow_normalizes) Q hQ c.left_le c.left_hall
  let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
  have hxD := normalizer_le_normalizer_of_le_cyclic D A hd.le_cartan hxA
  have hxK := mem_normalizer_iff_map_conj_eq.mp hxN.2
  apply d.changedSylow_conjugate_outside hd hz P hU hxD hxT
  exact ((map_mono (f := (MulAut.conj x).toMonoidHom) hRY).trans_eq hxK).trans hKE

/-- The changed orbit inside the nonzero-core extension cannot be invariant
under the original full Sylow. Both the Hall subgroup and D are preserved
by the Sylow conjugator used in the proof. -/
theorem LocalData.changedSylow_orbit_not_normalized
    {T U : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    (hU : (U : Subgroup G) =
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype) :
    ¬ (T : Subgroup G) ≤ normalizer (conjugateSpanBy R (U : Subgroup G) : Set G) := by
  intro hn
  apply d.changedSylow_invariant_not_le_extension h hH c hd hz P hTP hU
    (le_conjugateSpanBy R _) hn (le_normalizer_conjugateSpanBy R _)
  exact conjugateSpanBy_le
    (le_sup_left.trans (le_sup_right.trans (le_sup_left.trans le_sup_left)))
    ((hU ▸ map_subtype_le _).trans (extension T L H B D R).le_normalizer)

/-- Equality of the literal changed and original residuals would contradict
the orbit obstruction, without further hypotheses at the changed Sylow. -/
theorem LocalData.changedSylow_residual_ne_original
    {T U : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    (hU : (U : Subgroup G) =
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype) :
    residual (R ⊔ (U : Subgroup G)) ≠ residual H := by
  intro he
  apply d.changedSylow_orbit_not_normalized h hH c hd hz P hTP hU
  have horbit := d.changedSylow_residual_eq_conjugateSpan h hH P
  rw [←hU] at horbit
  rw [←horbit,he]
  exact hH.1.1.2.trans (le_normalizer_residual H)

/-- The actual unique common overcomponent strictly contains R, and its
normal T-orbit strictly contains the changed U-orbit of R. -/
theorem LocalData.changedSylow_common_orbit_strict
    {T U : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    (hU : (U : Subgroup G) =
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype) :
    let X := normalizer (normalizingSylow T R : Set G) ⊔ H
    ∃ I : Subgroup G, R < I ∧ I ≤ X ∧ (I.subgroupOf X).IsCComponent ∧
      normalizingSylow T R ≤ normalizer (I : Set G) ∧
      (∀ J : Subgroup G, J ≤ X → (J.subgroupOf X).IsCComponent → R ≤ J → J = I) ∧
      let Kplus := conjugateSpanBy I (T : Subgroup G)
      residual H ≤ Kplus ∧ Kplus ≤ X ∧ (Kplus.subgroupOf X).Normal ∧
        (U : Subgroup G) ≤ normalizer (Kplus : Set G) ∧
        conjugateSpanBy R (U : Subgroup G) < Kplus := by
  obtain ⟨I,hRI,hIX,hI,hTI,hu,hKJ,hJX,hJn,hUJ,hK0J⟩ :=
    d.changedSylow_common_component h hH c hd hz P hTP
  rw [←hU] at hUJ hK0J
  have hRI' : R < I := lt_of_le_of_ne hRI (by
    intro he
    apply d.changedSylow_not_common_component h hH c hd hz P hTP hU
    simpa only [he] using hI)
  refine ⟨I,hRI',hIX,hI,hTI,hu,hKJ,hJX,hJn,hUJ,lt_of_le_of_ne hK0J ?_⟩
  intro he
  apply d.changedSylow_orbit_not_normalized h hH c hd hz P hTP hU
  rw [he]
  exact le_normalizer_conjugateSpanBy I _

/-- Retain the source catalogue and original Hall markings on the same
selected R, with the strict common-orbit geometry in the larger-Sylow case. -/
theorem source_prime_pair_changedSylow_orbit
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R ≤ T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ((T₁ = normalizingSylow T R ∧
            let X := generated L H D R ⊔ normalizingSylow T R
            let q := QuotientGroup.mk' (pCore 2 X)
            ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
              (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
              (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
              RemainingSourceContainer X K) ∨
            (∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
              normalizingSylow T R < T₁ ∧ RemainingLargerSource H R p n ∧
              ¬ (T : Subgroup G) ≤ normalizer (conjugateSpanBy R T₁ : Set G) ∧
              residual (R ⊔ T₁) ≠ residual H ∧
              let X := normalizer (normalizingSylow T R : Set G) ⊔ H
              ∃ I : Subgroup G, R < I ∧ I ≤ X ∧ (I.subgroupOf X).IsCComponent ∧
                normalizingSylow T R ≤ normalizer (I : Set G) ∧
                (∀ J : Subgroup G, J ≤ X → (J.subgroupOf X).IsCComponent → R ≤ J → J = I) ∧
                let Kplus := conjugateSpanBy I (T : Subgroup G)
                residual H ≤ Kplus ∧ Kplus ≤ X ∧ (Kplus.subgroupOf X).Normal ∧
                  T₁ ≤ normalizer (Kplus : Set G) ∧ conjugateSpanBy R T₁ < Kplus)))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_changedSylow_remainder h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hTP,hDT,?_⟩
  rcases hcases with hsmall | ⟨U,hU,hlt,hm⟩
  · exact .inl hsmall
  refine .inr ⟨U,hU,hlt,hm,?_,?_,?_⟩
  · simpa only [←hU] using d.changedSylow_orbit_not_normalized h hH c hd hz P hTP hU
  · simpa only [←hU] using d.changedSylow_residual_ne_original h hH c hd hz P hTP hU
  · simpa only [←hU] using d.changedSylow_common_orbit_strict h hH c hd hz P hTP hU

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
