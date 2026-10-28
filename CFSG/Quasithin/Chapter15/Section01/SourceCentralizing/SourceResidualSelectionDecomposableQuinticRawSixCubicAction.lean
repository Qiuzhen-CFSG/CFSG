module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryAction
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.GroupTheory.PCoreNormalizerAction
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryRank

/-!
# The original moving sixteen acts trivially on the full central A6 core

The actual opposite quintic actor acts irreducibly on its sixteen-element
support. Its intersection with the core-action kernel is invariant. The
faithful alternative would embed an elementary sixteen in Aut(A6), contrary
to the native bound eight. Faithful automorphism descent for a perfect
central cover retains the entire center of L/O₂(L), including a cubic center.

Thus the literal original commutator [V,O²(C_M(Z₁))] acts trivially on L/O₂(L).
Its action on L can remain noncentral; no whole-core reconstruction, radical
Sylow assertion, star/normalizer-image identification or M-generation is used.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem no_sixteen_faithful_core_action
    {H B : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [Group B] [Finite B] [IsElementaryAbelian 2 B]
    (hb : Nat.card B = 16)
    (e : (H ⧸ center H) ≃* alternatingGroup (Fin 6))
    (a : B →* MulAut H) (ha : Function.Injective a) : False := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let c : PerfectCentralCovering.Cover H (alternatingGroup (Fin 6)) :=
    ⟨q,hq,inferInstance,hk.le⟩
  let f := (c.autMap hk).comp a
  have hf : Function.Injective f := (c.autMap_injective hk).comp ha
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hh := AlternatingSix.ShadowLocal.elementary_card_le_eight f.range
  have he : Nat.card f.range = Nat.card B :=
    Nat.card_congr (MonoidHom.ofInjective hf).symm.toEquiv
  rw [he,hb] at hh
  omega

private theorem irreducible_sixteen_core_commutator
    {A B L : Subgroup G} [IsElementaryAbelian 2 B]
    (hcard : Nat.card B = 16) (hAB : A ≤ normalizer (B : Set G))
    (hAL : A ≤ normalizer (L : Set G)) (hBL : B ≤ normalizer (L : Set G))
    (hir : ∀ K : Subgroup G, K ≤ B → A ≤ normalizer (K : Set G) → K = ⊥ ∨ K = B)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (e : ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃*
      alternatingGroup (Fin 6)) : ⁅B,L⁆ ≤ L.pCoreIn 2 := by
  let N := normalizer (L : Set G)
  let a := pCoreNormalizerAction 2 L
  let K := a.ker.map N.subtype
  have hNK : N ≤ normalizer (K : Set G) := by
    intro n hn
    apply a.ker.le_normalizer_map N.subtype
    exact ⟨⟨n,hn⟩,le_normalizer_of_normal (mem_top _),rfl⟩
  have hBK : B ≤ K := by
    rcases hir (B ⊓ K) inf_le_left (le_normalizer_inf hAB (hAL.trans hNK)) with hz | he
    · let f := a.comp (inclusion hBL)
      have hf : Function.Injective f := by
        apply (MonoidHom.ker_eq_bot_iff _).mp
        apply bot_unique
        intro b hb
        have hh : (b : G) ∈ B ⊓ K :=
          ⟨b.property,inclusion hBL b,hb,rfl⟩
        rw [hz] at hh
        exact Subtype.ext (mem_bot.mp hh)
      let : Group.IsPerfect (L ⧸ pCore 2 L) := hq.toIsPerfect
      exact (no_sixteen_faithful_core_action hcard e f hf).elim
    · exact he.symm.le.trans inf_le_right
  apply commutator_le.mpr
  intro b hb l hl
  obtain ⟨n,hn,he⟩ := hBK hb
  have he' : n = inclusion hBL ⟨b,hb⟩ := Subtype.ext he
  have ha : a (inclusion hBL ⟨b,hb⟩) = 1 := he' ▸ hn
  have hm := (pCoreNormalizerAction_eq_one_iff 2 L (inclusion hBL ⟨b,hb⟩)).mp ha ⟨l,hl⟩
  refine ⟨_,hm,?_⟩
  simp only [commutatorElement_def,div_eq_mul_inv]
  rfl

private theorem raw_six_moving_core_commutator
    {T : Sylow 2 G} {M V L : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hJi : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn))
    (hfive : s.prime = 5)
    (hnL : let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z1 : Set G); let R := (pResidual 2 C).map C.subtype
      R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G))
    (hLq : IsQuasisimple (L ⧸ pCore 2 L))
    (e : ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃*
      alternatingGroup (Fin 6)) :
    let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
    let C := M ⊓ centralizer (Z1 : Set G)
    let R := (pResidual 2 C).map C.subtype
    ⁅⁅V,R⁆,L⁆ ≤ L.pCoreIn 2 := by
  intro Z1 C R
  let B := plane V (c.ambientFactor d s.second).space
  let A := (primeToResidual 5 C).map C.subtype
  have hWB : ⁅V,R⁆ = B := (s.full_residual_geometry hTM hn c d π hp hs hJi).2.1
  have hRB : R ⊔ B ≤ normalizer (L : Set G) := hWB ▸ hnL
  obtain ⟨_,_,hAmove,_,_,_,_,hAR⟩ := s.quintic_actor_geometry hTM hn c d π hp hs hJi hfive
  have hAB : A ≤ normalizer (B : Set G) := by
    change A ≤ normalizer (plane V (c.ambientFactor d s.second).space : Set G)
    rw [←hAmove]
    exact normalizer_commutator_ge_right V A
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (plane_le _)
  rw [hWB]
  exact irreducible_sixteen_core_commutator (s.support_card s.second) hAB
    (hAR.trans (le_sup_left.trans hRB)) (le_sup_right.trans hRB)
    (s.quintic_actor_irreducible hTM hn c d π hp hs hJi hfive) hLq e

/-- The literal original quintic moving support acts trivially on the full
core quotient in either central A6 row, including its cubic covering center. -/
theorem PreparedChosenModule.decomposable_five_raw_six_moving_support_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z1 : Set G)
      let R := (pResidual 2 C).map C.subtype
      ∀ {L : Subgroup G}, R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) →
        IsQuasisimple (L ⧸ pCore 2 L) →
        ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* alternatingGroup (Fin 6) →
        ⁅⁅V,R⁆,L⁆ ≤ L.pCoreIn 2 := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 C R L hnL hLq e
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun A hA => hA.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  exact raw_six_moving_core_commutator hM.1.2 h.normalized c d s π hp hs hJi hfive hnL hLq e

end CFSG.Quasithin.Chapter15.Section01
