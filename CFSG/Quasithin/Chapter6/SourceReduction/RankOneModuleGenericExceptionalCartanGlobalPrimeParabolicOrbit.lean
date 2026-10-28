module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicHeldContainers
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ClassicalLocalPairs
public import Theory.GroupTheory.SylowTwoOrbitSpans

/-!
# Excluding the classical changed-Sylow orbit

The fixed full Sylow in the original diagram residual normalizes at most
two proper local components, including in the cubic SL₃ cover. Both
ambient Sylows have this same intersection with the residual. If the
changed Sylow normalized that residual, its orbit of the selected local
factor would equal the original Sylow orbit, contradicting the checked
Hall-preserving conjugate escape.

Every surviving common component is already the original residual and
is relatively normal in the literal common overgroup. Hence this argument
excludes all remaining nonzero-core prime pairs. The same selected pair
now supplies the zero-core F.1.1 setup, with its original source Sylow,
Cartans, residual and quotient kernels. Recognition of that zero-core
setup and the universal local-to-global normalization remain separate
obligations of the source assembly.

Source: Aschbacher–Smith 5.2.2, printed pp.648–649, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterA.Section03.SourceEmbeddings ClassicalLocalPairs
open Chapter1.Section02 LocalModels
variable {G : Type*} [Group G] [Finite G]

private theorem diagram_local_card
    {Y : Type*} [Group Y] [Finite Y] {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL Y 3 (2^f) ∨ IsSL Y 3 (2^f) ∨ ClassicalGroup.IsPSp Y 2 (2^f))
    (S : Sylow 2 Y) : Nat.card (NormalizedProperLocals (S : Subgroup Y)) ≤ 2 := by
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (f := f)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact (card_le_of_equiv e (S : Subgroup Y)).trans (linear_card hf hF (S.mapSurjective e.surjective))
  · let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (f := f)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact (card_le_of_equiv e (S : Subgroup Y)).trans
      (specialLinear_card hf hF (S.mapSurjective e.surjective))
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let a := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
    exact (card_le_of_equiv a (S : Subgroup Y)).trans
      (symplectic_card hf hF (S.mapSurjective a.surjective))

/-- The original diagram residual cannot be normalized by the larger changed
Sylow. Its common Sylow intersection leaves only two proper local factors,
so both full Sylows would generate the same parabolic orbit. -/
theorem LocalData.changedSylow_not_normalizes_diagram_residual
    {T U : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hs : SelectedSourceModels H R) (hr : ¬ (R.subgroupOf H).IsCComponent)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    (hU : (U : Subgroup G) =
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype) :
    ¬ (U : Subgroup G) ≤ normalizer (residual H : Set G) := by
  intro hUK
  let K := residual H
  have hKH : K ≤ H := map_subtype_le _
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) := hH.1.1.2.trans (le_normalizer_residual H)
  have hcomp := hs.residual_component_of_not_right hr
  let : Group.IsPerfect (K.subgroupOf H) := hcomp.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  have hSK : (S : Subgroup K).map K.subtype = (T : Subgroup G) ⊓ K := by
    rw [hS,subgroupOf_map_subtype]
  have hKT0 : (T : Subgroup G) ⊓ K ≤ normalizingSylow T R := by
    rw [←d.S_intersection_residual]
    exact inf_le_left.trans (d.sourceS_le_normalizingSylow h hH)
  have hT0 : (normalizingSylow T R).subgroupOf K = (S : Subgroup K) := by
    rw [hS]
    exact le_antisymm (comap_mono inf_le_left) (fun x hx => hKT0 ⟨hx,x.property⟩)
  have hl : R.subgroupOf K ∈ ChapterA.Section03.localCComponents (S : Subgroup K) := by
    rw [←hT0]
    exact local_restrict d.right_component d.right_le_residual
  have hn : (S : Subgroup K) ≤ normalizer (R.subgroupOf K : Set K) := by
    rw [←subgroupOf_normalizer_eq d.right_le_residual,hS]
    intro x hx
    exact (hKT0 ⟨hx,x.property⟩).2
  have hp : R.subgroupOf K ≠ ⊤ := fun he =>
    (d.right_lt_residual hH.1.1.2 c hd hz).not_ge (subgroupOf_eq_top.mp he)
  let a := ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let q := aq.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := aq.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 K := by
    ext x
    change aq (QuotientGroup.mk' (pCore 2 K) x) = 1 ↔ x ∈ pCore 2 K
    rw [←aq.map_one,aq.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hk : IsPGroup 2 q.ker := hker ▸ pCore_isPGroup
  obtain ⟨f,hf,_,hm⟩ := hs.resolve_left hr
  have hc : Nat.card (NormalizedProperLocals (S : Subgroup K)) ≤ 2 :=
    (two_kernel_card S q hq hk).trans (diagram_local_card hf hm (S.mapSurjective hq))
  have hUS : (S : Subgroup K).map K.subtype = (U : Subgroup G) ⊓ K := by
    have hi := (d.changedSylow_intersections h hH P hTP).2.1
    rw [←hU] at hi
    exact hSK.trans hi.symm
  let N := normalizer (((S : Subgroup K).map K.subtype : Subgroup G) : Set G) ⊓
    normalizer (K : Set G)
  have hTN : (T : Subgroup G) ≤ N := by
    refine le_inf ?_ hTK
    rw [hSK]
    exact (le_inf (T : Subgroup G).le_normalizer hTK).trans inf_normalizer_le_normalizer_inf
  have hUN : (U : Subgroup G) ≤ N := by
    refine le_inf ?_ hUK
    rw [hUS]
    exact (le_inf (U : Subgroup G).le_normalizer hUK).trans inf_normalizer_le_normalizer_inf
  have hi := normalizer_relIndex_le_two K N R S d.right_le_residual inf_le_right inf_le_left hl hn hp hc
  have heT := conjugateSpanBy_sylow_eq_of_relIndex_le_two R N (T.subtype hTN) hi
  have heU := conjugateSpanBy_sylow_eq_of_relIndex_le_two R N (U.subtype hUN) hi
  change conjugateSpanBy R (((T : Subgroup G).subgroupOf N).map N.subtype) = _ at heT
  change conjugateSpanBy R (((U : Subgroup G).subgroupOf N).map N.subtype) = _ at heU
  rw [map_subgroupOf_eq_of_le hTN] at heT
  rw [map_subgroupOf_eq_of_le hUN] at heU
  apply d.changedSylow_orbit_not_normalized h hH c hd hz P hTP hU
  rw [heU.trans heT.symm]
  exact le_normalizer_conjugateSpanBy R (T : Subgroup G)

/-- The nonzero-core prime-pair branch is impossible, including all classical
and cubic common containers. The literal zero-core F.1.1 setup remains. -/
theorem source_prime_pair_zero_core
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (generated L H D R).pCoreIn 2 = ⊥ ∧
      ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_parabolic_held_exclusion h hH hgen hthree c hd
  rcases hcases with hz | ⟨hz,_,_,_,P,hlt,_,U,hU,hr,_,I,_,hIX,_,hIn,_,_,hm⟩
  · exact ⟨R,d,hs,hz⟩
  have hKI : residual H = I := by
    rcases hm with ⟨_,g,_,_,he⟩ | ⟨_,f,_,_,_,he,_⟩
    · exact he
    · exact he
  apply (d.changedSylow_not_normalizes_diagram_residual h hH c hd hz hs hr P hlt.le hU ?_).elim
  rw [hKI]
  apply le_trans _ ((normal_subgroupOf_iff_le_normalizer hIX).mp hIn)
  exact (d.overgroup_two_subgroup_normalizes hH.1.1.2 c hd hz U.isPGroup'
    (hlt.le.trans_eq hU.symm)).trans le_sup_left

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
