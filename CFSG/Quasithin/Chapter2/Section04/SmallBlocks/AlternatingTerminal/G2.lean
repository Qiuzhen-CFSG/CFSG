module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankOne
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.AtlasPort.LinearGroups.G2.HigherFieldResiduals
public import CFSG.Quasithin.ChapterC.Section03.A5.NaturalExtension
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.InvariantParabolic
public import CFSG.Quasithin.Chapter1.Section01
/-!
# The native even-field G₂ escape for an alternating-five block

The actual commutator layer of the block is a nonidentity two-subgroup.
Its canonical fixed-tree center selects a full parabolic which contains
its normalizer and is invariant under every automorphism preserving the
layer. Both full parabolics have characteristic two.

At any full Sylow of a selected parabolic, a local alternating-five block
would equal its rank-one solvable residual by A.3.12. Transporting the
short-block centralization axiom to that residual contradicts the native
nonzero triple commutator of its two-core. Thus the selected parabolic
is the intrinsic normalized obstruction required by the terminal source
argument. No ambient Sylow order or radical centralizer is assumed.

Source: Aschbacher--Smith 2.4.25, printed p.543, the general G₂ row.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.AlternatingTerminal.G2
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.HigherFieldResiduals
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem perfect_twoPerfect {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] : IsPPerfect 2 G := by
  intro N hn hq
  let : N.Normal := hn
  by_contra hne
  let : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (G ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (G ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (G ⧸ N) inferInstance

private noncomputable def residualEquivLocal (hq : 2 < Nat.card F) (i : Fin 2) :
    solvableResidual (parabolicAt (F := F) i) ≃* localAt (F := F) i :=
  ((solvableResidual (parabolicAt (F := F) i)).equivMapOfInjective
    (parabolicAt i).subtype (parabolicAt i).subtype_injective).trans
    (MulEquiv.subgroupCongr (parabolicAt_residual hq i))

private noncomputable def residualQuotientEquivSL (hq : 2 < Nat.card F) (i : Fin 2) :
    solvableResidual (parabolicAt (F := F) i) ⧸
      pCore 2 (solvableResidual (parabolicAt (F := F) i)) ≃* SL(2,F) :=
  ((QuotientGroup.congr _ _ (residualEquivLocal hq i)
    (pCore_map_iso 2 (residualEquivLocal hq i))).trans
      (localCoreQuotientEquivPSL i)).trans longSLEquivPSL.symm

/-- The actual alternating-five block is nonlocal at every full parabolic Sylow. -/
theorem parabolic_not_local (hq : 2 < Nat.card F) (i : Fin 2)
    (B : Subgroup (parabolicAt (F := F) i)) (hB : ChapterC.IsAlternatingBlock B 5)
    (S : Sylow 2 (parabolicAt (F := F) i)) :
    B ∉ ChapterA.Section03.localCComponents S := by
  let R := solvableResidual (parabolicAt (F := F) i)
  let e := residualQuotientEquivSL hq i
  let f : R →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect SL(2,F) := Group.IsPerfect.ofSurjective hf
  have h4 : 4 ≤ Nat.card F := by
    obtain ⟨n,hn,hcard⟩ := field_card (F := F)
    have hn2 : 1 < n := (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
      (by simpa only [pow_one,← hcard] using hq)
    calc 4 = 2^2 := rfl
         _ ≤ 2^n := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn2
         _ = Nat.card F := hcard.symm
  let : IsQuasisimple SL(2,F) :=
    { toIsPerfect := inferInstance, simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4 }
  let : IsQuasisimple (R ⧸ pCore 2 R) := IsQuasisimple.of_mulEquiv e.symm
  have hR : R.IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient
      (Subgroup.Normal.isSubnormal inferInstance) perfect_twoPerfect
  let := hB.perfect_five
  have hBR : B ≤ R := le_solvableResidual_of_isPerfect B
  intro hlocal
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_rankOne_cover S hlocal hR hBR f hf
  have hshort : ChapterC.IsShort (localAt (F := F) i) :=
    ChapterC.RankOne.Solvable.isShort_of_equiv (residualEquivLocal hq i) (show ChapterC.IsShort R from he ▸ hB.2.1)
  exact local_core_triple i (commutator_eq_bot_iff_le_centralizer.mpr hshort.central)

/-- Both actual full parabolics have characteristic two. -/
theorem parabolic_mem_He (i : Fin 2) : parabolicAt (F := F) i ∈ Chapter1.He (Model F) := by
  apply Chapter1.mem_He_iff.mpr
  fin_cases i
  · exact Atlas.G2.EvenLocal.parabolic₁_centralizer_pCore
  · exact Atlas.G2.EvenLocal.parabolic₂_centralizer_pCore

private theorem parabolic_equiv_not_local (hq : 2 < Nat.card F) (i : Fin 2)
    {P : Subgroup (Model F)} (e : P ≃* parabolicAt (F := F) i)
    (B : Subgroup P) (hB : ChapterC.IsAlternatingBlock B 5) (Q : Sylow 2 P) :
    B ∉ ChapterA.Section03.localCComponents Q := by
  intro hlocal
  have hBm : ChapterC.IsAlternatingBlock (B.map e.toMonoidHom) 5 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
      (B.equivMapOfInjective e.toMonoidHom e.injective) hB
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  exact parabolic_not_local hq i (B.map e.toMonoidHom) hBm
    (Q.mapSurjective e.surjective)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal e.toMonoidHom)

/-- The literal block commutator layer selects an automorphism-invariant
characteristic-two escape; the original block is nonlocal at every full Sylow. -/
theorem invariant_parabolic_obstruction (hq : 2 < Nat.card F)
    (A : Subgroup (Model F)) (hA : ChapterC.IsAlternatingBlock A 5) :
    let U := (ChapterC.blockU A).map A.subtype
    ∃ P : Subgroup (Model F), P ∈ Chapter1.He (Model F) ∧ A ≤ P ∧
      (∀ a : MulAut (Model F), U.map a.toMonoidHom = U → P.map a.toMonoidHom = P) ∧
      ∀ Q : Sylow 2 P, A.subgroupOf P ∉ ChapterA.Section03.localCComponents Q := by
  let U := (ChapterC.blockU A).map A.subtype
  have hUb : ChapterC.blockU A ≠ ⊥ :=
    ne_of_gt (lt_of_le_of_lt bot_le hA.2.1.irreducible.1)
  have hU : U ≠ ⊥ := by
    intro h
    apply hUb
    apply map_injective A.subtype_injective
    rw [Subgroup.map_bot]
    exact h
  have hpU : IsPGroup 2 U := (pCore_isPGroup.to_le ChapterC.blockU_le_core).map A.subtype
  have hAN : A ≤ normalizer (U : Set (Model F)) := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (ChapterC.blockU A))
  obtain ⟨P,⟨g,hg⟩,hNP,hinv⟩ :=
    Atlas.G2.EvenLocal.NormalizerCover.exists_invariant_parabolic hq U hU hpU
  have hep : ∃ i : Fin 2, Nonempty (P ≃* parabolicAt (F := F) i) := by
    rcases hg with he | he
    · refine ⟨0,⟨?_⟩⟩
      exact ((parabolic₁.equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr he.symm)).symm
    · refine ⟨1,⟨?_⟩⟩
      exact ((parabolic₂.equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr he.symm)).symm
  obtain ⟨i,⟨e⟩⟩ := hep
  have hAP : A ≤ P := hAN.trans hNP
  refine ⟨P,Chapter1.mem_He_iff.mpr ?_,hAP,hinv,?_⟩
  · exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr
      (Chapter1.mem_He_iff.mp (parabolic_mem_He i))
  · intro Q
    exact parabolic_equiv_not_local hq i e (A.subgroupOf P)
      (ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
        (subgroupOfEquivOfLe hAP).symm hA) Q
end CFSG.Quasithin.Chapter2.AlternatingTerminal.G2
