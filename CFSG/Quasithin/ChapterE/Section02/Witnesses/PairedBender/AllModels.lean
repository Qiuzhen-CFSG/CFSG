module
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.Paired
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.LinearSource
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Suzuki.Source
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.AllPrimes

/-!
# All actual paired source families in E.2.7

The genuine component-model sieve and sporadic exclusion leave binary
PSL₂, Suzuki, and odd-prime PSL₂. The three constructed paired witnesses
give the original pair and its marked core quotient in every case. The
field-five comparison is made explicitly with PSL₂(4), so its model degree
is two. All other surviving odd primes have degree one.

The model parameter is retained independently of the ambient generation
parameter. No family, placement, projection bound or witness is an input.
The only earlier classification input is the genuine universal Theorem C.
Source: Aschbacher–Smith E.2.2(1) and E.2.7, printed pp.215–219.
-/

@[expose] public section
noncomputable section
open Subgroup Matrix Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedBender
universe u

inductive ModelAt (D : Type*) [Group D] : ℕ → Prop
  | linear {n : ℕ} (positive : 2 ≤ n) (model : ClassicalGroup.IsPSL D 2 (2^n)) : ModelAt D n
  | suzuki {m : ℕ} (positive : 0 < m) (model : Nonempty (D ≃* SuzukiMatrixGroup m)) : ModelAt D (2*m+1)
  | odd (p : ℕ) (prime : p.Prime) (odd : Odd p) (large : 7 ≤ p)
      (model : ClassicalGroup.IsPSL D 2 p) : ModelAt D 1

variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

theorem LinearAlternative.originalWitness {T : Sylow 2 H} {M V : Subgroup H} {n : ℕ}
    (w : LinearAlternative T M V n) : Nonempty (BenderPlacement.OriginalWitness T M V n) := by
  cases w with
  | linear hw =>
    obtain ⟨w⟩ := hw
    exact ⟨⟨w.pair,w.degree,by have := w.degree_gt_one; omega,w.degree_dvd,
      .linear w.degree_gt_one w.model w.borel_model⟩⟩
  | dihedral p hp hp2 w a ha he =>
    obtain ⟨e⟩ := he
    exact ⟨⟨w,1,by decide,one_dvd _,.dihedral rfl p a hp hp2 ha e⟩⟩

private theorem five_binary_model {D : Type*} [Group D]
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 5) (e : D ≃* PSL(2,F)) :
    ClassicalGroup.IsPSL D 2 (2^2) := by
  let : Fintype F := Fintype.ofFinite F
  let eF : ZMod 5 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let eA := (e.trans (GorensteinWalter.psl2RingEquiv eF).symm).trans
    GorensteinWalter.alternatingGroupFive_equiv_PSL2.some.symm
  have hfour : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]; norm_num
  let e4 := (ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour).some
  exact ⟨GaloisField 2 2,inferInstance,inferInstance,hfour,⟨eA.trans e4.symm⟩⟩

/-- The actual core-free paired source configuration constructs its family and original witness. -/
theorem coreFree_source
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup H) (hK : IsComponent H K)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVN : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2) (hV : V ≠ ⊥) :
    ∃ n : ℕ, ModelAt K n ∧
      Nonempty (BenderPlacement.OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n) := by
  have hrad : solvableRadical H = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  let : IsSimpleGroup K := hK.isCComponent.isSimpleGroup_of_solvableRadical_eq_bot hrad
  rcases Structure.source_paired_component_models hC hH T hP hs hJ K hK hgen hn with
    ⟨n,hnn,hm⟩ | ⟨m,hm,⟨e⟩⟩ | ⟨p,hp,ho,hm⟩
  · refine ⟨n,.linear hnn hm,?_⟩
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let eL := e.trans (SpecialLinearGroup.TwoConjugateWitness.slEquivPSL F).symm
    exact (source_linear_pair (by omega) hF hH.stronglyQuasithin T hP hs hJ hK hK.isCComponent
      hgen hn eL V hVT hVM hV).originalWitness
  · exact ⟨2*m+1,.suzuki (by omega) ⟨e⟩,Suzuki.source (by omega) hH.stronglyQuasithin
      T hP hJ hK hgen hn e V hVT hVM hV⟩
  · let : Fact p.Prime := ⟨hp⟩
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    by_cases h5 : p = 5
    · exact ⟨2,.linear (by decide) (five_binary_model (hF.trans h5) e),
        (PairedOddLinearTwo.source_five_pair (hF.trans h5) hH.stronglyQuasithin T hP hs hJ
          hK hK.isCComponent hgen hn e V hVT hVM hV).originalWitness⟩
    have h3 : p ≠ 3 := fun he => PairedOddLinearTwo.component_not_equiv_field_three (hF.trans he) hK e
    have hlarge : p = 7 ∨ 9 < p := by
      by_contra! hh
      have hle : p ≤ 9 := hh.2
      have hprime : p.Prime := hp
      interval_cases p <;> norm_num at *
    obtain ⟨w⟩ := PairedOddLinearTwo.source_pair ho hF hlarge hH.stronglyQuasithin
      T hP hs hJ hK hK.isCComponent hgen hn e V hVT hVN hVM hV
    refine ⟨1,.odd p hp ho (by omega) ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩,?_⟩
    exact ⟨⟨w.toPair,1,by decide,one_dvd _,
      .dihedral rfl w.prime w.degree w.prime_prime w.prime_odd w.degree_pos w.model⟩⟩

end CFSG.Quasithin.ChapterE.Witnesses.PairedBender
