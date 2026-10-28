module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.BlockConstruction
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.OffenderGeneration
public import Theory.Representation.RegularCyclicNormalClosure.Seed
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Pi

/-!
# Internal products of the solvable FF blocks

Enumerate the distinct actual subgroups [O₂′(G), A]A, with A a minimal
best offender. The local construction gives each block its natural binary
plane and a complementary fixed space. Distinct blocks fix one another's
planes; the complement and faithfulness imply independence of the planes
and of the group factors. Best-offender generation identifies their join
with J(G,V).

The commuting product map and the sum of the support inclusions are
injective and have exactly the required ranges. Passing to those ranges
constructs the two equivalences in `SolvableFFFactors`, including their
coordinate-inclusion identities. The FF hypothesis supplies a minimal
best offender, so the finite factor family is nonempty.

Source: Kurzweil–Stellmacher, *The Theory of Finite Groups*, 9.3.7,
printed p.246 (PDF p.259 of `refs/original/kurzweil.pdf`), assembling the
local results 9.3.2–9.3.6. This proves the internal decompositions in
Aschbacher–Smith B.1.8(1)–(2), printed p.70 (PDF p.81).
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Glauberman
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem moved_eq_displacement (E : Subgroup G) :
    subspaceCommutator ρ ⊤ E =
      Representation.RegularCyclicNormalClosure.displacementSpan ρ E ⊤ := by
  unfold subspaceCommutator Representation.RegularCyclicNormalClosure.displacementSpan
  congr 1
  ext v
  simp only [eq_comm]

private theorem moved_mono {E F : Subgroup G} (h : E ≤ F) :
    subspaceCommutator ρ ⊤ E ≤ subspaceCommutator ρ ⊤ F := by
  apply Submodule.span_mono
  rintro _ ⟨a, ha, v, hv, rfl⟩
  exact ⟨a, h ha, v, hv, rfl⟩

private theorem moved_iSup {ι : Type*} (E : ι → Subgroup G) :
    subspaceCommutator ρ ⊤ (⨆ i, E i) = ⨆ i, subspaceCommutator ρ ⊤ (E i) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, _, rfl⟩
    have hh : ∀ v : V, ρ a v - v ∈ ⨆ i, subspaceCommutator ρ ⊤ (E i) := by
      refine Subgroup.iSup_induction E
        (C := fun a => ∀ v : V, ρ a v - v ∈ ⨆ i, subspaceCommutator ρ ⊤ (E i))
        ha ?_ ?_ ?_
      · intro i a ha v
        exact le_iSup (fun i => subspaceCommutator ρ ⊤ (E i)) i
          (Submodule.subset_span ⟨a, ha, v, Submodule.mem_top, rfl⟩)
      · intro v
        simp
      · intro a b ha hb v
        have hh := (⨆ i, subspaceCommutator ρ ⊤ (E i)).add_mem (ha (ρ b v)) (hb v)
        simpa only [map_mul, Module.End.mul_apply, sub_add_sub_cancel] using hh
    exact hh v
  · exact iSup_le fun i => moved_mono ρ (le_iSup E i)

/-- Distinct local blocks fix one another's actual supports. -/
theorem localBlocks_cross_fixed [Finite G] [FiniteDimensional (ZMod 2) V]
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 G = ⊥) (hρ : Function.Injective ρ)
    {A B : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hB : IsMinimalBestOffender ρ B)
    (dA : SolvableFFLocalBlock ρ A) (dB : SolvableFFLocalBlock ρ B)
    (hne : dA.factor ≠ dB.factor) :
    subspaceCommutator ρ ⊤ dA.factor ≤ fixedSpace ρ dB.factor := by
  have hrA := minimalBestOffender_rank_one ρ hρ hsolv hcore hA
  have hrB := minimalBestOffender_rank_one ρ hρ hsolv hcore hB
  obtain ⟨x, hx, hxc⟩ := BlockConstruction.exists_noncentral_odd ρ hsolv hcore hA
  obtain ⟨y, hy, hyc⟩ := BlockConstruction.exists_noncentral_odd ρ hsolv hcore hB
  obtain ⟨dx⟩ := BlockConstruction.pairData_nonempty ρ hρ hA hrA hx hxc
  obtain ⟨dy⟩ := BlockConstruction.pairData_nonempty ρ hρ hB hrB hy hyc
  have heA := dA.factor_eq.trans
    (BlockConstruction.factor_pair_identification ρ hsolv hρ hA hrA hx hxc).1
  have heB := dB.factor_eq.trans
    (BlockConstruction.factor_pair_identification ρ hsolv hρ hB hrB hy hyc).1
  have hh := BlockConstruction.minimal_pair_alternative ρ hsolv hρ hA hB hrA hrB
    hx hxc hy hyc dx dy
  rw [← heA, ← heB] at hh
  exact (hh.resolve_left fun h => hne h.symm).2

private theorem assemble [Finite G] [FiniteDimensional (ZMod 2) V]
    (hρ : Function.Injective ρ) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Subgroup G) (d : ∀ i, SolvableFFLocalBlock ρ (A i))
    (hgen : (⨆ i, (d i).factor) = offenderSubgroup ρ)
    (hcross : ∀ i j, i ≠ j →
      subspaceCommutator ρ ⊤ (d i).factor ≤ fixedSpace ρ (d j).factor) :
    Nonempty (SolvableFFFactors ρ) := by
  classical
  let E := fun i => (d i).factor
  let W := fun i => subspaceCommutator ρ ⊤ (E i)
  have hs : ∀ i, IsCompl (fixedSpace ρ (E i))
      (Representation.RegularCyclicNormalClosure.displacementSpan ρ (E i) ⊤) := by
    intro i
    rw [← moved_eq_displacement]
    exact (d i).complement.symm
  have hf : ∀ i j, i ≠ j → ∀ a ∈ E i,
      ∀ v ∈ Representation.RegularCyclicNormalClosure.displacementSpan ρ (E j) ⊤,
      ρ a v = v := by
    intro i j hij a ha v hv
    rw [← moved_eq_displacement] at hv
    exact hcross j i hij.symm hv ⟨a, ha⟩
  have hcomm : Pairwise fun i j => ∀ x y : G, x ∈ E i → y ∈ E j → Commute x y := by
    intro i j hij x y hx hy
    exact Representation.RegularCyclicNormalClosure.commute_of_cross_fixed hρ
      (hf i j hij) (hf j i hij.symm) hx hy
  have hgi : iSupIndep E :=
    Representation.RegularCyclicNormalClosure.factors_independent_of_cross_fixed hρ E hs hf
  have hwi : iSupIndep W := by
    simpa only [← moved_eq_displacement] using
      Representation.RegularCyclicNormalClosure.summands_independent_of_cross_fixed E hs hf
  let f := Subgroup.noncommPiCoprod hcomm
  have hfr : f.range = offenderSubgroup ρ := by
    rw [Subgroup.noncommPiCoprod_range]
    exact hgen
  let eG : ((i : Fin n) → E i) ≃* offenderSubgroup ρ :=
    (MonoidHom.ofInjective (Subgroup.injective_noncommPiCoprod_of_iSupIndep hgi)).trans
      (MulEquiv.subgroupCongr hfr)
  let s : ((i : Fin n) → W i) →ₗ[ZMod 2] V :=
    LinearMap.lsum (ZMod 2) (fun i => W i) (ZMod 2) (fun i => (W i).subtype)
  have hsapp (v : (i : Fin n) → W i) : s v = ∑ i, (v i : V) := by
    simp only [s, LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.subtype_apply]
  have hsinj : Function.Injective s := by
    intro v w hvw
    have he := (iSupIndep_iff_finsetSum_eq_imp_eq W).mp hwi Finset.univ
      (fun i => (v i : V)) (fun i => (w i : V))
      (fun i _ => ⟨(v i).property, (w i).property⟩)
      (by simpa only [hsapp] using hvw)
    funext i
    exact Subtype.ext (he i (Finset.mem_univ i))
  have hsr : s.range = subspaceCommutator ρ ⊤ (offenderSubgroup ρ) := by
    rw [← hgen, moved_iSup]
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [hsapp]
      exact Submodule.sum_mem _ fun i _ => (le_iSup W i) (v i).property
    · apply iSup_le
      intro i v hv
      refine ⟨Pi.single i ⟨v, hv⟩, ?_⟩
      exact LinearMap.lsum_piSingle (ZMod 2) (fun i => W i) (ZMod 2)
        (fun i => (W i).subtype) i ⟨v, hv⟩
  let eV : ((i : Fin n) → W i) ≃ₗ[ZMod 2]
      subspaceCommutator ρ ⊤ (offenderSubgroup ρ) :=
    (LinearEquiv.ofInjective s hsinj).trans (LinearEquiv.ofEq _ _ hsr)
  refine ⟨{
    count := n
    count_pos := hn
    factor := E
    groupProduct := eG
    groupProduct_single := ?_
    moduleSum := eV
    moduleSum_single := ?_
    factorModel := fun i => (d i).factorModel
    naturalEquiv := fun i => (d i).naturalEquiv
    naturalEquiv_action := fun i => (d i).naturalEquiv_action }⟩
  · intro i g
    exact Subgroup.noncommPiCoprod_mulSingle (hcomm := hcomm) i g
  · intro i v
    exact LinearMap.lsum_piSingle (ZMod 2) (fun i => W i) (ZMod 2)
      (fun i => (W i).subtype) i v

/-- Construct the positive finite internal product of the actual local blocks. -/
theorem factors_nonempty [Finite G] [FiniteDimensional (ZMod 2) V]
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 G = ⊥) (hρ : Function.Injective ρ)
    (hff : IsFFModule ρ) : Nonempty (SolvableFFFactors ρ) := by
  classical
  let ι := {E : Subgroup G // ∃ A, IsMinimalBestOffender ρ A ∧ ⁅pPrimeCore 2 G, A⁆ ⊔ A = E}
  let : Fintype ι := Fintype.ofFinite ι
  have hi : Nonempty ι := by
    obtain ⟨A, hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
    obtain ⟨B, hB, _⟩ := hA.exists_minimal ρ
    exact ⟨⟨⁅pPrimeCore 2 G, B⁆ ⊔ B, B, hB, rfl⟩⟩
  let : Nonempty ι := hi
  let e := (Fintype.equivFin ι).symm
  let A := fun i => (e i).property.choose
  have hA : ∀ i, IsMinimalBestOffender ρ (A i) := fun i => (e i).property.choose_spec.1
  let d : ∀ i, SolvableFFLocalBlock ρ (A i) := fun i => Classical.choice
    (BlockConstruction.localBlock_nonempty ρ hsolv hcore hρ
      (fun _ hB => minimalBestOffender_rank_one ρ hρ hsolv hcore hB)
      (fun _ hB => bestOffender_generatedBy_minimal ρ hρ hsolv hcore hB) (hA i))
  have hd (i) : (d i).factor = (e i).val :=
    (d i).factor_eq.trans (e i).property.choose_spec.2
  have hdinj : Function.Injective (fun i => (d i).factor) := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    simpa only [hd] using hij
  apply assemble ρ hρ Fintype.card_pos A d
  · apply le_antisymm (iSup_le fun i => (d i).factor_le)
    apply iSup_le
    intro B
    apply iSup_le
    rintro ⟨hB, _⟩
    rw [← bestOffender_generatedBy_minimal ρ hρ hsolv hcore hB]
    apply iSup_le
    intro C
    apply iSup_le
    rintro ⟨hC, _⟩
    obtain ⟨i, hi⟩ := e.surjective (⟨⁅pPrimeCore 2 G, C⁆ ⊔ C, C, hC, rfl⟩ : ι)
    apply le_trans ?_ (le_iSup (fun i => (d i).factor) i)
    rw [hd, hi]
    exact le_sup_right
  · intro i j hij
    exact localBlocks_cross_fixed ρ hsolv hcore hρ (hA i) (hA j) (d i) (d j)
      (fun he => hij (hdinj he))

end CFSG.Quasithin.ChapterB.Glauberman
