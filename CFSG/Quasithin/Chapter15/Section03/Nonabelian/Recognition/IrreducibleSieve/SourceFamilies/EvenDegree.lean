module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Reductions
public import CFSG.Quasithin.ChapterG.Section09.Basic
public import Theory.Representation.Suzuki.BinaryDegree
public import Theory.Representation.SU3.BinaryDegree
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms.Unconditional
public import Theory.SpecificGroups.Suzuki.TwoRank
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.NaturalCases.Symplectic
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank.SourceBound

/-!
# Degree exclusions for the actual binary source action

The original source actor bounds the degree by the automorphism two-rank of
its normal irreducible component. The unitary and Suzuki degree minima exceed
that bound. For nonbinary symplectic groups the remaining action is natural,
and transitivity on nonzero vectors contradicts the source quadratic form.
All actions use the literal projective quotient or derived matrix carrier.

Source: Aschbacher--Smith, G.9.3, printed pp.354--357, and the irreducible
branch of 15.3.58, printed p.1149.
-/

public section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

private theorem actor_rank_bound (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) {D : Type*} [Group D]
    (e : K ≃* D) {r : ℕ} (hr : primeRank 2 (MulAut D) ≤ r) : s + 1 ≤ r := by
  let : Finite D := Finite.of_surjective e e.surjective
  let : Representation.IsIrreducible (ρ.comp K.subtype) := hK.irreducible
  have hm := h.setup.rank_le_automorphisms (L := K) (by
    rw [Subgroup.normalizer_eq_top_iff.mpr hK.normal]
    exact le_top)
  rw [primeRank_equiv 2 (MulAut.congr e)] at hm
  exact hm.trans hr

private theorem cover_nontrivial (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) {D : Type*} [Group D]
    (π : D →* K) (hπ : Function.Surjective π) :
    ∃ g : D, ((ρ.comp K.subtype).comp π) g ≠ 1 := by
  by_contra! hzero
  have hbot : K = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    change x = 1
    obtain ⟨g, hg⟩ := hπ ⟨x, hx⟩
    apply h.faithful
    calc
      ρ x = ((ρ.comp K.subtype).comp π) g := by
        rw [MonoidHom.comp_apply, hg]
        rfl
      _ = 1 := hzero g
      _ = ρ 1 := (map_one ρ).symm
  exact h.componentJoin_noncentral hK (by rw [hbot, Subgroup.commutator_bot_left])

/-- The faithful binary degree minimum and actual automorphism rank exclude
all simple Suzuki components under the original source data. -/
theorem SourceData.not_suzuki_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) {m : ℕ} (hm : 1 ≤ m)
    (model : Nonempty (K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) : False := by
  obtain ⟨e⟩ := model
  have hr := actor_rank_bound h hK e (BenderSuzuki.MatrixGroups.suzuki_automorphism_two_rank m hm)
  have hd := Representation.Suzuki.finrank_ge hm
    ((ρ.comp K.subtype).comp e.symm.toMonoidHom)
    ((h.faithful.comp K.subtype_injective).comp e.symm.injective)
  have hu := h.dimension
  omega

/-- For the actual projective unitary component, inflate through the genuine
special-to-projective map and apply the nontrivial binary degree minimum. -/
theorem SourceData.not_unitaryThree_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) {n : ℕ} (hn : 2 ≤ n)
    (model : ClassicalGroup.IsPSU K 3 (2 ^ n)) : False := by
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := model
  have hr := actor_rank_bound h hK e
    (BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.automorphism_two_rank_le J hn hF hconj)
  let π := e.symm.toMonoidHom.comp J.specialToProjective
  have hπ : Function.Surjective π := e.symm.surjective.comp J.specialToProjective_surjective
  have hd := Representation.SU3.BinaryDegree.finrank_ge J hn hF hconj
    ((ρ.comp K.subtype).comp π) (cover_nontrivial h hK π hπ)
  have hu := h.dimension
  omega

open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic
attribute [local instance] ZMod.algebra

private theorem not_symplectic_of_rank (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) {F : Type*} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : K ≃* commutator (Matrix.symplecticGroup (Fin 2) F))
    (hr : primeRank 2 (MulAut (commutator (Matrix.symplecticGroup (Fin 2) F))) ≤ 3*n) :
    False := by
  have hm := actor_rank_bound h hK e hr
  have hsmall : Module.finrank (ZMod 2) W ≤ 6*n+2 := by
    have := h.dimension
    omega
  let σ := (ρ.comp K.subtype).comp e.symm.toMonoidHom
  let : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom
      e.symm.surjective (ρ.comp K.subtype)).mpr hK.irreducible
  have hσ : Function.Injective σ :=
    (h.faithful.comp K.subtype_injective).comp e.symm.injective
  have hnat := SymplecticFourRecognition.quasiequivalent_of_comp_equiv e
    (SymplecticFourRecognition.Nonbinary.small_quasiequivalent hn hF hσ hsmall)
  exact h.not_natural_symplecticFour K hF
    (SymplecticFourRecognition.finrank_of_quasiequivalent hF hnat) hnat

/-- The literal projective symplectic model is the derived matrix group in
nonbinary characteristic two, so its actual source action is excluded. -/
theorem SourceData.not_symplecticFour_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) {n : ℕ} (hn : 2 ≤ n)
    (model : ClassicalGroup.IsPSp K 2 (2 ^ n)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := model
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let d : K ≃* commutator (Matrix.symplecticGroup (Fin 2) F) :=
    (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm).trans
      (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn).symm
  exact not_symplectic_of_rank h hK hn hF d
    (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derived_automorphism_rank_le hF hn)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
