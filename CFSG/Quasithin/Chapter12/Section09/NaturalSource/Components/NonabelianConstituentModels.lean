module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianConstituentQuotient
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedProperFaithful
public import CFSG.Quasithin.ChapterG.Section11.NaturalEightExclusion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.FieldFour
public import Theory.Representation.BinaryPermutation.FiveDoubleNormalizer
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Theory.Alternating.IndexEightSubgroups
public import Theory.Representation.AlternatingSevenConjugatePair.Model.OuterDual

/-!
# Excluding the original marked constituent

The literal constituent action quotient is faithful and self-dual, fixes the
original marked line, and has degree at most its actor rank plus two. The
G.9 carrier bounds leave only A₅, A₆, A₇ and A₈. Self-duality excludes A₇;
the actual two-copy action excludes A₈; the original seven-section excludes
A₆. Both remaining A₅ actions have doubled normalizers of order prime to
seven, contradicting that same original seven-section.

The carrier sieve reuses the mathematical argument of
Chapter14/Section04/CaseOneLarge/FixedLineModels, specialized here to the
original degree-four or degree-five flag without its separate ambient inputs.
Source: Aschbacher--Smith G.11.7--8 and 12.9.4, printed pp.366--369,859--860.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
local instance : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2
namespace FixedLineModels
open ChapterG.Section09
namespace Seven
open AlternatingSevenConjugatePair.Model
private def linearEquivToSL (e : Four ≃ₗ[ZMod 2] Four) : SL(4, ZMod 2) :=
  ⟨LinearMap.toMatrix' e.toLinearMap, by
    rw [LinearMap.det_toMatrix']
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ e.isUnit_det'.ne_zero⟩

private theorem linearEquivToSL_apply (e : Four ≃ₗ[ZMod 2] Four) :
    Matrix.SpecialLinearGroup.toLin' (linearEquivToSL e) = e := by
  apply LinearEquiv.toLinearMap_injective
  exact Matrix.toLin'_toMatrix' e.toLinearMap

private def linearEquivToSLHom : (Four ≃ₗ[ZMod 2] Four) →* SL(4, ZMod 2) where
  toFun := linearEquivToSL
  map_one' := by
    apply Matrix.SpecialLinearGroup.toLin'_injective
    rw [linearEquivToSL_apply, map_one]
  map_mul' g h := by
    apply Matrix.SpecialLinearGroup.toLin'_injective
    rw [map_mul, linearEquivToSL_apply, linearEquivToSL_apply, linearEquivToSL_apply]

private def comparison : alternatingGroup (Fin 8) ≃* SL(4, ZMod 2) :=
  Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
    Atlas.Order20160A8.sl4TwoEquivPSL.symm

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private def coordinateAction (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) : Representation (ZMod 2) G Four :=
  b.conjRingEquiv.toMonoidHom.comp ρ

private def linearImage (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) : G →* SL(4, ZMod 2) :=
  linearEquivToSLHom.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Four).toMonoidHom.comp
      (coordinateAction ρ b).asGroupHom)

private theorem linearImage_apply (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) (g : G) (v : V) :
    Matrix.SpecialLinearGroup.toLin' (linearImage ρ b g) (b v) = b (ρ g v) := by
  rw [show linearImage ρ b g = linearEquivToSL
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Four
      ((coordinateAction ρ b).asGroupHom g)) from rfl, linearEquivToSL_apply]
  change b (ρ g (b.symm (b v))) = _
  rw [b.symm_apply_apply]

private theorem linearImage_injective (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) (hf : Function.Injective ρ) :
    Function.Injective (linearImage ρ b) := by
  intro g h he
  apply hf
  ext v
  apply b.injective
  rw [← linearImage_apply ρ b g, ← linearImage_apply ρ b h, he]

private def permutationImage (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) : G →* alternatingGroup (Fin 8) :=
  comparison.symm.toMonoidHom.comp (linearImage ρ b)

private theorem permutationImage_injective (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) (hf : Function.Injective ρ) :
    Function.Injective (permutationImage ρ b) :=
  comparison.symm.injective.comp (linearImage_injective ρ b hf)



private theorem four_coordinates [Finite G] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hfρ : Function.Injective ρ)
    (eG : G ≃* alternatingGroup (Fin 7)) (hd : finrank (ZMod 2) V = 4) :
    Quasiequivalent ρ natural := by
  classical
  obtain ⟨b⟩ : Nonempty (V ≃ₗ[ZMod 2] Four) :=
    FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (hd.trans four_dimension.symm)
  let f := permutationImage ρ b
  have hf : Function.Injective f := permutationImage_injective ρ b hfρ
  let H := f.range
  have hcard : Nat.card H = 2520 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      Nat.card_congr eG.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hA : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hindex : H.index = 8 := by
    have hh := H.card_mul_index
    rw [hcard, hA] at hh
    omega
  let J := alternatingEmbedding.range
  have hJcard : Nat.card J = 2520 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective alternatingEmbedding_injective).toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hJindex : J.index = 8 := by
    have hh := J.card_mul_index
    rw [hJcard, hA] at hh
    omega
  -- Conjugacy takes place inside A₈, so it lifts to a linear coordinate change.
  obtain ⟨c, hc⟩ := GroupTheory.AlternatingIndexEight.index_eight_conjugate
    H J hindex hJindex
  let q := (MulAut.conj c).toMonoidHom.comp f
  have hq : Function.Injective q := (MulAut.conj c).injective.comp
    hf
  have hqr : q.range = alternatingEmbedding.range := by
    rw [MonoidHom.range_comp]
    exact hc
  let eGroup : G ≃* alternatingGroup (Fin 7) :=
    (MonoidHom.ofInjective hq).trans ((MulEquiv.subgroupCongr hqr).trans
      (MonoidHom.ofInjective alternatingEmbedding_injective).symm)
  have he (l : G) : alternatingEmbedding (eGroup l) = q l := by
    exact congrArg Subtype.val
      ((MonoidHom.ofInjective alternatingEmbedding_injective).apply_symm_apply
        ((MulEquiv.subgroupCongr hqr) ((MonoidHom.ofInjective hq) l)))
  let t : Four ≃ₗ[ZMod 2] Four := Matrix.SpecialLinearGroup.toLin' (comparison c)
  refine ⟨eGroup, b.trans t, fun l v => ?_⟩
  have hlin : linearEmbedding (eGroup l) =
      comparison c * linearImage ρ b l * (comparison c)⁻¹ := by
    change comparison (alternatingEmbedding (eGroup l)) = _
    rw [he]
    change comparison (c * (comparison.symm (linearImage ρ b l)) * c⁻¹) = _
    rw [map_mul, map_mul, map_inv, comparison.apply_symm_apply]
  change t (b (ρ l v)) =
    Matrix.SpecialLinearGroup.toLin' (linearEmbedding (eGroup l)) (t (b v))
  rw [hlin, map_mul, map_mul, map_inv]
  change t (b (ρ l v)) = t
    (Matrix.SpecialLinearGroup.toLin' (linearImage ρ b l) (t.symm (t (b v))))
  rw [t.symm_apply_apply, linearImage_apply]


private theorem no_selfDual [Finite G] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (eG : G ≃* alternatingGroup (Fin 7)) (hd : finrank (ZMod 2) V = 4)
    (hs : Nonempty (ρ.Equiv ρ.dual)) : False := by
  obtain ⟨e,c,hc⟩ := four_coordinates ρ hf eG hd
  obtain ⟨d⟩ := hs
  let f : natural.Equiv natural.dual := .mk
    ((c.symm.trans d.toLinearEquiv).trans c.symm.dualMap) (by
      intro a
      apply LinearMap.ext
      intro u
      apply LinearMap.ext
      intro w
      have hi (b : alternatingGroup (Fin 7)) (z : Four) :
          c.symm (natural b z) = ρ (e.symm b) (c.symm z) := by
        apply c.injective
        rw [c.apply_symm_apply,hc,e.apply_symm_apply,c.apply_symm_apply]
      change d (c.symm (natural a u)) (c.symm w) =
        d (c.symm u) (c.symm (natural a⁻¹ w))
      rw [hi,hi]
      have hh := congrArg (fun q : Module.Dual (ZMod 2) V => q (c.symm w))
        (Representation.IntertwiningMap.isIntertwining ρ ρ.dual
          d.toIntertwiningMap (e.symm a) (c.symm u))
      simpa only [Representation.Equiv.coe_toIntertwiningMap,
        Representation.dual_apply, Module.Dual.transpose_apply,
        LinearMap.comp_apply, e.symm.map_inv] using hh)
  exact natural_not_equiv_outerNatural ⟨f.trans outerDualEquiv.symm⟩
end Seven
/-- Actual carrier alternatives for the sharp fixed-line constituent. -/
private def SmallCarrier (D : Type*) [Group D] : Prop :=
  Nonempty (D ≃* alternatingGroup (Fin 5)) ∨
  Nonempty (D ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (D ≃* alternatingGroup (Fin 7)) ∨
  Nonempty (D ≃* alternatingGroup (Fin 8))
private theorem SmallCarrier.of_equiv {D E : Type*} [Group D] [Group E]
    (e : D ≃* E) (h : SmallCarrier E) : SmallCarrier D := by
  rcases h with h | h | h | h
  · exact Or.inl (h.map (e.trans ·))
  · exact Or.inr (Or.inl (h.map (e.trans ·)))
  · exact Or.inr (Or.inr (Or.inl (h.map (e.trans ·))))
  · exact Or.inr (Or.inr (Or.inr (h.map (e.trans ·))))

open Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open ChapterG.Section09 ChapterG.Section09.DefiningCharacteristic
open Chapter1.Section02.LocalModels
universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {A L : Subgroup D} {m : ℕ}
  (h : ComponentHypothesis KnownSimple.IsKnownSimple ρ A L L m)
  (hd : finrank (ZMod 2) V ≤ m+2)
  (hs : Nonempty (Representation.Equiv (ρ.comp L.subtype) (Representation.dual (ρ.comp L.subtype))))
  (v : V) (hv : v ≠ 0) (hfix : fixedSpace ρ A = Submodule.span (ZMod 2) {v})
include h hd
omit hd in
private theorem actor_rank : m ≤ primeRank 2 (MulAut L) := by
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  exact h.toSetup.rank_le_automorphisms (by
    rw [normalizer_eq_top_iff.mpr h.normal_H]; exact le_top)

include hs in
private theorem not_linear_three_cover {k : Type*} [Field k] [Finite k] [CharP k 2]
    (π : SL(3,k) →* L) (hπ : Function.Surjective π) (hz : π.ker ≤ center SL(3,k))
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card k = 2^n) : False :=
  MarkedLinearThree.not_two_copy_linear_three h hs (by omega) π hπ hz n hn hcard

include hs in
private theorem not_linear_three {n : ℕ} (hn : 0 < n)
    (model : ClassicalGroup.IsPSL L 3 (2^n) ∨ IsSL L 3 (2^n)) : False := by
  rcases model with model | model
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
    let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    exact not_linear_three_cover h hd hs (e.symm.toMonoidHom.comp (Matrix.PSL3.projection k))
      (e.symm.surjective.comp (Matrix.PSL3.projection_surjective k))
      (by rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective, Matrix.PSL3.projection_ker]) hn hcard
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
    let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    exact not_linear_three_cover h hd hs e.symm.toMonoidHom e.symm.surjective
      (by rw [e.symm.toMonoidHom.ker_eq_bot_iff.mpr e.symm.injective]; exact bot_le) hn hcard

private theorem rank_one_small {n : ℕ} (hn : 2 ≤ n)
    (model : ClassicalGroup.IsPSL L 2 (2^n)) : SmallCarrier L := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  have hm := rank_one_module_alternatives h
    (e.trans (Theory.PSL2.sl2QuotientEquiv k).symm) n hn hcard
  have hactor := hm.1
  have hn2 : n = 2 := by
    rcases hm.2 with ⟨hdeg,_,_⟩ | ⟨a,ha,hna,hdeg,_⟩ | ⟨hna,hdeg,_⟩ <;> omega
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (show Nat.card k = 4 by simpa [hn2] using hcard)
  exact Or.inl ⟨e.trans f⟩

include v hv hfix in
private theorem not_symplectic {n : ℕ} (hn : 2 ≤ n)
    (model : ClassicalGroup.IsPSp L 2 (2^n)) : False := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  let E := (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm).trans
    (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hcard hn).symm
  let := ZMod.algebra k 2
  let σ := (ρ.comp L.subtype).comp E.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff E.symm.toMonoidHom E.symm.surjective _).mpr h.irreducible
  have hf : Function.Injective σ := h.faithful.comp (L.subtype_injective.comp E.symm.injective)
  have hm := actor_rank h
  rw [primeRank_equiv 2 (MulAut.congr E)] at hm
  have hr := Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derived_automorphism_rank_le hcard hn
  have hdeg := SymplecticFourRecognition.Nonbinary.small_finrank hn hcard hf (by omega)
  change finrank (ZMod 2) V = 4*n at hdeg
  have he : finrank (ZMod 2) V = m+2 := by omega
  exact SymplecticFourRecognition.FixedLine.not_natural_sharp_fixed_line h he E hn hcard v hv hfix

private theorem not_g2 {n : ℕ} (hn : 2 ≤ n)
    (model : ClassificationModels.IsG2At L (2^n)) : False := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  exact G2Recognition.not_nonbinary_of_sharp_degree h (by omega)
    (e.trans (Atlas.G2.DerivedEvenOrder.derivedEquivModel (by omega) hcard).symm) hn hcard

include hs in
private theorem binary_linear {n : ℕ} (hn : n=4 ∨ n=5)
    (model : ClassicalGroup.IsPSL L n 2) : SmallCarrier L := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : Fintype k := Fintype.ofFinite k
  let a : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard)
  rcases hn with rfl | rfl
  · exact Or.inr (Or.inr (Or.inr ⟨(e.trans (Atlas.fieldEquivPSL 4 a)).trans
      Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm⟩))
  · exact (BinaryLinearRecognition.not_five_of_selfDual_sharp_degree h hd
      hs (e.trans (Atlas.fieldEquivPSL 5 a))).elim

private theorem native_g2 (e : L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    SmallCarrier L := by
  have hm := actor_rank h
  rw [primeRank_equiv 2 (MulAut.congr e)] at hm
  have hb := Atlas.G2.binary_derived_automorphism_two_rank_le_three
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h.irreducible
  obtain ⟨Ω,hΩ,τ,o,H,hH,hstab,htrans,hfil⟩ :=
    G2DerivedPermutationFiltration.exists_permutation_filtration
  let := hΩ
  have hs := BinaryPermutation.finrank_mem_of_factorDegreeFiltration
    τ o H hH hstab htrans hfil σ
  change finrank (ZMod 2) V = 1 ∨ finrank (ZMod 2) V = 6 ∨ 8 < finrank (ZMod 2) V at hs
  have hdim : finrank (ZMod 2) V ≤ 2 := by omega
  let : IsQuasisimple L := h.component.2
  let : Nontrivial L := (nontrivial_iff_ne_bot L).mpr
    (fun he => h.noncentral (by rw [he]; simp))
  have hf : Function.Injective (ρ.comp L.subtype) := h.faithful.comp L.subtype_injective
  obtain ⟨a,ha⟩ := exists_ne (1 : L)
  exact (ha (hf ((Representation.BinaryOffender.representation_eq_one_of_isPerfect_of_finrank_le_two
    (ρ.comp L.subtype) hdim a).trans (ρ.comp L.subtype).map_one.symm))).elim

omit h hd [Finite D] in
private theorem binary_symplectic (e : L ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) :
    SmallCarrier L :=
  Or.inr (Or.inl ⟨e.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp))⟩)

include hs in
private theorem odd_two {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (model : ClassicalGroup.IsPSL L 2 (p^e)) : SmallCarrier L := by
  let : IsQuasisimple L := h.component.2
  rcases ChapterG.Section07.OddCharacteristic.psl2_identification_of_degree_le_automorphism_rank
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) hp ho he model
    h.single_component_degree_bound with hb | ht | he
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := hb
    obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hcard
    exact Or.inl ⟨e.trans a⟩
  · exact (not_linear_three h hd hs (n := 1) (by decide) (Or.inl (by simpa using ht))).elim
  · exact binary_symplectic he.some

private theorem odd_three {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (model : ChapterG.Section07.OddCharacteristic.IsLinearUnitaryThree L p) :
    SmallCarrier L := by
  let : IsQuasisimple L := h.component.2
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  obtain ⟨e,_⟩ := ChapterG.Section07.OddCharacteristic.linear_unitary_three_of_degree_le_automorphism_rank
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) hp ho model h.single_component_degree_bound
  exact native_g2 h hd e.some

omit h hd [Finite D] in
private theorem alternating {n : ℕ} (hn : 5≤n ∧ n≤8)
    (e : L ≃* alternatingGroup (Fin n)) : SmallCarrier L := by
  obtain ⟨hnl,hnu⟩ := hn
  interval_cases n
  · exact Or.inl ⟨e⟩
  · exact Or.inr (Or.inl ⟨e⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨e⟩))

private theorem rank_one (model : ClassificationModels.IsBenderModel L) : SmallCarrier L := by
  cases model with
  | linear n hn hm => exact rank_one_small h hd hn hm
  | unitary n hn hm =>
    obtain ⟨k,_,_,J,hcard,hconj,e⟩ := hm
    exact (TwistedExclusions.not_unitary_three_positive_exponent h J (by omega) hcard hconj (Or.inr e)).elim
  | suzuki k hk e => exact (h.not_suzuki hk e.some).elim

include hs v hv hfix in
private theorem rank_two (model : RankTwoTheoremC L) : SmallCarrier L := by
  cases model with
  | linear n hn hm => exact (not_linear_three h hd hs hn (Or.inl hm)).elim
  | symplectic n hn hm => exact (not_symplectic h hd v hv hfix hn hm).elim
  | g2 n hn hm => exact (not_g2 h hd hn hm).elim
  | triality n hn hm => exact (TwistedExclusions.not_triality_positive_exponent h hn hm).elim
  | ree k hk hm =>
    obtain ⟨d,e⟩ := hm
    exact (TwistedExclusions.not_ree_of_local_block h hk d e.some).elim
  | symplectic_derived e =>
    exact Or.inr (Or.inl ⟨e.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩)
  | g2_derived e => exact native_g2 h hd e.some
  | tits e => exact (TwistedExclusions.not_tits_of_source_component h e.some).elim

omit h hd in
private theorem simple_center_eq_bot {S : Type*} [Group S] [IsSimpleGroup S] [Group.IsPerfect S] :
    center S = ⊥ := by
  rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp ht)).elim

include hs v hv hfix in
private theorem simple_models (hsimple : IsSimpleGroup L) (model : TheoremCModel L) :
    SmallCarrier L := by
  let : IsSimpleGroup L := hsimple
  let : IsQuasisimple L := h.component.2
  let q : L ⧸ center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq simple_center_eq_bot).trans QuotientGroup.quotientBot
  have hsharp : finrank (ZMod 2) V ≤ m+2 := by omega
  cases model with
  | alternating n hn e => exact alternating hn e.some
  | linear_odd p e hp ho he _ hm => exact odd_two h hd hs hp ho (by rcases he with rfl | rfl <;> decide) hm
  | three_odd p hp ho unitary hm =>
    apply odd_three h hd hp ho
    cases unitary with
    | false => exact Or.inl hm
    | true => exact Or.inr (Or.inr (Or.inl hm))
  | rank_one hm => exact rank_one h hd hm
  | rank_two hm => exact rank_two h hd hs v hv hfix hm
  | binary_linear n hn hm => exact binary_linear h hd hs hn hm
  | sporadic name hne e =>
    cases name with
    | m11 => exact (h.not_m11_central_quotient (q.trans e.some)).elim
    | m12 => exact (h.not_m12_of_sharp_degree hsharp e.some).elim
    | m22 => exact (h.not_m22_of_sharp_degree hsharp e.some).elim
    | m23 => exact (h.not_m23_of_sharp_degree hsharp e.some).elim
    | m24 => exact (h.not_m24_of_sharp_degree hsharp e.some).elim
    | j2 => exact (h.not_janko_two_of_sharp_degree hsharp e.some).elim
    | j3 => exact (hne rfl).elim
    | j4 => exact (h.not_janko_four e.some).elim
    | hs => exact (h.not_higman_sims e.some).elim
    | he => exact (h.not_held e.some).elim
    | ru => exact (h.not_rudvalis e.some).elim
  | janko_one e => exact (h.not_j1_central_quotient (q.trans e.some)).elim

include hs in
private theorem cover_models (model : ThreeCoverModel L) : SmallCarrier L := by
  have hsharp : finrank (ZMod 2) V ≤ m+2 := by omega
  cases model with
  | classical unitary q hq hm =>
    cases unitary with
    | false =>
      change IsSL L 3 q at hm
      rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
      · exact (not_linear_three h hd hs hn (Or.inr hm)).elim
      · exact odd_three h hd hp ho (Or.inr (Or.inl hm))
    | true =>
      change IsSU L 3 q at hm
      rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
      · obtain ⟨k,_,_,J,hcard,hconj,e⟩ := hm
        exact (TwistedExclusions.not_unitary_three_positive_exponent h J hn hcard hconj (Or.inl e)).elim
      · exact odd_three h hd hp ho (Or.inr (Or.inr (Or.inr hm)))
  | alternating_six hm => exact (h.not_triple_alternating_six_of_sharp_degree hsharp hm.2.2.some
      ((Nat.card_congr hm.2.1.some.toEquiv).trans (by simp))).elim
  | alternating_seven hm => exact (h.not_triple_alternating_seven hm.2.2.some
      ((Nat.card_congr hm.2.1.some.toEquiv).trans (by simp))).elim
  | mathieu hm => exact (h.not_m22_central_quotient_of_sharp_degree hsharp hm.2.2.some).elim

include hs v hv hfix in
/-- A self-dual single component at the proper-constituent degree bound has
only permitted native image carriers. -/
private theorem smallCarrier_of_selfDual_sharp_fixed_line : SmallCarrier L := by
  rcases h.single_component_models with ⟨hi,hm⟩ | ⟨_,hm⟩
  · exact simple_models h hd hs v hv hfix hi hm
  · exact cover_models h hd hs hm

private theorem small_alternating_degree {E : Type*} [Group E]
    (e : E ≃* L)
    (hc : Nonempty (E ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (E ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (E ≃* alternatingGroup (Fin 7))) : finrank (ZMod 2) V = 4 := by
  have hf : Function.Injective (ρ.comp L.subtype) := h.faithful.comp L.subtype_injective
  have hm := actor_rank h
  rcases hc with h5 | h6 | h7
  · obtain ⟨f⟩ := h5
    let a := e.symm.trans f
    rw [primeRank_equiv 2 (MulAut.congr a)] at hm
    have hr := Theory.SpecificGroups.Alternating.FiveExtensionAction.automorphism_primeRank_two_le
    have hdiv : 5 ∣ Nat.card L := by
      rw [Nat.card_congr a.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hlo := Representation.BinaryPrimeDegree.orderOf_le_finrank (ρ.comp L.subtype)
      hf (by decide : Nat.Prime 5) (by decide) hdiv
    rw [Representation.BinaryPrimeDegree.orderOf_two_mod_five] at hlo
    omega
  · obtain ⟨f⟩ := h6
    let a := e.symm.trans f
    rw [primeRank_equiv 2 (MulAut.congr a)] at hm
    have hr := AlternatingSixCover.alternating_six_automorphism_two_rank
    let σ := (ρ.comp L.subtype).comp a.symm.toMonoidHom
    let : IsIrreducible σ :=
      (irreducible_comp_surjective_iff a.symm.toMonoidHom a.symm.surjective _).mpr h.irreducible
    have hs := BinaryAlternatingSix.alternating_degrees σ
    have hdiv : 5 ∣ Nat.card L := by
      rw [Nat.card_congr a.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hlo := Representation.BinaryPrimeDegree.orderOf_le_finrank (ρ.comp L.subtype)
      hf (by decide : Nat.Prime 5) (by decide) hdiv
    rw [Representation.BinaryPrimeDegree.orderOf_two_mod_five] at hlo
    rcases hs with hs | hs | hs <;> omega
  · obtain ⟨f⟩ := h7
    let a := e.symm.trans f
    rw [primeRank_equiv 2 (MulAut.congr a)] at hm
    have hr := ChapterG.Section07.AlternatingSevenCover.alternating_seven_automorphism_two_rank
    let σ := (ρ.comp L.subtype).comp a.symm.toMonoidHom
    let : IsIrreducible σ :=
      (irreducible_comp_surjective_iff a.symm.toMonoidHom a.symm.surjective _).mpr h.irreducible
    have hs := ChapterK.Alternating.sevenSmallDegreeSpectrum σ
      (hf.comp a.symm.injective) inferInstance (by omega)
    rcases hs with hs | hs | hs <;> omega

end FixedLineModels
private theorem fixed_doubled_model
    {D E U V W : Type*} [Group D] [Group E]
    [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D U) (R : Representation (ZMod 2) D V)
    (σ : Representation (ZMod 2) E W)
    (d : ρ.Equiv (R.prod R)) (hm : ChapterG.Section09.Quasiequivalent R σ) :
    ChapterG.Section09.Quasiequivalent ρ (σ.prod σ) := by
  obtain ⟨e,c,hc⟩ := hm
  refine ⟨e,d.toLinearEquiv.trans (c.prodCongr c),?_⟩
  intro a w
  have hh := LinearMap.congr_fun (d.isIntertwining' a) w
  change d (ρ a w) = (R a (d w).1,R a (d w).2) at hh
  change (c (d (ρ a w)).1,c (d (ρ a w)).2) = _
  rw [hh,hc,hc]
  rfl



namespace FixedLineConstituent
open Chapter14.Section04.CaseOneLarge.FixedLineSemilinear
open ChapterG.Section09
private theorem not_seven_of_natural_double
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (H : Subgroup D) [H.Normal] (eH : H ≃* alternatingGroup (Fin 5))
    (hm : Quasiequivalent (ρ.comp H.subtype)
      ((SL2.BinarySmall.natural (K := Field)).prod (SL2.BinarySmall.natural (K := Field)))) :
    ¬ 7 ∣ Nat.card D := by
  obtain ⟨a⟩ := coordinates_of_double ρ hf H hm
  let f : D →* MulAut H := MulAut.conjNormal
  have hC : ¬ 7 ∣ Nat.card f.ker := by
    rw [MulAut.conjNormal_ker_eq_centralizer]
    intro hc
    have hh := hc.trans (card_dvd_of_injective a.centralizerLinear a.centralizerLinear_injective)
    have hfield : Fintype.card Field = 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card 2 2 (by decide)
    rw [Matrix.card_GL_field,hfield] at hh
    norm_num [Fin.prod_univ_succ] at hh
  have hA : ¬ 7 ∣ Nat.card f.range := by
    let e : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
      MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
        5 (by decide) (by decide))
    intro ha
    have hh := ha.trans (card_subgroup_dvd_card f.range)
    rw [Nat.card_congr (MulAut.congr eH).toEquiv,← Nat.card_congr e.toEquiv] at hh
    norm_num [Nat.card_perm,Nat.card_fin,Fintype.card_perm,Nat.factorial] at hh
  intro hd
  rw [card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hd
  exact (Nat.Prime.dvd_mul (by decide : Nat.Prime 7)).mp hd |>.elim hA hC

private theorem not_seven_of_permutation_double
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hfρ : Function.Injective ρ)
    (H : Subgroup D) [H.Normal]
    (hm : Quasiequivalent (ρ.comp H.subtype)
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin 5)).prod
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 5)))) :
    ¬ 7 ∣ Nat.card D := by
  obtain ⟨e,f,hf⟩ := hm
  let c := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  have hc (a : alternatingGroup (Fin 5)) (w : BinaryPermutation.natural (Fin 5)) :
      c.symm (BinaryPermutation.alternatingNaturalRepresentation (Fin 5) a w) =
        BinaryPermutation.alternatingCoreRepresentation (Fin 5) a (c.symm w) := by
    apply c.injective
    rw [c.apply_symm_apply]
    exact (BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide)
      a (c.symm w)).trans (by rw [c.apply_symm_apply]; rfl) |>.symm
  let f' := f.trans (c.symm.prodCongr c.symm)
  have hf' (h : H) (w : W) : f' (ρ h w) =
      (BinaryPermutation.alternatingCoreRepresentation (Fin 5) (e h) (f' w).1,
       BinaryPermutation.alternatingCoreRepresentation (Fin 5) (e h) (f' w).2) := by
    have hh := hf h w
    change f (ρ h w) =
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 5) (e h) (f w).1,
       BinaryPermutation.alternatingNaturalRepresentation (Fin 5) (e h) (f w).2) at hh
    change (c.symm (f (ρ h w)).1,c.symm (f (ρ h w)).2) = _
    rw [hh,hc,hc]
    rfl
  obtain ⟨j,_,hj,_,_⟩ :=
    BinaryPermutation.FiveTensorNormalizer.exists_tensor_embedding_of_double ρ hfρ H e f' hf'
  intro hseven
  have hd := hseven.trans (card_dvd_of_injective j hj)
  norm_num [Nat.card_prod,Nat.card_perm,Nat.card_fin,Fintype.card_perm,Nat.factorial] at hd
end FixedLineConstituent
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
open ChapterG.Section11
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The actual doubled A₈ constituent contradicts the original actor bound. -/
theorem nonabelian_marked_eight_constituent_impossible
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hg10 : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hS : NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)))
    {J : Subgroup F.TerminalHdot} (hJ : IsComponent F.TerminalHdot J)
    (hm : ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit J ⊤)
      (F.terminalDot (F.X g)) I)
    (hdata : FixedLineConstituent.MarkedData F.terminalRepresentation B v
      (F.terminalDot (F.X g)) J I hI)
    (e : componentOrbit J ⊤ ≃* alternatingGroup (Fin 8)) : False := by
  have hd := nonabelian_marked_constituent_double modules h hn preferred earlier four
    F hne g hgP hgH hg10 hS hJ hm hI hdata
  have hs := nonabelian_marked_constituent_single modules h hn preferred earlier four
    F hne g hgP hgH hg10 hS hJ hm hI hdata
  obtain ⟨hv,_,_,hfH,_,_,_,_,hXI,_,_,⟨eH,_⟩,_,_,_⟩ := hdata
  obtain ⟨_,_,_,_,_,h9,_,hself,_⟩ := hs
  let H := componentOrbit J ⊤
  let : H.Normal := componentOrbit_top_normal J
  let X := F.terminalDot (F.X g)
  have hmodel := ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.four_alternating_natural_of_selfDual
    h9 hself ((eH.symm.trans e).trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two)
  have hmR := MarkedAction.quasiequivalent_of_image F.terminalRepresentation H X I hI.invariant hXI
    hfH (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) hmodel
  exact ChapterG.Section11.not_doubled_natural_eight hg10 ⟨nonabelian_sqtkCover h F⟩ H
    (fixed_doubled_model _ _ _ hd.2.1.some hmR)

/-- Only the A₅ carrier remains for a proper constituent through the original
marked point. All other sharp-degree carriers are discharged on the same flag. -/
theorem nonabelian_marked_constituent_five
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hg10 : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hS : NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)))
    {J : Subgroup F.TerminalHdot} (hJ : IsComponent F.TerminalHdot J)
    (hm : ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit J ⊤)
      (F.terminalDot (F.X g)) I)
    (hdata : FixedLineConstituent.MarkedData F.terminalRepresentation B v
      (F.terminalDot (F.X g)) J I hI)
    : Nonempty (componentOrbit J ⊤ ≃* alternatingGroup (Fin 5)) ∧
      finrank (ZMod 2) I = 4 := by
  have saved := hdata
  have hs := nonabelian_marked_constituent_single modules h hn preferred earlier four
    F hne g hgP hgH hg10 hS hJ hm hI hdata
  obtain ⟨hv,_,_,hfH,hdual,_,_,_,hXI,_,_,⟨eH,_⟩,_,_,_⟩ := hdata
  obtain ⟨_,_,_,_,_,h9,hd,hself,hfix⟩ := hs
  have hc := FixedLineModels.smallCarrier_of_selfDual_sharp_fixed_line h9 hd hself
    ⟨v,hv⟩ (fun he => hg10.point_ne_zero (congrArg Subtype.val he)) hfix
  have hc' := FixedLineModels.SmallCarrier.of_equiv eH hc
  rcases hc' with h5 | h6 | h7 | h8
  · exact ⟨h5,FixedLineModels.small_alternating_degree h9 hd eH (Or.inl h5)⟩
  · exact (nonabelian_marked_six_constituent_impossible modules h hn preferred earlier four
      F hne g hgP hgH hg10 hS hJ hm hI
      saved h6.some).elim
  · have hd4 := FixedLineModels.small_alternating_degree h9 hd eH (Or.inr (Or.inr h7))
    exact (FixedLineModels.Seven.no_selfDual
      (invariantSubspace F.terminalRepresentation (componentOrbit J ⊤) I hI.invariant).toRepresentation
      hfH h7.some hd4 hdual).elim
  · exact (nonabelian_marked_eight_constituent_impossible modules h hn preferred earlier four
      F hne g hgP hgH hg10 hS hJ hm hI
      saved h8.some).elim


/-- No constituent through the original marked point survives. The A₅
natural and deleted-permutation doubles have normalizers of order prime
to seven, contradicting the original point residual's seven-section. -/
theorem nonabelian_marked_constituent_impossible
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hg10 : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hS : NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)))
    {J : Subgroup F.TerminalHdot} (hJ : IsComponent F.TerminalHdot J)
    (hm : ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit J ⊤)
      (F.terminalDot (F.X g)) I)
    (hdata : FixedLineConstituent.MarkedData F.terminalRepresentation B v
      (F.terminalDot (F.X g)) J I hI)
    : False := by
  obtain ⟨⟨e⟩,_⟩ := nonabelian_marked_constituent_five modules h hn preferred earlier four
    F hne g hgP hgH hg10 hS hJ hm hI hdata
  have hd := nonabelian_marked_constituent_double modules h hn preferred earlier four
    F hne g hgP hgH hg10 hS hJ hm hI hdata
  obtain ⟨_,_,_,hf,_,_⟩ := hdata
  let H := componentOrbit J ⊤
  let : H.Normal := componentOrbit_top_normal J
  let R := invariantSubspace F.terminalRepresentation H I hI.invariant
  let : IsIrreducible R.toRepresentation := hI.isIrrPlus.irreducible_of_normal_restriction
    F.terminalRepresentation (hg10.irreducible_of_not_solvable (nonabelian_hat_not_solvable h hn F hne)) H
  let : Nontrivial H := e.symm.injective.nontrivial
  obtain ⟨a,ha⟩ := exists_ne (1 : H)
  have hnon : ∃ a, R.toRepresentation a ≠ 1 :=
    ⟨a,fun he => ha (hf (he.trans R.toRepresentation.map_one.symm))⟩
  have hseven := (point_hat_seven_dvd h hn F hne).trans
    (card_subgroup_dvd_card (F.terminalDot (F.Li L 1)))
  obtain ⟨_,hnat | hperm⟩ :=
    ChapterG.Section09.DefiningCharacteristic.alternating_five_irreducible_action_alternatives
      R.toRepresentation e hnon
  · obtain ⟨a,⟨c⟩⟩ := hnat
    have hmR : ChapterG.Section09.Quasiequivalent R.toRepresentation
        (SL2.BinarySmall.natural (K := OrthogonalFourMinus.FiniteModel.Field 1)) :=
      ⟨a,c.toLinearEquiv,fun b w => LinearMap.congr_fun (c.isIntertwining' b) w⟩
    exact FixedLineConstituent.not_seven_of_natural_double F.terminalRepresentation
      F.terminalRepresentation_injective H e (fixed_doubled_model _ _ _ hd.2.1.some hmR) hseven
  · obtain ⟨a,⟨c⟩⟩ := hperm
    have hmR : ChapterG.Section09.Quasiequivalent R.toRepresentation
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 5)) :=
      ⟨a,c.toLinearEquiv,fun b w => LinearMap.congr_fun (c.isIntertwining' b) w⟩
    exact FixedLineConstituent.not_seven_of_permutation_double F.terminalRepresentation
      F.terminalRepresentation_injective H (fixed_doubled_model _ _ _ hd.2.1.some hmR) hseven

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
