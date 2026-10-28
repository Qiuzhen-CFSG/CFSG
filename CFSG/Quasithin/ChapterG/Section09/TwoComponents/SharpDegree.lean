module
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.ModelRestrictions
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.AutomorphismSquare
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryRankOne
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank
public import Theory.Representation.Suzuki.BinaryDegree
public import Theory.Representation.BinaryOffender.QuadraticHomogeneousOrbit
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.ModelRestrictions.KnownSimpleSource

/-!
# A single component under the sharp original degree bound

For two distinct components the common-field tensor decomposition has degree
n*k^2, while the actual elementary actor has rank at most twice the component
rank. The stronger bound d <= m+2 forces the factor degree below the minimum
for each of the four A.1.34 models. The completed Theorems A and C supply that
list for the genuine SQTK cover. Hence H equals the original moved component.

This specializes G.9.3 to the bound occurring in the exchanged constituent
and proper or two-copy marked actions; it does not assert this stronger bound
for the whole-space marked action.
Source: Aschbacher--Smith G.9.3, printed pp.353--357, and G.11.6, p.366.
-/

public noncomputable section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents
open FactorReduction.ModelRestrictions
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L L₂ : Subgroup G}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem factor_faithful (T : TensorData ρ L L₂) :
    Function.Injective (Representation.restrictScalars T.left :
      Representation (ZMod 2) L T.I) := by
  intro a b h
  apply T.left_faithful
  ext x
  exact congrArg (fun f : Module.End (ZMod 2) T.I => f x) h

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem factor_nontrivial (T : TensorData ρ L L₂)
    (hL : IsComponent G L) :
    ∃ g, (Representation.restrictScalars T.left :
      Representation (ZMod 2) L T.I) g ≠ 1 := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  obtain ⟨g,hg⟩ := exists_ne (1 : L)
  refine ⟨g, fun he => hg (factor_faithful T ?_)⟩
  simpa only [map_one] using he

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem factor_degree_le_of_sharp (T : TensorData ρ L L₂)
    (hL : IsComponent G L) {m r : ℕ} (hm : m ≤ 2*r)
    (hd : Module.finrank (ZMod 2) V ≤ m+2) :
    Module.finrank (ZMod 2) T.I ≤ r+1 := by
  have hk := T.two_le_factor_dimension hL
  have hmul := Nat.mul_le_mul_left (T.n * T.k) hk
  rw [T.factor_degree_eq]
  rw [T.degree_eq] at hd
  nlinarith

omit [FiniteDimensional (ZMod 2) V] in
/-- The actual tensor factor cannot meet the sharper original degree bound
for any of the four source component models. -/
theorem tensor_false_of_sharp_models (T : TensorData ρ L L₂)
    (hL : IsComponent G L) {m : ℕ} (hm : m ≤ 2*primeRank 2 L)
    (hd : Module.finrank (ZMod 2) V ≤ m+2)
    (hodd : ∀ p : ℕ, p.Prime → Odd p → primeRank p L ≤ 1)
    (hmodels : QuotientModel L) : False := by
  let τ : Representation (ZMod 2) L T.I := Representation.restrictScalars T.left
  have hf : Function.Injective τ := factor_faithful T
  have hn := factor_nontrivial T hL
  have hsmall := factor_degree_le_of_sharp T hL hm hd
  rcases hmodels with ⟨n,hn2,⟨e⟩⟩ | ⟨s,hs,⟨e⟩⟩ | hj | ⟨p,hp,a,hp3,ha,ha2,⟨e⟩⟩
  · let : NeZero n := ⟨by omega⟩
    have hc := GaloisField.card 2 n (by omega)
    have hr : primeRank 2 L ≤ n := by
      rw [primeRank_equiv 2 e]
      exact (Theory.GroupTheory.primeRank_le_of_injective 2 MulAut.conj
        (MulAut.conj_injective_of_center_eq_bot
          (Theory.PSL2.sl2_center_eq_bot _))).trans
        (Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn2 hc)
    let σ : Representation (ZMod 2) SL(2,GaloisField 2 n) T.I :=
      τ.comp e.symm.toMonoidHom
    let : Representation.IsIrreducible σ :=
      (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom
        e.symm.surjective τ).mpr T.left_irreducible
    have hnt : ∃ g, σ g ≠ 1 := by
      obtain ⟨g,hg⟩ := hn
      exact ⟨e g, by simpa [σ,τ] using hg⟩
    rcases DefiningCharacteristic.binary_small_degree_alternatives σ hnt n hn2 hc
      (by omega) with hdeg | hdeg <;> omega
  · let σ : Representation (ZMod 2) (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup s) T.I :=
      τ.comp e.symm.toMonoidHom
    have hsf : Function.Injective σ := hf.comp e.symm.injective
    have hlo := Representation.Suzuki.finrank_ge (by omega : 1 ≤ s) σ hsf
    have hr : primeRank 2 L = 2*s+1 :=
      (primeRank_equiv 2 e).trans (BenderSuzuki.MatrixGroups.suzuki_two_rank s hs)
    omega
  · obtain ⟨e⟩ := hj
    have hr : primeRank 2 L ≤ 3 := by
      obtain ⟨E,_,hE⟩ := exists_elementaryAbelian_card_primeRank (G := L) (p := 2)
      have hdiv := E.card_subgroup_dvd_card
      rw [hE, Nat.card_congr e.toEquiv, Janko1.card_model] at hdiv
      by_contra h
      have hh : 2^4 ∣ 175560 :=
        (pow_dvd_pow 2 (by omega : 4 ≤ primeRank 2 L)).trans hdiv
      norm_num at hh
    have hdiv : 11 ∣ Nat.card L := by
      rw [Nat.card_congr e.toEquiv,Janko1.card_model]
      norm_num
    have hlo := Representation.BinaryPrimeDegree.orderOf_le_finrank τ hf
      (by decide : Nat.Prime 11) (by decide) hdiv
    rw [Representation.BinaryPrimeDegree.orderOf_two_mod_eleven] at hlo
    omega
  · have he : a = 1 := odd_exponent_eq_one hp3 ha e
      (hodd p hp.out (hp.out.odd_of_ne_two (by omega)))
    subst a
    let : Fintype (GaloisField p 1) := Fintype.ofFinite _
    let eF : GaloisField p 1 ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, GaloisField.card p 1 (by decide)]
      simp)
    let ep := e.trans (GorensteinWalter.psl2RingEquiv eF)
    have hr : primeRank 2 L = 2 :=
      (primeRank_equiv 2 ep).trans (Theory.PSL2.primeField_two_rank hp3)
    have hk := T.two_le_factor_dimension hL
    have hnpos := T.n_pos
    have hdegree := T.degree_eq
    have hmul := Nat.mul_le_mul_right (T.k^2) hnpos
    have hk2 : T.k = 2 := by nlinarith
    have hfac := T.factor_degree_eq
    have hdim : Module.finrank (ZMod 2) T.I ≤ 2 := by
      rw [hk2] at hdegree hfac
      norm_num at hdegree hfac
      omega
    let : IsQuasisimple L := hL.2
    obtain ⟨g,hg⟩ := hn
    exact hg (Representation.BinaryOffender.representation_eq_one_of_isPerfect_of_finrank_le_two
      τ hdim g)

variable {K : GroupClass.{u}} {A H : Subgroup G} {m : ℕ}

theorem single_component_of_sharp_degree_of_source
    (hA : SemisimpleSectionRankTheorem K) (hs : SourceA134Three K)
    (h : ComponentHypothesis K ρ A L H m)
    (hd : Module.finrank (ZMod 2) V ≤ m+2) : H = L := by
  rcases h.components with he | ⟨L₂,hL₂,hH,hq⟩
  · exact he
  by_cases hne : L = L₂
  · simpa only [← hne, sup_idem] using hH
  obtain ⟨T⟩ := CommonField.tensorConstruction ρ L L₂ h.faithful h.component hL₂ hne
    (hH ▸ h.irreducible) hq
  obtain ⟨e⟩ : Nonempty (L ≃* L₂) := by
    rcases hq with ⟨e,_,_⟩ | ⟨e,_,_⟩ <;> exact ⟨e⟩
  have hz := component_center_eq_bot hA h hL₂ hne e T
  have hmodel := source_quotient_models hA hs h hL₂ hH hne e
  let ez : L ≃* (L ⧸ center L) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hz.symm)
  have hmodels : QuotientModel L := hmodel.of_equiv ez
  have hodd : ∀ p : ℕ, p.Prime → Odd p → primeRank p L ≤ 1 := fun p hp ho =>
    odd_rank_le_one h.component hL₂ hH hne e hz
      (pair_join_stronglyQuasithin hA h hL₂ hH) hp ho
  have hb : BinaryAutomorphismRankTheorem := fun _ _ _ _ _ hn hc =>
    Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn hc
  have hr := model_ranks hb hmodels hodd
  have hm := actor_rank_bound_of_factor_automorphism_rank h hL₂ hH hne e hz hr.1 hr.2.1
  exact (tensor_false_of_sharp_models T h.component hm hd hodd hmodels).elim

/-- The sharp original degree bound excludes two distinct components with
all earlier classification inputs discharged for the full known-simple class. -/
theorem single_component_of_sharp_degree
    (h : ComponentHypothesis KnownSimple.IsKnownSimple ρ A L H m)
    (hd : Module.finrank (ZMod 2) V ≤ m+2) : H = L :=
  single_component_of_sharp_degree_of_source
    semisimpleSectionRank_knownSimple sourceA134Three_knownSimple h hd

end CFSG.Quasithin.ChapterG.Section09.TwoComponents
