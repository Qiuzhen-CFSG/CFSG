module
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.SharpDegree
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition
public import GorensteinWalter.PSL2CoreModelFacts

/-!
# Recognition of even-degree two-component actions

For a pair of components the genuine common-field tensor has degree n*k².
The source rank bounds reduce k to two or three. In even degree the second
case forces n at least two and component rank at least four. The actual
binary SL₂ Schur degrees and Suzuki minimum degree then exclude k=3.
The surviving two-dimensional factors have the full special-linear order
over their actual Schur field: the binary model uses its Schur degree, Suzuki
and J₁ violate the degree bound, and odd PSL₂ embeds in SL₂(4) with order
at least sixty. Actual matrix images then construct the two natural factors
and their tensor intertwiner. All earlier section and component-model inputs
are discharged for the full known-simple class. The action on the original
component join is retained.

Source: Aschbacher–Smith G.9.3, printed pp.354–357, and G.11.7, pp.366–368.
-/

public noncomputable section
open scoped MatrixGroups MonoidAlgebra
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents
open FactorReduction.ModelRestrictions
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L L₂ A H : Subgroup G} {m : ℕ}

namespace TensorData
omit [FiniteDimensional (ZMod 2) V] in
/-- Evenness eliminates the three-dimensional factor using its actual
Schur field, without a whole-group tensor identification. -/
theorem factor_dimension_two_of_even (T : TensorData ρ L L₂)
    (hL : IsComponent G L) (hm : m ≤ 2 * primeRank 2 L)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (m + 1))
    (hev : Even (Module.finrank (ZMod 2) V))
    (hmodels : 4 ≤ primeRank 2 L → FactorReduction.LargeRankModel L) :
    T.k = 2 := by
  have hsz : FactorReduction.SuzukiBinaryDegreeTheorem.{v} := by
    intro s hs W _ _ _ σ hi hf
    let := hi
    exact Representation.Suzuki.finrank_ge hs σ hf
  rcases T.factor_dimension_two_or_three_of_large_models hsz hL hm hd hmodels with hk | hk
  · exact hk
  exfalso
  have hdeg := T.degree_eq
  rw [hk] at hdeg
  norm_num at hdeg
  have hn := T.n_pos
  obtain ⟨a, ha⟩ := hev
  have hn2 : 2 ≤ T.n := by omega
  have hr : 4 ≤ primeRank 2 L := by omega
  have hnr : T.n ≤ primeRank 2 L := by omega
  obtain ⟨B, hB, hc⟩ := exists_elementaryAbelian_card_primeRank (G := L) (p := 2)
  have hsetup := (T.factor_setup_and_degree_lt B hB hc hm hnr (by omega) hd).1
  let τ : Representation (ZMod 2) L T.I := Representation.restrictScalars T.left
  have hfac := T.factor_degree_eq
  rw [hk] at hfac
  rcases hmodels hr with ⟨F,_,_,_,hF,⟨e⟩⟩ | ⟨s,hs,⟨e⟩⟩
  · let σ : Representation (ZMod 2) SL(2,F) T.I := τ.comp e.symm.toMonoidHom
    let : Representation.IsIrreducible σ :=
      (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom
        e.symm.surjective τ).mpr T.left_irreducible
    let : IsQuasisimple L := hL.2
    let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    have hnt : ∃ g, σ g ≠ 1 := by
      obtain ⟨l, hl⟩ := exists_ne (1 : L)
      refine ⟨e l, fun he => hl ?_⟩
      apply T.left_faithful
      ext x
      have hx := congrArg (fun f : Module.End (ZMod 2) T.I => f x) he
      simpa [σ, τ, Representation.restrictScalars] using hx
    have hschur := T.left_schur_degree_comp e.symm
    change Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,F)] σ.asModule) = T.n at hschur
    rcases DefiningCharacteristic.binary_small_degree_schur_alternatives σ hnt
      (primeRank 2 L) (by omega) hF hsetup.degree_le with h | h | h
    · rw [hschur] at h
      omega
    · rw [hschur] at h
      omega
    · omega
  · let σ : Representation (ZMod 2) (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup s) T.I :=
      τ.comp e.symm.toMonoidHom
    have hf : Function.Injective σ := by
      intro a b hab
      apply e.symm.injective
      apply T.left_faithful
      ext x
      exact congrArg (fun f : Module.End (ZMod 2) T.I => f x) hab
    have hlo := Representation.Suzuki.finrank_ge hs σ hf
    have hrank : primeRank 2 L = 2*s+1 :=
      (primeRank_equiv 2 e).trans (BenderSuzuki.MatrixGroups.suzuki_two_rank s hs)
    have hu := hsetup.degree_le
    omega
end TensorData

/-- The original even-degree action has genuine two-dimensional tensor
factors whenever its component orbit has two distinct components. -/
theorem exists_tensor_factor_dimension_two_of_even
    (h : ComponentHypothesis KnownSimple.IsKnownSimple ρ A L H m)
    (h₂ : IsComponent G L₂) (hH : H = L ⊔ L₂) (hne : L ≠ L₂)
    (hq : Quasiequivalent (ρ.comp L.subtype) (ρ.comp L₂.subtype) ∨
      Quasiequivalent (ρ.comp L.subtype) (Representation.dual (ρ.comp L₂.subtype)))
    (hev : Even (Module.finrank (ZMod 2) V)) :
    ∃ T : TensorData ρ L L₂, T.k = 2 ∧ m ≤ 2 * primeRank 2 L := by
  obtain ⟨T⟩ := CommonField.tensorConstruction ρ L L₂ h.faithful h.component h₂ hne
    (hH ▸ h.irreducible) hq
  obtain ⟨e⟩ : Nonempty (L ≃* L₂) := by
    rcases hq with ⟨e,_,_⟩ | ⟨e,_,_⟩ <;> exact ⟨e⟩
  have hb : BinaryAutomorphismRankTheorem := fun _ _ _ _ _ hn hc =>
    Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn hc
  obtain ⟨hz,hr,ha,hmodels⟩ := component_model_restrictions
    semisimpleSectionRank_knownSimple sourceA134Three_knownSimple hb h h₂ hH hne hq T
  have hm := actor_rank_bound_of_factor_automorphism_rank h h₂ hH hne e hz hr ha
  exact ⟨T,T.factor_dimension_two_of_even h.component hm h.degree_le hev hmodels,hm⟩

private theorem perfect_card_le_specialLinear
    {S E W : Type*} [Group S] [Group.IsPerfect S] [Field E] [Finite E]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (σ : Representation E S W) (hi : Function.Injective σ) {d : ℕ}
    (hd : Module.finrank E W = d) : Nat.card S ≤ Nat.card SL(d,E) := by
  let b := Module.finBasisOfFinrankEq E W hd
  let g : S →* (W ≃ₗ[E] W) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv E W).toMonoidHom.comp σ.asGroupHom
  have hdet (s : S) : (g s).det = 1 :=
    Abelianization.commutator_subset_ker (LinearEquiv.det.comp g)
      (Group.IsPerfect.mem_commutator (g := s))
  let t : S →* _root_.SpecialLinearGroup E W :=
    { toFun := fun s => ⟨g s, hdet s⟩
      map_one' := by apply Subtype.ext; exact g.map_one
      map_mul' := fun s t => by apply Subtype.ext; exact g.map_mul s t }
  have ht : Function.Injective t := by
    intro a b hab
    apply hi
    ext w
    exact congrArg (fun f : _root_.SpecialLinearGroup E W => f.val w) hab
  exact Nat.card_le_card_of_injective
    (fun s => (Matrix.SpecialLinearGroup.toLin_equiv b).symm (t s))
    ((Matrix.SpecialLinearGroup.toLin_equiv b).symm.injective.comp ht)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem left_binary_faithful (T : TensorData ρ L L₂) :
    Function.Injective (Representation.restrictScalars T.left :
      Representation (ZMod 2) L T.I) := by
  intro a b h
  apply T.left_faithful
  ext x
  exact congrArg (fun f : Module.End (ZMod 2) T.I => f x) h

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem left_binary_nontrivial (T : TensorData ρ L L₂)
    (hL : IsComponent G L) :
    ∃ g, (Representation.restrictScalars T.left :
      Representation (ZMod 2) L T.I) g ≠ 1 := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  obtain ⟨g,hg⟩ := exists_ne (1 : L)
  exact ⟨g,fun he => hg (left_binary_faithful T (by simpa only [map_one] using he))⟩

omit [FiniteDimensional (ZMod 2) V] in
/-- In the source degree window each genuine two-dimensional factor has
full special-linear order over its own Schur field. The odd PSL₂ branch is
handled inside SL₂(4); no unrestricted small-module classification is assumed. -/
theorem TensorData.card_eq_specialLinear_of_dimension_two (T : TensorData ρ L L₂)
    (hL : IsComponent G L) (hk : T.k = 2)
    (hm : m ≤ 2 * primeRank 2 L)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (m+1))
    (hodd : ∀ p : ℕ, p.Prime → Odd p → primeRank p L ≤ 1)
    (hmodels : QuotientModel L) : Nat.card L = Nat.card SL(2,GaloisField 2 T.n) := by
  let τ : Representation (ZMod 2) L T.I := Representation.restrictScalars T.left
  have hf : Function.Injective τ := left_binary_faithful T
  have hnt : ∃ g, τ g ≠ 1 := left_binary_nontrivial T hL
  let : IsQuasisimple L := hL.2
  have hdeg := T.degree_eq
  rw [hk] at hdeg
  norm_num at hdeg
  have hfac := T.factor_degree_eq
  rw [hk] at hfac
  have hn := T.n_pos
  have hnr : T.n ≤ primeRank 2 L := by omega
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
    have hsnt : ∃ g, σ g ≠ 1 := by
      obtain ⟨g,hg⟩ := hnt
      exact ⟨e g,by simpa [σ] using hg⟩
    have hschur := T.left_schur_degree_comp e.symm
    change Module.finrank (ZMod 2)
      (Module.End (ZMod 2)[SL(2,GaloisField 2 n)] σ.asModule) = T.n at hschur
    have hnEq : n = T.n := by
      rcases DefiningCharacteristic.binary_small_degree_schur_alternatives σ hsnt n hn2 hc
        (by omega) with h | h | h
      · rw [hschur] at h
        omega
      · rw [hschur] at h
        omega
      · rw [hschur] at h
        omega
    exact (Nat.card_congr e.toEquiv).trans (by rw [hnEq])
  · let σ : Representation (ZMod 2) (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup s) T.I :=
      τ.comp e.symm.toMonoidHom
    have hlo := Representation.Suzuki.finrank_ge hs σ (hf.comp e.symm.injective)
    have hr : primeRank 2 L = 2*s+1 :=
      (primeRank_equiv 2 e).trans (BenderSuzuki.MatrixGroups.suzuki_two_rank s hs)
    omega
  · obtain ⟨e⟩ := hj
    have hr : primeRank 2 L ≤ 3 := by
      obtain ⟨E,_,hE⟩ := exists_elementaryAbelian_card_primeRank (G := L) (p := 2)
      have hdiv := E.card_subgroup_dvd_card
      rw [hE,Nat.card_congr e.toEquiv,Janko1.card_model] at hdiv
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
      rw [← Nat.card_eq_fintype_card,GaloisField.card p 1 (by decide)]
      simp)
    let ep := e.trans (GorensteinWalter.psl2RingEquiv eF)
    have hr : primeRank 2 L = 2 :=
      (primeRank_equiv 2 ep).trans (Theory.PSL2.primeField_two_rank hp3)
    have hn2 : T.n = 2 := by
      by_contra he
      have hn1 : T.n = 1 := by omega
      have hdim : Module.finrank (ZMod 2) T.I ≤ 2 := by omega
      obtain ⟨g,hg⟩ := hnt
      exact hg (Representation.BinaryOffender.representation_eq_one_of_isPerfect_of_finrank_le_two
        τ hdim g)
    have hcF : Nat.card T.F = 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      change 2^T.n = 4
      norm_num [hn2]
    let : Finite T.F := Module.finite_of_finite (ZMod 2)
    have hupper := perfect_card_le_specialLinear T.left T.left_faithful hk
    rw [GorensteinWalter.sl2_card_formula,hcF] at hupper
    norm_num at hupper
    have hlower : 60 ≤ Nat.card L := by
      rw [Nat.card_congr ep.toEquiv]
      apply GorensteinWalter.psl2_card_ge_sixty_of_card_gt_three (ZMod p)
      · exact ⟨p,1,hp.out,hp.out.odd_of_ne_two (by omega),by decide,by simp⟩
      · simpa only [Nat.card_zmod] using hp3
    have htarget : Nat.card SL(2,GaloisField 2 T.n) = 60 := by
      rw [GorensteinWalter.sl2_card_formula,GaloisField.card 2 T.n hn.ne',hn2]
      norm_num
    omega

/-- Recognition of the actual normal component join in the even-degree
case, with all catalogue and small-factor premises discharged. -/
theorem even_component_join_recognition
    (h : ComponentHypothesis KnownSimple.IsKnownSimple ρ A L H m)
    (h₂ : IsComponent G L₂) (hH : H = L ⊔ L₂) (hne : L ≠ L₂)
    (hq : Quasiequivalent (ρ.comp L.subtype) (ρ.comp L₂.subtype) ∨
      Quasiequivalent (ρ.comp L.subtype) (Representation.dual (ρ.comp L₂.subtype)))
    (hev : Even (Module.finrank (ZMod 2) V)) :
    ∃ n : ℕ, 1 < n ∧ Module.finrank (ZMod 2) V = 4*n ∧
      Nonempty (L ≃* SL(2,GaloisField 2 n)) ∧
      Quasiequivalent (ρ.comp H.subtype) (fourOrthogonal n) := by
  obtain ⟨T,hk,hm⟩ := exists_tensor_factor_dimension_two_of_even h h₂ hH hne hq hev
  obtain ⟨e⟩ : Nonempty (L ≃* L₂) := by
    rcases hq with ⟨e,_,_⟩ | ⟨e,_,_⟩ <;> exact ⟨e⟩
  have hz := component_center_eq_bot semisimpleSectionRank_knownSimple h h₂ hne e T
  have hmodel := source_quotient_models semisimpleSectionRank_knownSimple
    sourceA134Three_knownSimple h h₂ hH hne e
  let ez : L ≃* (L ⧸ center L) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hz.symm)
  have hodd : ∀ p : ℕ, p.Prime → Odd p → primeRank p L ≤ 1 := fun p hp ho =>
    odd_rank_le_one h.component h₂ hH hne e hz
      (pair_join_stronglyQuasithin semisimpleSectionRank_knownSimple h h₂ hH) hp ho
  have ho := T.card_eq_specialLinear_of_dimension_two h.component hk hm h.degree_le
    hodd (hmodel.of_equiv ez)
  let : IsQuasisimple L := h.component.2
  let : IsQuasisimple L₂ := h₂.2
  have hd := component_pair_disjoint_of_center_eq_bot h.component h₂ hne hz
  refine ⟨T.n,NaturalRecognition.two_dimensional_field_degree T h.component hk ho,?_,?_,?_⟩
  · rw [T.degree_eq,hk]
    ring
  · obtain ⟨a,_,_⟩ := NaturalRecognition.natural_coordinates_of_order T.left T.left_faithful
      hk T.fieldEquiv.toRingEquiv ho
    exact ⟨a⟩
  · exact NaturalRecognition.quasiequivalent_trans
      (NaturalRecognition.tensor_natural_of_order T
        (h.component.commutator_eq_bot_of_ne h₂ hne) hd hH T.fieldEquiv hk ho
        ((Nat.card_congr e.toEquiv).symm.trans ho))
      (NaturalRecognition.naturalTensor_fourOrthogonal T.n)

end CFSG.Quasithin.ChapterG.Section09.TwoComponents
