module
public import CFSG.Quasithin.ChapterG.Section11.WholePair
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Natural recognition of the whole component pair

The four actual A.1.34 carrier families and the original actor-degree bound
identify the order of each two-dimensional tensor factor. Binary SL2 uses
the actual Schur degree; Suzuki and J1 violate constituent degree bounds.
Odd-field PSL2 has common field F4: perfectness bounds its faithful matrix
image by SL2(4), and its order formula gives equality. Faithful coordinates
then identify the original component-join action with the natural split
orthogonal module. No small-module classification callback is assumed.

`WholePairExclusion` uses this identification on the original rank-two actor.
Source: Aschbacher--Smith G.9.3(15), G.11.7 and 6.2.19,
printed pp.354--356,368,691.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped MatrixGroups MonoidAlgebra
namespace CFSG.Quasithin.ChapterG.Section11.WholePairNatural
open Section09 Section09.TwoComponents
open Section09.TwoComponents.FactorReduction.ModelRestrictions
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {X L L₂ H : Subgroup G} {m : ℕ}

private theorem perfect_card_le_special {F I S : Type*} [Field F] [Finite F]
    [AddCommGroup I] [Module F I] [FiniteDimensional F I]
    [Group S] [Finite S] [Group.IsPerfect S]
    (σ : Representation F S I) (hf : Function.Injective σ)
    (d : ℕ) (hd : finrank F I=d) : Nat.card S ≤ Nat.card SL(d,F) := by
  let b := Module.finBasisOfFinrankEq F I hd
  let g : S →* (I ≃ₗ[F] I) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F I).toMonoidHom.comp σ.asGroupHom
  have hdet (s : S) : (g s).det=1 :=
    Abelianization.commutator_subset_ker (LinearEquiv.det.comp g)
      (Group.IsPerfect.mem_commutator (g := s))
  let t : S →* _root_.SpecialLinearGroup F I :=
    { toFun := fun s => ⟨g s,hdet s⟩,
      map_one' := by apply Subtype.ext; exact g.map_one,
      map_mul' := fun s t => by apply Subtype.ext; exact g.map_mul s t }
  let q := (Matrix.SpecialLinearGroup.toLin_equiv b).symm.toMonoidHom.comp t
  apply Nat.card_le_card_of_injective q
  intro r s he
  have hh : t r=t s := (Matrix.SpecialLinearGroup.toLin_equiv b).symm.injective he
  have hh' : g r=g s := congrArg Subtype.val hh
  apply hf
  ext x
  exact LinearEquiv.congr_fun hh' x

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem factor_faithful (T : TensorData ρ L L₂) :
    Function.Injective (Representation.restrictScalars T.left :
      Representation (ZMod 2) L T.I) := by
  intro a b hab
  apply T.left_faithful
  ext x
  exact congrArg (fun f : Module.End (ZMod 2) T.I => f x) hab

private theorem factor_order
    (h : ComponentHypothesis KnownSimple.IsKnownSimple ρ X L H m)
    (T : TensorData ρ L L₂) (hm : m≤2*primeRank 2 L) (hk : T.k=2)
    (hodd : ∀ p, p.Prime → Odd p → primeRank p L≤1)
    (hmodels : QuotientModel L) :
    Nat.card L=Nat.card SL(2,GaloisField 2 T.n) := by
  let : Finite T.F := Module.finite_iff_finite.mp T.finiteField
  let : IsQuasisimple L := h.component.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  let τ : Representation (ZMod 2) L T.I := Representation.restrictScalars T.left
  have hf : Function.Injective τ := factor_faithful T
  have hn0 := T.n_pos
  have hdeg := T.degree_eq
  have hfac := T.factor_degree_eq
  rw [hk] at hdeg hfac
  norm_num at hdeg hfac
  have hd := h.degree_le
  have hnrank : T.n≤primeRank 2 L := by omega
  have hn2 : 2≤T.n := by
    by_contra hh
    have hh' : finrank (ZMod 2) T.I≤2 := by omega
    obtain ⟨g,hg⟩ := exists_ne (1 : L)
    apply hg
    apply hf
    simpa only [map_one] using
      BinaryOffender.representation_eq_one_of_isPerfect_of_finrank_le_two τ hh' g
  rcases hmodels with ⟨n,hn,⟨e⟩⟩ | ⟨s,hs,⟨e⟩⟩ | hj | ⟨p,hp,a,hp3,ha,ha2,⟨e⟩⟩
  · let : NeZero n := ⟨by omega⟩
    have hc := GaloisField.card 2 n (by omega)
    have hr : primeRank 2 L≤n := by
      rw [primeRank_equiv 2 e]
      exact (Theory.GroupTheory.primeRank_le_of_injective 2 MulAut.conj
        (MulAut.conj_injective_of_center_eq_bot (Theory.PSL2.sl2_center_eq_bot _))).trans
        (Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn hc)
    let σ : Representation (ZMod 2) SL(2,GaloisField 2 n) T.I := τ.comp e.symm.toMonoidHom
    let : IsIrreducible σ :=
      (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective τ).mpr T.left_irreducible
    have hnt : ∃ g,σ g≠1 := by
      obtain ⟨g,hg⟩ := exists_ne (1 : L)
      refine ⟨e g,fun he => hg (hf ?_)⟩
      simpa only [σ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply,map_one] using he
    have hsch := T.left_schur_degree_comp e.symm
    change finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,GaloisField 2 n)] σ.asModule)=T.n at hsch
    have heq : T.n=n := by
      rcases DefiningCharacteristic.binary_small_degree_schur_alternatives σ hnt n hn hc
        (by omega) with hh | hh | hh
      all_goals rw [hsch] at hh; omega
    rw [heq]
    exact Nat.card_congr e.toEquiv
  · let σ := τ.comp e.symm.toMonoidHom
    have hlo := Representation.Suzuki.finrank_ge (by omega : 1≤s) σ (hf.comp e.symm.injective)
    have hrank : primeRank 2 L=2*s+1 :=
      (primeRank_equiv 2 e).trans (BenderSuzuki.MatrixGroups.suzuki_two_rank s hs)
    omega
  · obtain ⟨e⟩ := hj
    have hr : primeRank 2 L≤3 := by
      obtain ⟨E,_,hE⟩ := exists_elementaryAbelian_card_primeRank (G := L) (p := 2)
      have hdiv := E.card_subgroup_dvd_card
      rw [hE,Nat.card_congr e.toEquiv,Janko1.card_model] at hdiv
      by_contra hh
      have hh' : 2^4 ∣175560 := (pow_dvd_pow 2 (by omega : 4≤primeRank 2 L)).trans hdiv
      norm_num at hh'
    have hdiv : 11 ∣ Nat.card L := by
      rw [Nat.card_congr e.toEquiv,Janko1.card_model]
      norm_num
    have hlo := BinaryPrimeDegree.orderOf_le_finrank τ hf
      (by decide : Nat.Prime 11) (by decide) hdiv
    rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hlo
    omega
  · have he : a=1 := odd_exponent_eq_one hp3 ha e
      (hodd p hp.out (hp.out.odd_of_ne_two (by omega)))
    subst a
    let : Fintype (GaloisField p 1) := Fintype.ofFinite _
    let eF : GaloisField p 1 ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
      rw [←Nat.card_eq_fintype_card,GaloisField.card p 1 (by decide)]
      simp)
    let ep := e.trans (GorensteinWalter.psl2RingEquiv eF)
    have hr : primeRank 2 L=2 :=
      (primeRank_equiv 2 ep).trans (Theory.PSL2.primeField_two_rank hp3)
    have hn : T.n=2 := by omega
    have hup := perfect_card_le_special T.left T.left_faithful 2 hk
    rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,T.field_card,hn] at hup
    norm_num at hup
    have hpodd : Odd p := hp.out.odd_of_ne_two (by omega)
    have hcard := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
      (F := ZMod p) (by simpa only [Nat.card_zmod] using hpodd)
    rw [Nat.card_zmod,←Nat.card_congr ep.toEquiv] at hcard
    have hp5 : 5≤p := by obtain ⟨k,hk⟩ := hpodd; omega
    have hsq : 25≤p^2 := by
      simpa only [pow_two] using Nat.mul_le_mul hp5 hp5
    have hsub : 24≤p^2-1 := by omega
    have hlo : 120≤p*(p^2-1) := Nat.mul_le_mul hp5 hsub
    have heq : Nat.card L=60 := by omega
    rw [heq,hn,BenderSuzuki.External.huppert614_card_specialLinearGroup,
      GaloisField.card 2 2 (by decide)]
    norm_num

/-- The actual two-dimensional factors give the natural orthogonal action
on the original component join, with all numerical classification inputs discharged. -/
theorem recognition
    (h : ComponentHypothesis KnownSimple.IsKnownSimple ρ X L H m)
    (h₂ : IsComponent G L₂) (hH : H=L⊔L₂) (hne : L≠L₂)
    (e : L ≃* L₂) (hz : center L=⊥)
    (T : TensorData ρ L L₂) (hm : m≤2*primeRank 2 L) (hk : T.k=2) :
    Nat.card L=Nat.card SL(2,GaloisField 2 T.n) ∧
      1<T.n ∧ Quasiequivalent (ρ.comp H.subtype) (fourOrthogonal T.n) := by
  have hmodels := source_quotient_models semisimpleSectionRank_knownSimple
    sourceA134Three_knownSimple h h₂ hH hne e
  let ez : L ≃* (L ⧸ center L) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hz.symm)
  have hodd : ∀ p,p.Prime → Odd p → primeRank p L≤1 := fun p hp ho =>
    odd_rank_le_one h.component h₂ hH hne e hz
      (pair_join_stronglyQuasithin semisimpleSectionRank_knownSimple h h₂ hH) hp ho
  have ho := factor_order h T hm hk hodd (hmodels.of_equiv ez)
  let : IsQuasisimple L := h.component.2
  let : IsQuasisimple L₂ := h₂.2
  refine ⟨ho,NaturalRecognition.two_dimensional_field_degree T h.component hk ho,?_⟩
  exact NaturalRecognition.quasiequivalent_trans (NaturalRecognition.tensor_natural_of_order T
    (h.component.commutator_eq_bot_of_ne h₂ hne)
    (component_pair_disjoint_of_center_eq_bot h.component h₂ hne hz) hH
    T.fieldEquiv hk ho ((Nat.card_congr e.toEquiv).symm.trans ho))
      (NaturalRecognition.naturalTensor_fourOrthogonal T.n)
end CFSG.Quasithin.ChapterG.Section11.WholePairNatural
