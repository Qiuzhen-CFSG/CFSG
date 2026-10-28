module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineConstituent
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedProperFaithful

/-!
# Small carriers for the original marked fixed-line constituent

The preceding module supplies the literal single-component action quotient,
with degree at most its actor rank plus two, a fixed marked line and
self-duality. The G.9 component list at this sharper degree leaves only
A₅, A₆, A₇ and A₈. The binary derived G₂ row is excluded by its actual
irreducible degrees and automorphism two-rank. In the A₈ row, self-duality
identifies the actual natural six-space; the already proved two-copy
coordinates then give the original doubled-natural contradiction.

Thus the original component is normal and isomorphic to A₅, A₆ or A₇.
Their actual degree spectra and automorphism ranks force a four-dimensional
constituent. The proved multiplicity gives degree eight for the original
terminal module and order eight for its actor.

These conclusions concern a constituent containing the original marked
point. Existence or exchange of such constituents, identification of the
whole terminal action, and marked-catalogue exhaustiveness remain assembly
obligations. All ambient source assumptions and literal action maps are kept.

The carrier sieve specializes the existing marked proper-constituent sieve
in Chapter14/Section03 to the sharp fixed-line bound.
Source: Aschbacher--Smith G.11.7--8 and 14.4.2,
printed pp.366--369,1006--1007; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
namespace FixedLineModels
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
private theorem model_of_subgroup_eq
    {D E W U : Type*} [Group D] [Group E]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup U] [Module (ZMod 2) U]
    {ρ : Representation (ZMod 2) D W} {σ : Representation (ZMod 2) E U}
    {H C : Subgroup D} (he : H = C)
    (hm : ChapterG.Section09.Quasiequivalent (ρ.comp C.subtype) σ) :
    ChapterG.Section09.Quasiequivalent (ρ.comp H.subtype) σ := by
  subst H
  exact hm

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

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter14.Section03.NonabelianSource.Recognition
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction.Components
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
  (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
  (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
  (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
  (classification : EarlierFaithfulClassification G (T : Subgroup G))
  (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
  (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
  (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
  [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
    (hatSpace F (F.E g)) (F.terminalDot (F.X g))
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
  {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
  (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
  {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (hI : IsIrrPlus F.terminalRepresentation (componentOrbit C ⊤) I) (hv : v ∈ I)

include d earlier hq chosen structural alternatives hne hZ hlarge hgP hgH hyp hC hm hI hv

private theorem models_homogeneous_data :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
    Homogeneous.homogeneousPart R ⊤ = ⊤ ∧ Function.Injective R.toRepresentation ∧
      (∀ J : Subrepresentation (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype),
        IsIrreducible J.toRepresentation → Homogeneous.SameModule R J) := by
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hn := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
  have ha := hyp.constituent_homogeneous_faithful_selfDual_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv
  exact ⟨ha.1,ha.2.1,hyp.constituent_sameModule_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv⟩

include classification

private theorem fixed_line_original_carrier
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    FixedLineModels.SmallCarrier C := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let X := F.terminalDot (F.X g)
  have hns := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hXI := hyp.stabilizes_constituent_of_point_mem (hyp.irreducible_of_not_solvable hns) H hI hv
  have hinput := source_large_fixed_line_single_input d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hXI hline hn
  have hf := (models_homogeneous_data d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv).2.1
  let eC := MarkedAction.subgroupEquiv F.terminalRepresentation H X I hI.choose hXI hf
    C (le_componentOrbit C ⊤)
  have hc := FixedLineModels.smallCarrier_of_selfDual_sharp_fixed_line
    hinput.1 hinput.2.1 hinput.2.2.1 ⟨v,hv⟩
    (fun he => hyp.point_ne_zero (congrArg Subtype.val he)) hinput.2.2.2
  exact FixedLineModels.SmallCarrier.of_equiv eC hc

private theorem fixed_line_no_eight
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    (e : C ≃* alternatingGroup (Fin 8)) : False := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let X := F.terminalDot (F.X g)
  have hns := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hXI := hyp.stabilizes_constituent_of_point_mem (hyp.irreducible_of_not_solvable hns) H hI hv
  have hinput := source_large_fixed_line_single_input d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hXI hline hn
  have hHC := (source_large_fixed_line_component_normal d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn).1
  have hf := (models_homogeneous_data d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv).2.1
  let eC := MarkedAction.subgroupEquiv F.terminalRepresentation H X I hI.choose hXI hf
    C (le_componentOrbit C ⊤)
  have hm8 := ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.four_alternating_natural_of_selfDual
    hinput.1 hinput.2.2.1 ((eC.symm.trans e).trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two)
  have hmH := model_of_subgroup_eq
    (congrArg (MarkedAction.image F.terminalRepresentation H X I hI.choose hXI) hHC) hm8
  have hmR := MarkedAction.quasiequivalent_of_image F.terminalRepresentation H X I hI.choose hXI hf
    (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) hmH
  let f := Classical.choice (source_large_marked_double d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv).2
  exact ChapterG.Section11.not_doubled_natural_eight hyp (source_terminal_cover F d chosen) H
    (fixed_doubled_model _ _ _ f hmR)

/-- The proper marked branch of the original fixed-line action has one
normal component, with an actual A₅, A₆ or A₇ carrier.
The sharp constituent action excludes all other source carrier rows. -/
theorem source_large_fixed_line_component_models
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    C.Normal ∧ (Nonempty (C ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (C ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (C ≃* alternatingGroup (Fin 7))) := by
  refine ⟨(source_large_fixed_line_component_normal d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn).2,?_⟩
  rcases fixed_line_original_carrier d earlier hq chosen structural alternatives classification
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn with h5 | h6 | h7 | h8
  · exact Or.inl h5
  · exact Or.inr (Or.inl h6)
  · exact Or.inr (Or.inr h7)
  · obtain ⟨e8⟩ := h8
    exact (fixed_line_no_eight d earlier hq chosen structural alternatives classification
      F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn e8).elim

/-- In the original marked fixed-line branch the constituent has dimension
four and occurs exactly twice. Consequently the terminal module has degree
eight and the actual elementary actor has order eight. -/
theorem source_large_fixed_line_marked_degree
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
      Nat.card (F.terminalDot (F.X g)) = 8 := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let X := F.terminalDot (F.X g)
  have hns := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hXI := hyp.stabilizes_constituent_of_point_mem (hyp.irreducible_of_not_solvable hns) H hI hv
  have hinput := source_large_fixed_line_single_input d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hXI hline hn
  have hf := (models_homogeneous_data d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv).2.1
  let eC := MarkedAction.subgroupEquiv F.terminalRepresentation H X I hI.choose hXI hf
    C (le_componentOrbit C ⊤)
  have hdI := FixedLineModels.small_alternating_degree hinput.1 hinput.2.1 eC
    (source_large_fixed_line_component_models d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn).2
  have hd := (source_large_marked_double d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv).1
  have he : finrank (ZMod 2) (Additive F.Uhat) = 8 := by omega
  exact ⟨hdI,he,(source_fixed_line_module d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH B v hyp hline hn).2.2 he |>.1⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
