module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.ModuleSieve
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.ElementaryAbelian.Quotient

/-!
# Source critical-pair transport for the orthogonal branch of 13.8.25

This module realizes the actual section U_H/V₁ as a binary conjugation module,
retains the distinct source denominators A₁ and V₁, and transports the critical
pair bounds used in 13.8.22–23. The source group assumptions are explicit:
normality is relative to U_H, while H-normalization and H-centrality are
separate fields. Thus no arbitrary representation or ambient normality is
introduced. The final rank-one record supplies the faithful section actions,
fixed-space identifications, atom line, larger actor and displacement line
consumed by the orthogonal contradiction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, printed pp.947–950 and 957–960 (PDF pp.964–967,
974–977), especially F.9.13(6–7), 13.8.8 and 13.8.21–23.
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.SourceTransport
open FourStructure.CriticalTransfer Representation.BinaryOffender
open FourStructure.CriticalTransfer
variable {G : Type*} [Group G] (H U Z : Subgroup G)
  [(Z.subgroupOf U).Normal] [IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U)]

private noncomputable def localAction (hn : H ≤ normalizer (U : Set G))
    (hz : H ≤ centralizer (Z : Set G)) : H →* MulAut (U ⧸ Z.subgroupOf U) :=
  Classical.choose (exists_quotient_conjugation_action H U Z hn
    (hz.trans (centralizer_le_normalizer _)) inferInstance)

omit [IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U)] in
private theorem localAction_apply (hn : H ≤ normalizer (U : Set G))
    (hz : H ≤ centralizer (Z : Set G)) (a : H) (u : U) :
    localAction H U Z hn hz a (QuotientGroup.mk' (Z.subgroupOf U) u) =
      QuotientGroup.mk' (Z.subgroupOf U)
        ⟨(a : G) * (u : G) * (a : G)⁻¹,
          (mem_normalizer_iff.mp (hn a.property) u).mp u.property⟩ :=
  Classical.choose_spec (exists_quotient_conjugation_action H U Z hn
    (hz.trans (centralizer_le_normalizer _)) inferInstance) a u

omit [IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U)] in
private theorem core_killed (hn : H ≤ normalizer (U : Set G))
    (hz : H ≤ centralizer (Z : Set G)) (hc : ⁅U, Source.QH H⁆ ≤ Z) :
    pCore 2 H ≤ (localAction H U Z hn hz).ker := by
  have hk := quotient_conjugation_action_kills_commutator_layer H U Z (Source.QH H)
    inferInstance hn hc (localAction H U Z hn hz) (localAction_apply H U Z hn hz)
  intro a ha
  exact hk (mem_map_of_mem H.subtype ha)

/-- Conjugation on the literal central section, descended through the actual two-core. -/
noncomputable def quotientAction (hn : H ≤ normalizer (U : Set G))
    (hz : H ≤ centralizer (Z : Set G)) (hc : ⁅U, Source.QH H⁆ ≤ Z) :
    Source.Hstar H →* MulAut (U ⧸ Z.subgroupOf U) :=
  QuotientGroup.lift (pCore 2 H) (localAction H U Z hn hz)
    (fun _ ha => core_killed H U Z hn hz hc ha)

/-- Canonical binary conjugation representation on U/Z. -/
noncomputable def representation (hn : H ≤ normalizer (U : Set G))
    (hz : H ≤ centralizer (Z : Set G)) (hc : ⁅U, Source.QH H⁆ ≤ Z) :
    Representation (ZMod 2) (Source.Hstar H) (Additive (U ⧸ Z.subgroupOf U)) where
  toFun a := (quotientAction H U Z hn hz hc a).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext v
    change Additive.ofMul (quotientAction H U Z hn hz hc 1 v.toMul) = v
    rw [map_one]
    rfl
  map_mul' a b := by
    ext v
    change Additive.ofMul (quotientAction H U Z hn hz hc (a * b) v.toMul) = _
    rw [map_mul]
    rfl

/-- The canonical projection into the additive form of the actual group quotient. -/
public def projection : U →* Multiplicative (Additive (U ⧸ Z.subgroupOf U)) where
  toFun u := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u))
  map_one' := by change QuotientGroup.mk' (Z.subgroupOf U) 1 = 1; exact map_one _
  map_mul' u v := by
    change QuotientGroup.mk' (Z.subgroupOf U) (u * v) = _
    exact map_mul _ _ _

/-- Realize the checked section API on the literal quotient, using only the source
normalization, centrality, elementary-abelian and two-core commutator facts. -/
public noncomputable def canonicalSection (hU : U ≤ H) (hn : H ≤ normalizer (U : Set G))
    (hz : H ≤ centralizer (Z : Set G)) (hZU : Z ≤ U) (hc : ⁅U, Source.QH H⁆ ≤ Z) :
    ConjugationSection H U Z (representation H U Z hn hz hc) where
  le := hU
  normalizes := hn
  centralizes := hz
  line_le := hZU
  quotient := projection U Z
  surjective := QuotientGroup.mk'_surjective (Z.subgroupOf U)
  kernel := QuotientGroup.ker_mk' (Z.subgroupOf U)
  conjugates a u := by
    change Additive.ofMul (quotientAction H U Z hn hz hc _
      (QuotientGroup.mk' (Z.subgroupOf U) u)) = _
    change Additive.ofMul (localAction H U Z hn hz a
      (QuotientGroup.mk' (Z.subgroupOf U) u)) = _
    exact congrArg Additive.ofMul (localAction_apply H U Z hn hz a u)


open FourStructure.CriticalTransfer Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {H U Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) V}
  (s : ConjugationSection H U Z ρ)

/-- The preimage in U of an actual subspace of U/Z, viewed inside G. -/
public def preimage (W : Submodule (ZMod 2) V) : Subgroup G :=
  ((W.toAddSubgroup.toSubgroup).comap s.quotient).map U.subtype

theorem mem_preimage (W : Submodule (ZMod 2) V) (u : U) :
    (u : G) ∈ preimage s W ↔ (s.quotient u).toAdd ∈ W := by
  change (u : G) ∈ (((W.toAddSubgroup.toSubgroup).comap s.quotient).map U.subtype) ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, he⟩
    exact (Subtype.ext he : v = u) ▸ hv
  · intro hu
    exact ⟨u, hu, rfl⟩

theorem image_preimage (W : Submodule (ZMod 2) V) : s.image (preimage s W) = W := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (mem_preimage s W u).mp hu
  · intro hv
    obtain ⟨u, hu⟩ := s.surjective (Multiplicative.ofAdd v)
    refine ⟨u, (mem_preimage s W u).mpr ?_, ?_⟩
    · rw [hu]; exact hv
    · exact congrArg Multiplicative.toAdd hu

theorem image_le_iff (I : Subgroup G) (hIU : I ≤ U) (W : Submodule (ZMod 2) V) :
    s.image I ≤ W ↔ I ≤ preimage s W := by
  constructor
  · intro h x hx
    exact (mem_preimage s W ⟨x, hIU hx⟩).mpr (h ⟨⟨x,hIU hx⟩, hx, rfl⟩)
  · rintro h v ⟨u, hu, rfl⟩
    exact (mem_preimage s W u).mp (h hu)

private theorem image_bot : s.image ⊥ = ⊥ := by
  apply le_bot_iff.mp
  rintro v ⟨u, hu, rfl⟩
  have hu1 : u = 1 := Subtype.ext hu
  rw [hu1, map_one]
  rfl

/-- The image of the genuine centralizer is fixed. Equality needs additional
information: quotienting a centralizer does not automatically preserve fixed points. -/
theorem centralizer_image_le (E : Subgroup G) :
    s.image (U ⊓ centralizer (E : Set G)) ≤ fixedSpace ρ (Source.starImage H E) := by
  intro v hv a
  have hcomm : ⁅E, U ⊓ centralizer (E : Set G)⁆ ≤ ⊥ := by
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer.mpr inf_le_right]
  have hc := s.displacement_mem _ E ⊥ hcomm a a.property v hv
  rw [image_bot s] at hc
  exact sub_eq_zero.mp hc

include s in
theorem central_line_le_centralizer (E : Subgroup G) (hE : E ≤ H) :
    Z ≤ U ⊓ centralizer (E : Set G) :=
  le_inf s.line_le (le_centralizer_iff.mp (hE.trans s.centralizes))

theorem centralizer_le_critical (E L : Subgroup G) :
    U ⊓ centralizer (E : Set G) ≤ Source.DH U E L := by
  apply le_commutatorPreimage inf_le_left
  exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le

include s in
/-- The group equality in 13.8.21(4) forces a nontrivial K-action on every
proper quotient. This is proved for the actual conjugation section. -/
theorem quotient_nontrivial_of_full_commutator (K : Subgroup G) (hK : K ≤ H)
    (hfull : ⁅U, K⁆ = U) (W : Subrepresentation ρ) (hW : W.toSubmodule ≠ ⊤) :
    ∃ k ∈ Source.starImage H K, ∃ q : V ⧸ W.toSubmodule,
      W.quotientRepresentation k q ≠ q := by
  by_contra hn
  push Not at hn
  have hc : ⁅K, U⁆ ≤ preimage s W.toSubmodule := by
    apply commutator_le.mpr
    intro k hk u hu
    let kH : H := ⟨k, hK hk⟩
    let uU : U := ⟨u, hu⟩
    apply (mem_preimage s W.toSubmodule
      ⟨⁅k,u⁆, s.commutator_mem kH uU⟩).mpr
    rw [← s.displacement kH uU]
    exact (Submodule.Quotient.eq _).mp
      (hn _ (mem_map_of_mem _ hk) (W.toSubmodule.mkQ (s.quotient uU).toAdd))
  have hU : U ≤ preimage s W.toSubmodule := by
    rwa [commutator_comm, hfull] at hc
  apply hW
  apply top_unique
  intro v _
  obtain ⟨u, hu⟩ := s.surjective (Multiplicative.ofAdd v)
  have hm := (mem_preimage s W.toSubmodule u).mp (hU u.property)
  rwa [hu] at hm

include s in
/-- The faithfulness deduction before 13.8.22: the source simple generalized
Fitting subgroup lies in every nontrivial normal subgroup; its action on W
is supplied and its action on the quotient follows from 13.8.21(4). -/
theorem faithful_source_sections (K : Subgroup G) (hK : K ≤ H)
    (hfull : ⁅U, K⁆ = U) (W : Subrepresentation ρ) (hW : W.toSubmodule ≠ ⊤)
    (hmonolith : ∀ N : Subgroup (Source.Hstar H), N.Normal → N ≠ ⊥ →
      Source.starImage H K ≤ N)
    (hKW : ∃ k ∈ Source.starImage H K, ∃ w : W.toSubmodule,
      W.toRepresentation k w ≠ w) :
    Function.Injective W.toRepresentation ∧ Function.Injective W.quotientRepresentation :=
  ⟨faithful_of_nontrivial_on_monolith _ _ hmonolith hKW,
    faithful_of_nontrivial_on_monolith _ _ hmonolith
      (quotient_nontrivial_of_full_commutator s K hK hfull W hW)⟩

variable [Finite G] [FiniteDimensional (ZMod 2) V]

omit [Finite G] in
/-- The faithful sections of 13.8.22 exclude every transvection on Ũ_H.
Apply this to the transvection witness of case (1) of the original 13.8.8
dichotomy; all clauses of its other branch remain available unchanged. -/
theorem no_transvection_of_faithful_sections (W : Subrepresentation ρ)
    (hW : Function.Injective W.toRepresentation)
    (hQ : Function.Injective W.quotientRepresentation) (a : Source.Hstar H) :
    fixedCodim ρ (zpowers a) ≠ 1 := by
  intro he
  have hn : zpowers a ≠ ⊥ := by
    intro hbot
    have hz := (fixedCodim_eq_zero_iff ρ (zpowers a)).mpr
      (by rw [hbot, fixedSpace_bot])
    omega
  have := faithful_sections_fixedCodim_ge_two ρ W hW hQ hn
  omega


/-- Nonfixation forces the order-two critical subgroup to be the actual group
commutator. It also identifies its nonzero image with the linear commutator.
This implication precedes any orthogonal centralizer-index calculation. -/
theorem critical_commutator_of_nonfixed (E L : Subgroup G) (hE : E ≤ H)
    (hUL : U ≤ normalizer (L : Set G)) (hL : Nat.card L = 2)
    (hnonfixed : ¬ s.image (Source.DH U E L) ≤ fixedSpace ρ (Source.starImage H E)) :
    ⁅Source.DH U E L, E⁆ = L ∧ L ≤ U ∧ IsAtom (s.image L) ∧
      subspaceCommutator ρ (s.image (Source.DH U E L)) (Source.starImage H E) = s.image L := by
  have hbound := commutator_commutatorPreimage_le U E L hUL
  have hne : ⁅Source.DH U E L, E⁆ ≠ ⊥ := by
    intro heq
    apply hnonfixed
    intro v hv a
    have hc := s.displacement_mem (Source.DH U E L) E ⊥
      (by rw [commutator_comm, heq]) a a.property v hv
    rw [image_bot s] at hc
    exact sub_eq_zero.mp hc
  have heq : ⁅Source.DH U E L, E⁆ = L := by
    have hd : Nat.card (⁅Source.DH U E L, E⁆ : Subgroup G) ∣ 2 := by
      rw [← hL]
      exact card_dvd_of_le hbound
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact (hne (card_eq_one.mp h1)).elim
    · exact eq_of_le_of_card_ge hbound (by rw [hL, h2])
  have hLU : L ≤ U := by
    rw [← heq]
    exact (commutator_mono (commutatorPreimage_le U E L) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hE.trans s.normalizes))
  obtain ⟨hdim, hdisp⟩ := s.critical_line_displacement E L hUL hL
  have hc_le : subspaceCommutator ρ (s.image (Source.DH U E L))
      (Source.starImage H E) ≤ s.image L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, x, hx, rfl⟩
    exact hdisp a ha x hx
  have hc_eq := subspaceCommutator_eq_of_le_one_dimensional ρ
    (s.image (Source.DH U E L)) (s.image L) (Source.starImage H E) hnonfixed hc_le hdim
  have hS : s.image L ≠ ⊥ := by
    intro he
    exact hnonfixed ((subspaceCommutator_eq_bot_iff _ _ _).mp (hc_eq.trans he))
  have hpos := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.mpr hS)
  simp only [finrank_bot] at hpos
  exact ⟨heq, hLU, Submodule.isAtom_iff_finrank_eq_one.mpr (by omega), hc_eq⟩

/-- Construct the actual critical subspace and the image of L ∩ U. The source
13.8.8 inequality is transported through the genuine quotient kernel Z. -/
theorem critical_linear_data (E L : Subgroup G) (hE : E ≤ H)
    (hUL : U ≤ normalizer (L : Set G)) (hL : Nat.card L = 2)
    (hindex : Nat.log 2 ((Source.DH U E L).relIndex U) ≤ rank (Source.starImage H E)) :
    Module.finrank (ZMod 2) (V ⧸ s.image (Source.DH U E L)) ≤ rank (Source.starImage H E) ∧
      Module.finrank (ZMod 2) (s.image L) ≤ 1 ∧
      (∀ a ∈ Source.starImage H E, ∀ x ∈ s.image (Source.DH U E L),
        ρ a x - x ∈ s.image L) := by
  obtain ⟨hS, hdisp⟩ := s.critical_line_displacement E L hUL hL
  refine ⟨?_, hS, hdisp⟩
  rwa [s.quotient_finrank _ (s.line_le_DH E L hE)]



/-- Linear data on the actual section used by the rank-one orthogonal argument.
The last alternative is the full fixed-space and strict-centralizer conclusion,
with containment tested in the genuine preimage subgroup of W. -/
structure RankOneData (W : Subrepresentation ρ) (E F L : Subgroup G) : Prop where
  submodule_faithful : Function.Injective W.toRepresentation
  quotient_faithful : Function.Injective W.quotientRepresentation
  actor_ne_bot : Source.starImage H E ≠ ⊥
  actor_lt : Source.starImage H E < Source.starImage H F
  fixedCodim_eq_two : fixedCodim ρ (Source.starImage H E) = 2
  submodule_transvections : fixedCodim W.toRepresentation (Source.starImage H E) = 1
  quotient_transvections : fixedCodim W.quotientRepresentation (Source.starImage H E) = 1
  fixedSpace_eq : s.image (U ⊓ centralizer (E : Set G)) = fixedSpace ρ (Source.starImage H E)
  fixedSpace_submodule :
    (s.image (U ⊓ centralizer (E : Set G))).comap W.toSubmodule.subtype =
      fixedSpace W.toRepresentation (Source.starImage H E)
  fixedSpace_quotient :
    (s.image (U ⊓ centralizer (E : Set G))).map W.toSubmodule.mkQ =
      fixedSpace W.quotientRepresentation (Source.starImage H E)
  line_commutator : ⁅Source.DH U E L, E⁆ = L
  line_le : L ≤ U
  line_atom : IsAtom (s.image L)
  displacements : ∀ b ∈ Source.starImage H F, ∀ c ∈ fixedSpace ρ (Source.starImage H E),
    ρ b c - c ∈ s.image L
  centralizer_alternative :
    (L ≤ preimage s W.toSubmodule ∧
      fixedSpace W.quotientRepresentation (Source.starImage H E) ≤
        fixedSpace W.quotientRepresentation (Source.starImage H F) ∧
      Source.starImage H E < subspaceKernel W.quotientRepresentation
        (fixedSpace W.quotientRepresentation (Source.starImage H E)) ⊤) ∨
    (¬ L ≤ preimage s W.toSubmodule ∧
      fixedSpace W.toRepresentation (Source.starImage H E) ≤
        fixedSpace W.toRepresentation (Source.starImage H F) ∧
      Source.starImage H E < subspaceKernel W.toRepresentation
        (fixedSpace W.toRepresentation (Source.starImage H E)) ⊤)

/-- Transport the two hyperplanes in 13.8.23(1) and the actual centralizer
commutator from 13.7.3(7). Faithful sections force equality of fixed spaces;
nonfixation of the critical hyperplane then makes the source image an atom.
The larger actor is proved strict using 13.8.18(4), not assumed to be an
arbitrary subgroup of a linear model. -/
theorem rank_one_transport (W : Subrepresentation ρ) (E F L : Subgroup G)
    (hE : E ≤ H) (hEF : E ≤ F)
    (hUL : U ≤ normalizer (L : Set G)) (hL : Nat.card L = 2)
    (hW : Function.Injective W.toRepresentation)
    (hQ : Function.Injective W.quotientRepresentation)
    (hE_rank : rank (Source.starImage H E) = 1)
    (hF_rank : 1 < rank (Source.starImage H F))
    (hD_index : (Source.DH U E L).relIndex U = 2)
    (hC_index : (U ⊓ centralizer (E : Set G)).relIndex (Source.DH U E L) = 2)
    (hC_comm : ⁅U ⊓ centralizer (E : Set G), F⁆ ≤ L) :
    RankOneData s W E F L := by
  let A := Source.starImage H E
  let B := Source.starImage H F
  let C := U ⊓ centralizer (E : Set G)
  let D := Source.DH U E L
  have hA : A ≠ ⊥ := by
    intro he
    have hh : rank A = 1 := hE_rank
    rw [he, Representation.BinaryOffender.rank_bot] at hh
    omega
  have hABle : A ≤ B := map_mono (fun _ hx => hEF hx)
  have hAB : A < B := lt_of_le_of_ne hABle (by
    intro he
    change 1 < rank B at hF_rank
    rw [← he] at hF_rank
    change rank A = 1 at hE_rank
    omega)
  have hC_total : C.relIndex U = 4 := by
    rw [← relIndex_mul_relIndex C D U (centralizer_le_critical E L)
      (commutatorPreimage_le U E L)]
    change (U ⊓ centralizer (E : Set G)).relIndex (Source.DH U E L) *
      (Source.DH U E L).relIndex U = 4
    rw [hC_index, hD_index]
  have hC_dim : Module.finrank (ZMod 2) (V ⧸ s.image C) = 2 := by
    rw [s.quotient_finrank C (central_line_le_centralizer s E hE), hC_total]
    decide
  have hC_le := centralizer_image_le s E
  change s.image C ≤ fixedSpace ρ A at hC_le
  have hC_mono := Submodule.finrank_mono hC_le
  have hC_null := (s.image C).finrank_quotient_add_finrank
  have hfix_null := fixedCodim_add_finrank ρ A
  have hsmall : fixedCodim ρ A ≤ 2 := by omega
  obtain ⟨hWt, hQt, htotal⟩ := faithful_sections_of_fixedCodim_le_two ρ W hW hQ hA hsmall
  have hC_eq : s.image C = fixedSpace ρ A :=
    Submodule.eq_of_le_of_finrank_eq hC_le (by omega)
  have hD_dim : Module.finrank (ZMod 2) (V ⧸ s.image D) = 1 := by
    rw [s.quotient_finrank D (s.line_le_DH E L hE)]
    change Nat.log 2 ((Source.DH U E L).relIndex U) = 1
    rw [hD_index]
    decide
  have hD_notfixed : ¬ s.image D ≤ fixedSpace ρ A := by
    intro hle
    have hmono := Submodule.finrank_mono hle
    have hnull := (s.image D).finrank_quotient_add_finrank
    omega
  obtain ⟨hLcomm, hLU, hLatom, _⟩ := critical_commutator_of_nonfixed s E L hE hUL hL hD_notfixed
  have hdisplacements : ∀ b ∈ B, ∀ c ∈ fixedSpace ρ A, ρ b c - c ∈ s.image L := by
    rw [← hC_eq]
    exact s.displacement_mem C F L (by rw [commutator_comm]; exact hC_comm)
  have hfixedquot := fixedSpace_quotient_eq_map_of_fixedCodim_eq ρ W A (by omega)
  have hfixedsub : (s.image C).comap W.toSubmodule.subtype = fixedSpace W.toRepresentation A := by
    rw [hC_eq]
    ext w
    constructor
    · intro hw a
      exact Subtype.ext (hw a)
    · intro hw a
      exact congrArg Subtype.val (hw a)
  refine ⟨hW, hQ, hA, hAB, htotal, hWt, hQt, hC_eq, hfixedsub, ?_,
    hLcomm, hLU, hLatom, hdisplacements, ?_⟩
  · rw [hC_eq]
    exact hfixedquot
  · have hc := faithful_sections_centralizer_sieve ρ W (s.image L) hLatom hW hQ
      hA hAB hsmall hdisplacements
    rcases hc with ⟨hSW, hfix, hlt⟩ | ⟨hSW, hfix, hlt⟩
    · exact Or.inl ⟨(image_le_iff s L hLU W.toSubmodule).mp hSW, hfix, hlt⟩
    · exact Or.inr ⟨fun h => hSW ((image_le_iff s L hLU W.toSubmodule).mpr h), hfix, hlt⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.SourceTransport
