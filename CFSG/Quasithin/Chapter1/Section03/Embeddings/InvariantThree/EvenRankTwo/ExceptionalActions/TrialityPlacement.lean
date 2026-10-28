module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.Geometry
public import Theory.SpecificGroups.Triality.BinaryParabolicThreeRank
public import Theory.SpecificGroups.Triality.ThreeOvergroupPlacement
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# Coordinate changes for three-complements in genuine triality

An actual isomorphism transports the proper solvable product RS to the standard
D₄ graph-field elementary central quotient. Once the positive subgroup is
proved Sylow, Sylow conjugacy marks S as that subgroup. Proper-parabolic
placement and the binary parabolic rank bounds then exclude the binary field.

For a complement already in the Borel, the concrete Borel product formula
makes the torus index a power of two. Sylow-three conjugacy inside the Borel
puts the complement in the torus; this conjugator preserves the positive
subgroup. Thus simultaneous coordinates require no additional automorphism
coverage or Hall-complement theorem. The torus is exactly the published
`CartanAction.torus`, the descended closure of the genuine coroot words.

The final assembly discharges the coordinate reductions using the concrete
Sylow, proper-parabolic, Borel and full-parabolic rank theorems. The complement
order bound required by overgroup placement follows from the source elementary
or extraspecial alternatives in `PairInput`. The resulting `geometric_restriction`
has no extra geometric premises. Field-action, automorphism and central-cover
arguments belong to the separate pair-reducibility assembly.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`);
GLS3 §§2.3–2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

open Subgroup
open scoped Pointwise
open Triality.Standard

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.ExceptionalActions.TrialityPlacement

private theorem conjugate_le_of_index {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (A H : Subgroup G) (hA : IsPGroup p A)
    (hH : ¬ p ∣ H.index) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ H := by
  classical
  let T : Sylow p H := default
  have hidx : ¬ p ∣ ((T : Subgroup H).map H.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul T.not_dvd_index hH
  let T' := (T.isPGroup'.map H.subtype).toSylow hidx
  obtain ⟨D, hAD⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G D T'
  refine ⟨g, ?_⟩
  have hm : (D : Subgroup G).map (MulAut.conj g).toMonoidHom = T' :=
    congrArg Sylow.toSubgroup hg
  have ht : (T' : Subgroup G) ≤ H := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  exact (Subgroup.map_mono hAD).trans (hm.le.trans ht)

private theorem conjugate_le_in {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (A H B : Subgroup G) (hA : IsPGroup p A)
    (hAB : A ≤ B) (hH : ¬ p ∣ H.relIndex B) :
    ∃ g ∈ B, A.map (MulAut.conj g).toMonoidHom ≤ H := by
  obtain ⟨g, hg⟩ := conjugate_le_of_index (A.subgroupOf B) (H.subgroupOf B)
    (hA.comap_of_injective B.subtype B.subtype_injective) hH
  refine ⟨g, g.property, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact hg (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom
    (show (⟨a, hAB ha⟩ : B) ∈ A.subgroupOf B from ha))

private theorem index_eq_card_of_product {G : Type*} [Group G]
    (U T B : Subgroup G) (hUB : U ≤ B) (hTB : T ≤ B)
    (hdis : Disjoint U T)
    (hprod : ∀ b ∈ B, ∃ u ∈ U, ∃ t ∈ T, b = u * t) :
    T.relIndex B = Nat.card U := by
  have hc : (U.subgroupOf B).IsComplement' (T.subgroupOf B) := by
    apply isComplement'_of_disjoint_and_mul_eq_univ
    · rw [Subgroup.disjoint_def]
      intro x hxU hxT
      exact Subtype.ext ((Subgroup.disjoint_def.mp hdis) hxU hxT)
    · apply Set.eq_univ_of_forall
      intro b
      obtain ⟨u, hu, t, ht, he⟩ := hprod b b.property
      exact Set.mem_mul.mpr ⟨⟨u, hUB hu⟩, hu, ⟨t, hTB ht⟩, ht, Subtype.ext he.symm⟩
  exact hc.index_eq_card.trans (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUB).toEquiv)

variable {Q : Type*} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}

/-- The proper solvable product is transported along the actual model isomorphism. -/
theorem mapped_product_facts (h : PairInput S R) (P : Parameters)
    (e : Q ≃* Carrier P) :
    Group.IsSolvable ((R ⊔ (S : Subgroup Q)).map e.toMonoidHom) ∧
      (R ⊔ (S : Subgroup Q)).map e.toMonoidHom ≠ ⊤ := by
  constructor
  · let _ := product_solvable h
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom.subgroupMap _)
      (e.toMonoidHom.subgroupMap_surjective _)
  · intro ht
    apply product_ne_top h
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [ht, Subgroup.map_top_of_surjective _ e.surjective]

/-- Sylow conjugacy gives positive-root coordinates once its two-group and
odd-index calculations have been established on the genuine carrier. -/
theorem sylow_coordinates (S : Sylow 2 Q) (P : Parameters)
    (e : Q ≃* Carrier P) (hU : IsPGroup 2 (Parabolics.unipotent P))
    (hidx : ¬ 2 ∣ (Parabolics.unipotent P).index) :
    ∃ e' : Q ≃* Carrier P,
      (S : Subgroup Q).map e'.toMonoidHom = Parabolics.unipotent P := by
  let U : Sylow 2 (Carrier P) := hU.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Carrier P)
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) U
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  change (S : Subgroup Q).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
  rw [← map_map]
  exact congrArg Sylow.toSubgroup hg

/-- The exact finite inputs to a model-specific three-overgroup placement
argument, after the Sylow subgroup has been put in positive-root coordinates. -/
theorem mapped_three_overgroup_inputs (h : PairInput S R) (P : Parameters)
    (e : Q ≃* Carrier P)
    (hS : (S : Subgroup Q).map e.toMonoidHom = Parabolics.unipotent P) :
    IsPGroup 3 (R.map e.toMonoidHom) ∧
      primeRank 3 (R.map e.toMonoidHom) = 2 ∧
      (R.map e.toMonoidHom : Set (Carrier P)) * (Parabolics.unipotent P : Set _) =
        (Parabolics.unipotent P : Set _) * (R.map e.toMonoidHom : Set _) ∧
      Group.IsSolvable (R.map e.toMonoidHom ⊔ Parabolics.unipotent P : Subgroup _) ∧
      R.map e.toMonoidHom ⊔ Parabolics.unipotent P ≠ ⊤ := by
  have hrank := Theory.GroupTheory.primeRank_equiv 3
    (Subgroup.equivMapOfInjective R e.toMonoidHom e.injective)
  have hperm := congrArg (fun A : Set Q => e.toMonoidHom '' A) h.permutes
  simp only [Set.image_mul, ← Sylow.coe_coe, ← Subgroup.coe_map, hS] at hperm
  have hfacts := mapped_product_facts h P e
  rw [Subgroup.map_sup, hS] at hfacts
  exact ⟨h.oddComplement.isPGroup.map e.toMonoidHom,
    hrank.symm.trans (complement_rank h), hperm, hfacts⟩

/-- Placement in either genuine small parabolic contradicts the complement's
three-rank. The rank bounds and placement remain separate geometric inputs. -/
theorem not_pair_of_parabolic_rank (h : PairInput S R) (P : Parameters)
    (hrank : ∀ a, primeRank 3 (Parabolics.parabolic P a) ≤ 1)
    (hplace : ∃ (e : Q ≃* Carrier P) (a : Parabolics.Node),
      R.map e.toMonoidHom ≤ Parabolics.parabolic P a) : False := by
  obtain ⟨e, a, hRa⟩ := hplace
  exact not_map_le_of_rank_le_one h e.toMonoidHom
    (e.injective.comp R.subtype_injective) (hrank a) hRa

/-- The binary obstruction turns positive binary degree into degree at least two. -/
theorem field_degree_ge_two_of_parabolic_rank (h : PairInput S R) (P : Parameters)
    (f : ℕ) (hf : 1 ≤ f) (hq : P.q = 2 ^ f)
    (hrank : P.q = 2 → ∀ a, primeRank 3 (Parabolics.parabolic P a) ≤ 1)
    (hplace : ∃ (e : Q ≃* Carrier P) (a : Parabolics.Node),
      R.map e.toMonoidHom ≤ Parabolics.parabolic P a) : 2 ≤ f := by
  by_contra hf2
  have hf1 : f = 1 := by omega
  have hq2 : P.q = 2 := by simpa only [hf1, pow_one] using hq
  exact not_pair_of_parabolic_rank h P (hrank hq2) hplace

/-- The Borel product formula computes the relative index of its actual torus. -/
theorem torus_relIndex_of_borel_geometry (P : Parameters)
    (hG : CartanAction.BorelGeometry P) :
    (CartanAction.torus P).relIndex (Parabolics.borel P) =
      Nat.card (Parabolics.unipotent P) :=
  index_eq_card_of_product _ _ _ (Parabolics.unipotent_le_borel P)
    (CartanAction.torus_le_borel P) hG.disjoint hG.product

omit [Finite Q] in
/-- A Borel conjugator puts a three-complement in the coroot torus while
preserving its marked Sylow subgroup. Only the torus index and normalization
are used, so the statement makes its exact geometric requirements explicit. -/
theorem torus_coordinates_of_borel_index (h : PairInput S R) (P : Parameters)
    (e : Q ≃* Carrier P)
    (hS : (S : Subgroup Q).map e.toMonoidHom = Parabolics.unipotent P)
    (hR : R.map e.toMonoidHom ≤ Parabolics.borel P)
    (hN : Parabolics.borel P ≤ normalizer (Parabolics.unipotent P))
    (hidx : ¬ 3 ∣ (CartanAction.torus P).relIndex (Parabolics.borel P)) :
    ∃ e' : Q ≃* Carrier P,
      (S : Subgroup Q).map e'.toMonoidHom = Parabolics.unipotent P ∧
      R.map e'.toMonoidHom ≤ CartanAction.torus P := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg, hRg⟩ := conjugate_le_in _ _ _
    (h.oddComplement.isPGroup.map e.toMonoidHom) hR hidx
  refine ⟨e.trans (MulAut.conj g), ?_, ?_⟩
  · change (S : Subgroup Q).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map, hS]
    exact mem_normalizer_iff_map_conj_eq.mp (hN hg)
  · change R.map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) ≤ _
    rw [← map_map]
    exact hRg

omit [Finite Q] in
/-- In the proved Borel product geometry the torus index is a power of two,
so the simultaneous coordinate change follows directly. -/
theorem torus_coordinates_of_borel_geometry (h : PairInput S R) (P : Parameters)
    (e : Q ≃* Carrier P)
    (hS : (S : Subgroup Q).map e.toMonoidHom = Parabolics.unipotent P)
    (hR : R.map e.toMonoidHom ≤ Parabolics.borel P)
    (hG : CartanAction.BorelGeometry P) :
    ∃ e' : Q ≃* Carrier P,
      (S : Subgroup Q).map e'.toMonoidHom = Parabolics.unipotent P ∧
      R.map e'.toMonoidHom ≤ CartanAction.torus P := by
  have hU : IsPGroup 2 (Parabolics.unipotent P) :=
    hS ▸ S.isPGroup'.map e.toMonoidHom
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  apply torus_coordinates_of_borel_index h P e hS hR hG.normalizer_eq.ge
  rw [torus_relIndex_of_borel_geometry P hG, hk]
  exact fun hdiv => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hdiv)

/-! The source geometric restriction, with all model inputs discharged. -/

omit [Finite Q] in
/-- The source complement catalogue supplies the order bound used by the
concrete overgroup theorem; this is stronger than the rank-two bound alone. -/
theorem mapped_complement_card_le (h : PairInput S R) (P : Parameters)
    (e : Q ≃* Carrier P) : Nat.card (R.map e.toMonoidHom) ≤ 27 := by
  rw [Subgroup.card_map_of_injective e.injective]
  rcases h.oddComplement with ⟨_, hc⟩ | ⟨_, hc, _⟩ <;> rw [hc] <;> decide

/-- The genuine positive subgroup is Sylow for every characteristic-two
parameter, so the initial model isomorphism can mark the given Sylow subgroup. -/
theorem sylow_coordinates_characteristic_two (S : Sylow 2 Q) (P : Parameters)
    (hp : P.prime = 2) (e : Q ≃* Carrier P) :
    ∃ e' : Q ≃* Carrier P,
      (S : Subgroup Q).map e'.toMonoidHom = Parabolics.unipotent P :=
  sylow_coordinates S P e (Parabolics.unipotent_isPGroup_binary P hp)
    (Parabolics.unipotentSylow P hp).not_dvd_index

/-- In positive-root coordinates, the entire solvable product lies in one
of the two proper genuine root parabolics. All placement premises are discharged. -/
theorem mapped_product_le_proper_parabolic (h : PairInput S R) (P : Parameters)
    (f : ℕ) (hf : 1 ≤ f) (hq : P.q = 2 ^ f) (e : Q ≃* Carrier P)
    (hS : (S : Subgroup Q).map e.toMonoidHom = Parabolics.unipotent P) :
    ∃ a : Parabolics.Node,
      R.map e.toMonoidHom ⊔ Parabolics.unipotent P ≤ Parabolics.parabolic P a ∧
      Parabolics.parabolic P a ≠ ⊤ := by
  have hP := P.eq_binaryParameters_of_q_eq f hf hq
  subst P
  obtain ⟨hA, hrank, hperm, hsolv, hproper⟩ := mapped_three_overgroup_inputs h _ e hS
  exact ThreeOvergroupPlacement.le_proper_parabolic f hf _ hA hrank
    (mapped_complement_card_le h _ e) hperm hsolv hproper

/-- Choose Sylow coordinates and place the whole product in a proper
parabolic, including at the binary endpoint. -/
theorem proper_parabolic_coordinates (h : PairInput S R) (P : Parameters)
    (f : ℕ) (hf : 1 ≤ f) (hq : P.q = 2 ^ f) (e : Q ≃* Carrier P) :
    ∃ (e' : Q ≃* Carrier P) (a : Parabolics.Node),
      (S : Subgroup Q).map e'.toMonoidHom = Parabolics.unipotent P ∧
      R.map e'.toMonoidHom ⊔ Parabolics.unipotent P ≤ Parabolics.parabolic P a ∧
      Parabolics.parabolic P a ≠ ⊤ := by
  have hp : P.prime = 2 := by
    rw [P.eq_binaryParameters_of_q_eq f hf hq]
    rfl
  obtain ⟨e', hS⟩ := sylow_coordinates_characteristic_two S P hp e
  obtain ⟨a, ha, hproper⟩ := mapped_product_le_proper_parabolic h P f hf hq e' hS
  exact ⟨e', a, hS, ha, hproper⟩

/-- A pair cannot occur in the genuine binary triality carrier: its rank-two
three-complement would embed in a full parabolic of three-rank at most one. -/
theorem not_pair_of_q_eq_two (h : PairInput S R) (P : Parameters)
    (hq : P.q = 2) (e : Q ≃* Carrier P) : False := by
  obtain ⟨e', a, _, ha, _⟩ :=
    proper_parabolic_coordinates h P 1 (by decide) (by simpa only [pow_one] using hq) e
  exact not_pair_of_parabolic_rank h P
    (Parabolics.parabolic_threeRank_le_one_of_q_eq_two P hq)
    ⟨e', a, le_sup_left.trans ha⟩

/-- The binary parabolic obstruction excludes degree one without any
extra placement or rank hypothesis. -/
theorem field_degree_ge_two (h : PairInput S R) (P : Parameters)
    (f : ℕ) (hf : 1 ≤ f) (hq : P.q = 2 ^ f) (e : Q ≃* Carrier P) : 2 ≤ f := by
  by_contra hn
  have hf1 : f = 1 := by omega
  exact not_pair_of_q_eq_two h P (by simpa only [hf1, pow_one] using hq) e

/-- Above the binary endpoint, the marked solvable product is contained
in the genuine Borel subgroup. -/
theorem mapped_product_le_borel (h : PairInput S R) (P : Parameters)
    (f : ℕ) (hf : 2 ≤ f) (hq : P.q = 2 ^ f) (e : Q ≃* Carrier P)
    (hS : (S : Subgroup Q).map e.toMonoidHom = Parabolics.unipotent P) :
    R.map e.toMonoidHom ⊔ Parabolics.unipotent P ≤ Parabolics.borel P := by
  have hfpos : 0 < f := lt_of_lt_of_le (by decide : 0 < 2) hf
  have hP := P.eq_binaryParameters_of_q_eq f hfpos hq
  subst P
  obtain ⟨hA, hrank, hperm, hsolv, hproper⟩ := mapped_three_overgroup_inputs h _ e hS
  exact ThreeOvergroupPlacement.le_borel f hfpos hf _ hA hrank
    (mapped_complement_card_le h _ e) hperm hsolv hproper

/-- Simultaneously put the marked Sylow subgroup in the positive subgroup
and the three-complement in the actual descended coroot torus. -/
theorem torus_coordinates (h : PairInput S R) (P : Parameters)
    (f : ℕ) (hf : 1 ≤ f) (hq : P.q = 2 ^ f) (e : Q ≃* Carrier P) :
    ∃ e' : Q ≃* Carrier P,
      (S : Subgroup Q).map e'.toMonoidHom = Parabolics.unipotent P ∧
      R.map e'.toMonoidHom ≤ CartanAction.torus P := by
  have hf2 := field_degree_ge_two h P f hf hq e
  have hp : P.prime = 2 := by
    rw [P.eq_binaryParameters_of_q_eq f hf hq]
    rfl
  obtain ⟨e', hS⟩ := sylow_coordinates_characteristic_two S P hp e
  exact torus_coordinates_of_borel_geometry h P e' hS
    (le_sup_left.trans (mapped_product_le_borel h P f hf2 hq e' hS))
    (CartanAction.borelGeometry P hp)

/-- The geometric triality restriction from the proof of Proposition 1.3.4
(p.511): exclude the binary field and construct simultaneous Sylow, Borel and
Cartan coordinates. The torus is displayed as the exact descended closure of
coroot words. No geometric witness or complement-order bound remains assumed. -/
theorem geometric_restriction (h : PairInput S R) (P : Parameters)
    (f : ℕ) (hf : 1 ≤ f) (hq : P.q = 2 ^ f) (e : Q ≃* Carrier P) :
    2 ≤ f ∧ ∃ e' : Q ≃* Carrier P,
      (S : Subgroup Q).map e'.toMonoidHom = Parabolics.unipotent P ∧
      (R ⊔ (S : Subgroup Q)).map e'.toMonoidHom ≤ Parabolics.borel P ∧
      R.map e'.toMonoidHom ≤ Parabolics.descendSubgroup P
        (Subgroup.closure {g | ∃ i t, g = Parabolics.torusWord P i t}) := by
  obtain ⟨e', hS, hR⟩ := torus_coordinates h P f hf hq e
  refine ⟨field_degree_ge_two h P f hf hq e, e', hS, ?_, hR⟩
  rw [Subgroup.map_sup, hS]
  exact sup_le (hR.trans (CartanAction.torus_le_borel P)) (Parabolics.unipotent_le_borel P)


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.ExceptionalActions.TrialityPlacement
