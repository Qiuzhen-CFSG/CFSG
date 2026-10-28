module

public import Theory.Alternating.proposition_5_2_7_8
public import Theory.Representation.HexacodeAction.Cover
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Odd central covers of alternating groups

For a component of a finite group with trivial two-core, its center has odd
order: the two-core descends along its subnormal chain, and a central
involution would generate a normal two-subgroup. Schur universality bounds
the center by two outside degrees six and seven, and by six in those two
degrees. Oddness leaves only the trivial and order-three kernels.

Triple-cover uniqueness identifies the degree-six case with the concrete
even hexacode automorphism group. In degree seven we construct a carrier by
quotienting the actual universal cover by the Sylow two-subgroup of its
central kernel. Its projection, center of order three and central quotient
are proved here, as is the isomorphism from every triple cover to this carrier.
These results do not make any representation-theoretic FF exclusion.

Sources: Gorenstein–Lyons–Solomon, volume 3, Theorem 5.2.3;
Aschbacher–Smith, *The Classification of Quasithin Groups*, I.1.3 and the
alternating-cover reduction in B.1.13, printed pp. 73–74 and 407.
The hexacode carrier and its source attribution are in
`Theory.Representation.HexacodeAction.Cover`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory GLS3.Chapter5 GLS3.Chapter5.SchurPresentation
namespace GLS3.Chapter5.OddCentralCovers

private theorem center_odd_of_twoCore_eq_bot (M : Type*) [Group M] [Finite M]
    (h2 : pCore 2 M = ⊥) : Odd (Nat.card (center M)) := by
  by_contra hodd
  have hd : 2 ∣ Nat.card (center M) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center M) 2 hd
  let X := (zpowers z).map (center M).subtype
  have hXc : X ≤ center M := map_subtype_le _
  let : X.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hXc hx) g, mul_inv_cancel_right]
    exact hx⟩
  have hXp : IsPGroup 2 X := by
    apply IsPGroup.of_card (n := 1)
    simp only [X, card_map_of_injective (center M).subtype_injective,
      Nat.card_zpowers, hz, pow_one]
  have hle : X ≤ pCore 2 M := le_sSup ⟨inferInstance, hXp⟩
  have hz1 : (z : M) = 1 := (h2 ▸ hle) (mem_map_of_mem _ (mem_zpowers z))
  have : z = 1 := Subtype.ext hz1
  simp [this] at hz

/-- A component has odd center when the ambient two-core is trivial. -/
theorem component_center_odd {G : Type*} [Group G] [Finite G]
    (hcore : pCore 2 G = ⊥) (L : Subgroup G) (hL : IsComponent G L) :
    Odd (Nat.card (center L)) := by
  apply center_odd_of_twoCore_eq_bot L
  rw [pCore_subnormal_eq_comap 2 hL.1, hcore, MonoidHom.comap_bot]
  exact (MonoidHom.ker_eq_bot_iff L.subtype).mpr L.subtype_injective

/-- The nonexceptional Schur multiplier bounds the center of every cover. -/
theorem center_card_dvd_two_of_nonexceptional
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (m : ℕ) (hm : 5 ≤ m) (hm6 : m ≠ 6) (hm7 : m ≠ 7)
    (e : L ⧸ center L ≃* alternatingGroup (Fin m)) :
    Nat.card (center L) ∣ 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm 5 n] at e hm6 hm7
  let f : Covering L (alternatingGroup (Fin (n + 5))) := {
    toMonoidHom := alternatingQuotientHom e
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective (center L)) }
  have hk : f.toMonoidHom.ker = center L := by
    ext l
    simp [f, alternatingQuotientHom]
  have hd := Covering.coveringKernel_card_dvd_of_universal
    (schurAlternatingCovering n) (theorem_5_2_3_b_universality n hm6 hm7) f
  rwa [hk, theorem_5_2_3_a] at hd

/-- An odd center is trivial, except possibly for a cubic center in degrees six and seven. -/
theorem odd_center_alternatives
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (m : ℕ) (hm : 5 ≤ m) (e : L ⧸ center L ≃* alternatingGroup (Fin m))
    (hodd : Odd (Nat.card (center L))) :
    Nat.card (center L) = 1 ∨
      ((m = 6 ∨ m = 7) ∧ Nat.card (center L) = 3) := by
  by_cases he : m = 6 ∨ m = 7
  · have hd := exceptional_alternating_center_card_dvd_six m e he
    have hc : Nat.card (center L) ∣ 3 := hodd.coprime_two_right.dvd_of_dvd_mul_left
      (by simpa using hd)
    exact (Nat.prime_three.eq_one_or_self_of_dvd _ hc).imp_right (fun h => ⟨he, h⟩)
  · have hd := center_card_dvd_two_of_nonexceptional m hm
      (fun h => he (Or.inl h)) (fun h => he (Or.inr h)) e
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with h | h
    · exact Or.inl h
    · rw [h] at hodd
      norm_num at hodd

/-- The actual alternating isomorphism when the center is trivial. -/
def alternatingEquivOfCenterCardOne
    {L : Type*} [Group L] (m : ℕ)
    (e : L ⧸ center L ≃* alternatingGroup (Fin m))
    (hc : Nat.card (center L) = 1) : L ≃* alternatingGroup (Fin m) :=
  QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ((eq_bot_iff_card _).mpr hc).symm).trans e)

private theorem triple_cover_equiv
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    {U D T : Type} [Group U] [Finite U] [IsQuasisimple U]
    [Group D] [Finite D] [IsQuasisimple D] [Group T] [Finite T] [IsQuasisimple T]
    (fu : Covering U D) (hu : Covering.IsUniversal.{0, 0, 0} fu)
    (hcyc : IsCyclic fu.toMonoidHom.ker) (hcard : Nat.card fu.toMonoidHom.ker = 6)
    (f : Covering L D) (fT : Covering T D)
    (hc : Nat.card f.toMonoidHom.ker = 3) (hT : Nat.card fT.toMonoidHom.ker = 3) :
    Nonempty (L ≃* T) := by
  obtain ⟨S, iS, finS, ⟨s⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{_, 0} L
  let := iS
  let := finS
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv s
  let fS := f.comp (Covering.ofMulEquiv s.symm)
  have hcS : Nat.card fS.toMonoidHom.ker = 3 := by
    rw [← hc]
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨s.symm x, x.property⟩
      invFun := fun x => ⟨s x, by change f (s.symm (s x)) = 1; rw [s.symm_apply_apply]; exact x.property⟩
      left_inv := fun x => Subtype.ext (s.apply_symm_apply x)
      right_inv := fun x => Subtype.ext (s.symm_apply_apply x) }
  obtain ⟨q, _, _⟩ := coveringIso_of_cyclic_kernel_card_six_of_kernel_card_three
    fu hu hcyc hcard fS fT hcS hT
  exact ⟨s.trans q⟩

/-- Every perfect central triple cover of A₆ is the concrete even hexacode group. -/
theorem triple_six_equiv_hexacode
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (e : L ⧸ center L ≃* alternatingGroup (Fin 6))
    (hc : Nat.card (center L) = 3) :
    Nonempty (L ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  let := Representation.Hexacode.even_isQuasisimple
  let fhex : Covering Atlas.Codes.HexEvenAutomorphisms (alternatingGroup (Fin 6)) := {
    toMonoidHom := Atlas.Codes.hexEvenCoordinate
    surjective := Atlas.Codes.hexEvenCoordinate_surjective }
  let f : Covering L (alternatingGroup (Fin 6)) := {
    toMonoidHom := alternatingQuotientHom e
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective (center L)) }
  have hk : f.toMonoidHom.ker = center L := by
    ext l
    simp [f, alternatingQuotientHom]
  obtain ⟨U, iU, finU, qU, fu, hu, hcyc, hcard⟩ := theorem_5_2_3_c_multiplier_a6
  let := iU
  let := finU
  let := qU
  exact triple_cover_equiv fu hu hcyc hcard f fhex (hk ▸ hc) Atlas.Codes.hexEven_kernel_card

/-- The central subgroup of order two in the universal cover of A₇. -/
@[expose] def sevenCentralTwo : Subgroup (AlternatingFreeCentralDerived 2) :=
  ((default : Sylow 2 (alternatingFreeCentralCovering 2).toMonoidHom.ker) :
    Subgroup (alternatingFreeCentralCovering 2).toMonoidHom.ker).map
      (alternatingFreeCentralCovering 2).toMonoidHom.ker.subtype

private theorem sevenCentralTwo_le_ker :
    sevenCentralTwo ≤ (alternatingFreeCentralCovering 2).toMonoidHom.ker := map_subtype_le _

instance sevenCentralTwo_normal : sevenCentralTwo.Normal := ⟨fun x hx g => by
  have hc := (alternatingFreeCentralCovering 2).ker_le_center (sevenCentralTwo_le_ker hx)
  rw [mem_center_iff.mp hc g, mul_inv_cancel_right]
  exact hx⟩

/-- The subgroup removed from the universal cover has exactly two elements. -/
theorem sevenCentralTwo_card : Nat.card sevenCentralTwo = 2 := by
  rw [sevenCentralTwo, card_map_of_injective (alternatingFreeCentralCovering 2).toMonoidHom.ker.subtype_injective,
    Sylow.card_eq_multiplicity, a7UniversalKernel_card_eq_six a7UniversalKernel_three_dvd_new]
  rw [show Nat.factorization 6 2 = 1 from by decide +kernel]
  norm_num

/-- The genuine triple cover of A₇, as an explicit quotient of its universal cover. -/
abbrev TripleSeven := AlternatingFreeCentralDerived 2 ⧸ sevenCentralTwo

/-- The projection from the constructed triple cover onto A₇. -/
@[expose] def tripleSevenProjection : TripleSeven →* alternatingGroup (Fin 7) :=
  QuotientGroup.lift sevenCentralTwo (alternatingFreeCentralCovering 2).toMonoidHom
    (by exact sevenCentralTwo_le_ker)

/-- The projection onto A₇ is surjective. -/
theorem tripleSevenProjection_surjective : Function.Surjective tripleSevenProjection :=
  QuotientGroup.lift_surjective_of_surjective _ _ (alternatingFreeCentralCovering 2).surjective _

instance tripleSeven_isQuasisimple : IsQuasisimple TripleSeven := by
  let : Nontrivial (alternatingGroup (Fin 7)) :=
    (alternatingGroup.isSimpleGroup (by simp)).toNontrivial
  let : Nontrivial TripleSeven := tripleSevenProjection_surjective.nontrivial
  exact IsQuasisimple.of_surjective (QuotientGroup.mk' sevenCentralTwo)
    (QuotientGroup.mk'_surjective _)

/-- The constructed group is a covering of A₇ in the finite quasisimple sense. -/
@[expose] def tripleSevenCovering : Covering TripleSeven (alternatingGroup (Fin 7)) where
  toMonoidHom := tripleSevenProjection
  surjective := tripleSevenProjection_surjective

/-- The constructed covering has kernel of order three. -/
theorem tripleSevenCovering_kernel_card : Nat.card tripleSevenCovering.toMonoidHom.ker = 3 := by
  have h := card_comap_mul (QuotientGroup.mk' sevenCentralTwo)
    (QuotientGroup.mk'_surjective _) tripleSevenProjection.ker
  have he : tripleSevenProjection.ker.comap (QuotientGroup.mk' sevenCentralTwo) =
      (alternatingFreeCentralCovering 2).toMonoidHom.ker := by
    ext x
    rfl
  rw [he, QuotientGroup.ker_mk', sevenCentralTwo_card,
    a7UniversalKernel_card_eq_six a7UniversalKernel_three_dvd_new] at h
  change Nat.card tripleSevenProjection.ker = 3
  have h' : Nat.card tripleSevenProjection.ker * 2 = 3 * 2 := h.symm
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) h'

/-- The center of the constructed triple cover has order three. -/
theorem tripleSeven_center_card : Nat.card (center TripleSeven) = 3 := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  rw [← tripleSevenCovering.ker_eq_center_of_isSimple]
  exact tripleSevenCovering_kernel_card

/-- The literal central quotient of the constructed carrier is A₇. -/
def tripleSevenQuotientCenterEquiv :
    TripleSeven ⧸ center TripleSeven ≃* alternatingGroup (Fin 7) := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  exact (QuotientGroup.quotientMulEquivOfEq
    tripleSevenCovering.ker_eq_center_of_isSimple.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective tripleSevenProjection tripleSevenProjection_surjective)

/-- Every perfect central triple cover of A₇ is isomorphic to the constructed carrier. -/
theorem triple_seven_equiv
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (e : L ⧸ center L ≃* alternatingGroup (Fin 7))
    (hc : Nat.card (center L) = 3) : Nonempty (L ≃* TripleSeven) := by
  let f : Covering L (alternatingGroup (Fin 7)) := {
    toMonoidHom := alternatingQuotientHom e
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective (center L)) }
  have hk : f.toMonoidHom.ker = center L := by
    ext l
    simp [f, alternatingQuotientHom]
  exact triple_cover_equiv (alternatingFreeCentralCovering 2)
    (alternatingFreeCentralCovering_isUniversal 2) a7UniversalKernel_isCyclic
    (a7UniversalKernel_card_eq_six a7UniversalKernel_three_dvd_new)
    f tripleSevenCovering (hk ▸ hc) tripleSevenCovering_kernel_card

/-- The three genuine covering alternatives for a component with alternating central quotient. -/
theorem component_alternating_cover_alternatives
    {G : Type*} [Group G] [Finite G]
    (hcore : pCore 2 G = ⊥) (L : Subgroup G) (hL : IsComponent G L)
    (m : ℕ) (hm : 5 ≤ m) (e : L ⧸ center L ≃* alternatingGroup (Fin m)) :
    Nonempty (L ≃* alternatingGroup (Fin m)) ∨
      (m = 6 ∧ Nonempty (L ≃* Atlas.Codes.HexEvenAutomorphisms)) ∨
      (m = 7 ∧ Nat.card (center L) = 3 ∧ Nonempty (L ≃* TripleSeven)) := by
  let := hL.2
  rcases odd_center_alternatives m hm e (component_center_odd hcore L hL) with hc | ⟨hm, hc⟩
  · exact Or.inl ⟨alternatingEquivOfCenterCardOne m e hc⟩
  · rcases hm with rfl | rfl
    · exact Or.inr (Or.inl ⟨rfl, triple_six_equiv_hexacode e hc⟩)
    · exact Or.inr (Or.inr ⟨rfl, hc, triple_seven_equiv e hc⟩)

end GLS3.Chapter5.OddCentralCovers
