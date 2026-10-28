module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryDerivedRoots
public import Theory.GroupTheory.CommutatorPreimageFrattini

/-!
# The actual central derived section of a unitary hexagon

Put V = U_sj, D = [V,V] and T = [D,V]. A class-two opposite
root makes U/V_i class two, so T lies in V_i. Conjugation by the
literal reflection s_j puts T in the intersection of both opposite
radicals, hence in the three-middle-root product. A nonzero opposite
root commutator lies in D and survives modulo T. Its reflection moves
it to a disjoint root, proving that R_j acts nontrivially on D/T.

For a regular unitary actor this gives |D/T| >= 2^(6n), and therefore
2^(6n)|T| <= |D|. If Phi(V) = D, then squares in V/T are central;
the derived subgroup of V/T is elementary abelian. The literal relative
quotient D/T is isomorphic to that subgroup. Consequently its effective
source denominator Phi(D)T(H intersect D) is exactly T. No normality in
the whole ambient group is asserted.

The CFSG companion supplies the actual SU3/PSU3 models in either
orientation and on the original/geometric Sylow image. Nontriviality
and the Cartan lower bound for T, the remaining unitary degree argument,
and the final (6D)/(6E) assembly remain further source obligations.

Source: Fong--Seitz I (6D), printed pp.42--43, using (3G), (4D), (5D).
-/

public noncomputable section
open Subgroup
open scoped Pointwise

private theorem triple_le_of_classTwo_complement {G : Type*} [Group G]
    (U A N : Subgroup G) (hAU : A ≤ U) (hNU : N ≤ U)
    (hN : U ≤ normalizer (N : Set G))
    (hprod : (U : Set G) = (A : Set G) * (N : Set G))
    (hclass : ⁅⁅A,A⁆,A⁆ = ⊥) : ⁅⁅U,U⁆,U⁆ ≤ N := by
  let K := N.subgroupOf U
  let : K.Normal := normal_subgroupOf_of_le_normalizer hN
  let π := QuotientGroup.mk' K
  let f := π.comp (inclusion hAU)
  have hf : Function.Surjective f := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H z =>
      have hz : (z : G) ∈ (A : Set G) * (N : Set G) := hprod ▸ z.property
      obtain ⟨a,ha,b,hb,hab⟩ := hz
      refine ⟨⟨a,ha⟩,?_⟩
      have he : z = inclusion hAU ⟨a,ha⟩ * (⟨b,hNU hb⟩ : U) := Subtype.ext hab.symm
      change π (inclusion hAU ⟨a,ha⟩) = π z
      rw [he,map_mul,show π (⟨b,hNU hb⟩ : U) = 1 from (QuotientGroup.eq_one_iff _).mpr hb,mul_one]
  have hA : ⁅⁅(⊤ : Subgroup A),(⊤ : Subgroup A)⁆,(⊤ : Subgroup A)⁆ = ⊥ := by
    apply Subgroup.map_injective (f := A.subtype) A.subtype_injective
    simpa only [map_commutator,←MonoidHom.range_eq_map,range_subtype,Subgroup.map_bot] using hclass
  have hquot : ⁅⁅(⊤ : Subgroup (U ⧸ K)),(⊤ : Subgroup (U ⧸ K))⁆,(⊤ : Subgroup (U ⧸ K))⁆ = ⊥ := by
    have he := congrArg (fun B : Subgroup A => B.map f) hA
    simpa only [map_commutator,←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr hf,Subgroup.map_bot] using he
  have hmap : (⁅⁅(⊤ : Subgroup U),(⊤ : Subgroup U)⁆,(⊤ : Subgroup U)⁆).map π = ⊥ := by
    simpa only [map_commutator,←MonoidHom.range_eq_map,show π.range = ⊤ from MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective K)] using hquot
  have hle : ⁅⁅(⊤ : Subgroup U),(⊤ : Subgroup U)⁆,(⊤ : Subgroup U)⁆ ≤ K := by
    intro u hu
    exact (QuotientGroup.eq_one_iff _).mp (mem_bot.mp (hmap ▸ mem_map_of_mem π hu))
  have hh := Subgroup.map_mono (f := U.subtype) hle
  change (⁅⁅(⊤ : Subgroup U),(⊤ : Subgroup U)⁆,(⊤ : Subgroup U)⁆).map U.subtype ≤ (N.subgroupOf U).map U.subtype at hh
  simpa only [map_commutator,←MonoidHom.range_eq_map,range_subtype,map_subgroupOf_eq_of_le hNU] using hh

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- A class-two canonical root makes the third commutator of U lie in its radical. -/
theorem unipotent_triple_le_remainder (i : Fin 2)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (hclass : ⁅⁅simpleRoot Q split i,simpleRoot Q split i⁆,simpleRoot Q split i⁆ = ⊥) :
    ⁅⁅split.U,split.U⁆,split.U⁆ ≤ simpleRemainder Q split i :=
  triple_le_of_classTwo_complement split.U (simpleRoot Q split i)
    (simpleRemainder Q split i) (simpleRoot_le Q split i) inf_le_left
    (split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
      (remainder_parabolic_normalizes Q split i hK)))
    (simpleRoot_mul_remainder Q split i).symm hclass

private theorem rightConjugate_commutators (A B : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) :
    rightConjugate ⁅A,B⁆ n = ⁅rightConjugate A n,rightConjugate B n⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]

/-- The actual third lower-central subgroup lies in the three literal middle roots. -/
theorem radical_triple_le_middle (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hclass : ⁅⁅simpleRoot Q split i,simpleRoot Q split i⁆,simpleRoot Q split i⁆ = ⊥) :
    ⁅⁅simpleRemainder Q split j,simpleRemainder Q split j⁆,simpleRemainder Q split j⁆ ≤
      middleRoots Q split i j := by
  let V := simpleRemainder Q split j
  let T := ⁅⁅V,V⁆,V⁆
  let s := representative (Q.simple j)
  have hT : T ≤ simpleRemainder Q split i :=
    (commutator_mono (commutator_mono inf_le_left inf_le_left) inf_le_left).trans
      (unipotent_triple_le_remainder Q split i hKi hclass)
  have hV : rightConjugate V (s : X ⧸ Q.D) = V := by
    dsimp only [V]
    rw [simpleRemainder,rightConjugate_inf,
      ←unipotentConjugate_eq split _ s (representative_spec _),
      unipotentConjugate_right split _ _ s (representative_spec _),
      show Q.simple j*Q.simple j = 1 from by
        simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem j)).2,
      unipotentConjugate_one,inf_comm]
  have hconj := comap_mono (f := (MulAut.conj (s : X ⧸ Q.D)).toMonoidHom) hT
  change rightConjugate T (s : X ⧸ Q.D) ≤ rightConjugate (simpleRemainder Q split i) (s : X ⧸ Q.D) at hconj
  dsimp only [T] at hconj
  rw [rightConjugate_commutators,rightConjugate_commutators,hV] at hconj
  rw [middleRoots_eq_intersection Q split hhex i j hij s (representative_spec _)]
  exact le_inf (le_inf ((commutator_mono (commutator_le_self V) le_rfl).trans
    (commutator_le_self V)) hT) hconj

/-- The actual third lower-central subgroup is stable under the source parabolic. -/
theorem radical_triple_normalized (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    Q.tits.standardParabolic {Q.simple j} ≤ normalizer
      ((⁅⁅simpleRemainder Q split j,simpleRemainder Q split j⁆,
        simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) : Set _) := by
  intro r hr
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (remainder_parabolic_normalizes Q split j hKj hr)]

/-- The actual relative quotient D/[D,V], with its rank-one conjugation action. -/
@[expose] def derivedCentralSection (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) : RootSection Q split j where
  numerator := ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆
  le_radical := commutator_le_self _
  normalized := (rankOne_le_parabolic Q split j).trans (radical_commutator_normalized Q split j hKj)
  denominator := (⁅⁅simpleRemainder Q split j,simpleRemainder Q split j⁆,
    simpleRemainder Q split j⁆).subgroupOf ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆
  normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left _ _)
  invariant r := by
    let D := ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆
    let T := ⁅D,simpleRemainder Q split j⁆
    have hn := radical_triple_normalized Q split j hKj ((rankOne_le_parabolic Q split j) r.property)
    apply le_antisymm
    · rintro x ⟨y,hy,rfl⟩
      exact (mem_normalizer_iff.mp hn _).mp hy
    · intro x hx
      let a := D.normalizerMonoidHom (inclusion
        ((rankOne_le_parabolic Q split j).trans (radical_commutator_normalized Q split j hKj)) r)
      refine ⟨a.symm x,?_,a.apply_symm_apply x⟩
      exact (mem_normalizer_iff.mp ((normalizer (T : Set (X ⧸ Q.D))).inv_mem hn) _).mp hx

/-- A nonzero opposite root commutator survives and is moved by the source reflection. -/
theorem derivedCentralSection_action_ne_one (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hclass : ⁅⁅simpleRoot Q split i,simpleRoot Q split i⁆,simpleRoot Q split i⁆ = ⊥)
    (hne : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ ≠ ⊥) :
    (derivedCentralSection Q split j hKj).action ≠ 1 := by
  obtain ⟨a,ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ha := a.property
  have ha1' : (a : X ⧸ Q.D) ≠ 1 := fun he => ha1 (Subtype.ext he)
  intro he
  apply reflection_moves_section Q split hhex i j hij (UnitarySource.actorReflection Q split j)
    (derivedCentralSection Q split j hKj) a ((commutator_le_self _) ha)
    (commutator_mono (simpleRoot_le_other_remainder Q split hhex i j hij)
      (simpleRoot_le_other_remainder Q split hhex i j hij) ha) ha1' ?_ (by rw [he]; rfl)
  rintro x ⟨y,hy,rfl⟩
  exact (middleRoots_le_other_remainder Q split hhex i j hij)
    (radical_triple_le_middle Q split hhex i j hij hKi hclass hy)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

open Subgroup RootCoordinates BenderSuzuki.MatrixGroups

/-- A uniform nontrivial lower-central bound is incompatible with a finite
nilpotent subgroup.  This is the abstract final step in the repeated
lower-central-series argument: source-specific work only has to show that
the same effective section (and hence a fixed cardinal lower bound) survives
at every lower-central term. -/
theorem lowerCentralSeries_card_contradiction
    {G : Type*} [Group G] [Finite G] (S : Subgroup G)
    [Group.IsNilpotent S] {c : ℕ} (hc : 2 ≤ c)
    (hcard : ∀ n : ℕ, c ≤ Nat.card (S.lowerCentralSeries n)) : False := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent S)
  have hn' : S.lowerCentralSeries n = ⊥ := by
    rw [← Subgroup.top_subtype_lowerCentralSeries, hn, Subgroup.map_bot]
  have h := hcard n
  rw [hn', card_eq_one.mpr rfl] at h
  omega

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
  {n : ℕ} (hn : 2 ≤ n) (hcardF : Nat.card F = (2^n)^2)
  (hconj : ∀ x, J.conj x = x^(2^n))
  (j : Fin 2) (σ : J.specialSubgroup →* rankOne Q split j)
  (hσ : Function.Surjective σ)

include J hn hcardF hconj σ hσ in
/-- A persistent family of moving unitary sections gives the uniform cardinal
bound required by the abstract lower-central contradiction.  The quotient
carrier can only be smaller than its numerator, so no assumption on the
section denominators is needed. -/
theorem unitary_lowerCentral_card_bound_of_persistent_sections
    (S : Subgroup (X ⧸ Q.D)) (sections : ℕ → RootSection Q split j)
    (hnum : ∀ k : ℕ, (sections k).numerator = S.lowerCentralSeries k)
    (hmove : ∀ k : ℕ, (sections k).action ≠ 1) :
    ∀ k : ℕ, 2^(6*n) ≤ Nat.card (S.lowerCentralSeries k) := by
  intro k
  have hb := unitary_section_card_bound Q split j J hn hcardF hconj σ hσ
    (sections k) (hmove k)
  have hq : Nat.card (sections k).EffectiveCarrier ≤
      Nat.card (sections k).numerator :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  rw [hnum k] at hq
  exact hb.trans hq

include J hn hcardF hconj σ hσ in
/-- The source-style persistence contract closes the finite unitary radical
branch once supplied by the composition-factor calculation. -/
theorem unitary_lowerCentral_persistent_sections_contradiction
    (S : Subgroup (X ⧸ Q.D)) (hS : S ≤ simpleRemainder Q split j)
    (sections : ℕ → RootSection Q split j)
    (hnum : ∀ k : ℕ, (sections k).numerator = S.lowerCentralSeries k)
    (hmove : ∀ k : ℕ, (sections k).action ≠ 1) : False := by
  have hc : 2 ≤ 2^(6*n) := by
    calc
      2 = 2^1 := by norm_num
      _ ≤ 2^(6*n) := Nat.pow_le_pow_right (by decide) (by omega)
  let : Fact (IsPGroup 2 S) := ⟨split.isTwo.to_le (hS.trans inf_le_left)⟩
  let : Group.IsNilpotent S := (split.isTwo.to_le (hS.trans inf_le_left)).isNilpotent
  exact lowerCentralSeries_card_contradiction S hc
    (unitary_lowerCentral_card_bound_of_persistent_sections Q split J hn hcardF hconj
      j σ hσ S sections hnum hmove)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates BenderSuzuki.MatrixGroups
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The third term is contained in the derived subgroup in the ambient group. -/
theorem radical_triple_le_derived (j : Fin 2) :
    ⁅⁅simpleRemainder Q split j,simpleRemainder Q split j⁆,simpleRemainder Q split j⁆ ≤
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ :=
  le_normalizer_iff_commutator_le_left.mp (normalizer_commutator_ge_left _ _)

/-- The unitary degree bound applies to D/[D,V], retaining the size of the third term. -/
theorem unitary_derived_mod_triple_card_bound
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hclass : ⁅⁅simpleRoot Q split i,simpleRoot Q split i⁆,simpleRoot Q split i⁆ = ⊥)
    (hne : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ ≠ ⊥) :
    2^(6*n) ≤ Nat.card (derivedCentralSection Q split j hKj).Carrier ∧
      2^(6*n)*Nat.card (⁅⁅simpleRemainder Q split j,simpleRemainder Q split j⁆,
        simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) ≤
        Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) := by
  let d := derivedCentralSection Q split j hKj
  have hb := unitary_section_card_bound Q split j J hn hcard hconj σ hσ d
    (derivedCentralSection_action_ne_one Q split hhex i j hij hKi hKj hclass hne)
  have hc : 2^(6*n) ≤ Nat.card d.Carrier := hb.trans (index_antitone (by
    rw [d.effectiveDenominator_eq]; exact le_sup_right))
  refine ⟨hc,?_⟩
  have hprod := d.denominator.index_mul_card
  have he : Nat.card d.denominator =
      Nat.card (⁅⁅simpleRemainder Q split j,simpleRemainder Q split j⁆,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) :=
    Nat.card_congr (subgroupOfEquivOfLe (radical_triple_le_derived Q split j)).toEquiv
  change Nat.card d.Carrier * Nat.card d.denominator = Nat.card d.numerator at hprod
  change 2^(6*n) * _ ≤ Nat.card d.numerator
  rw [←he]
  exact (Nat.mul_le_mul_right _ hc).trans_eq hprod

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

open scoped commutatorElement IsMulCommutative

private theorem elementary_derived_of_central_squares {G : Type*} [Group G]
    (hc : _root_.commutator G ≤ center G) (hsq : ∀ g : G, g^2 ∈ center G) :
    IsElementaryAbelian 2 (_root_.commutator G) := by
  let : IsMulCommutative (_root_.commutator G) := ⟨⟨fun a b => Subtype.ext
    ((mem_center_iff.mp (hc a.property) b).symm)⟩⟩
  let K := (powMonoidHom 2 : center G →* center G).ker.map (center G).subtype
  have hle : _root_.commutator G ≤ K := by
    change ⁅(⊤ : Subgroup G),(⊤ : Subgroup G)⁆ ≤ K
    apply commutator_le.mpr
    intro a _ b _
    have hm := hc (commutator_mem_commutator (mem_top a) (mem_top b))
    have hb : ⁅a^2,b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      ((mem_center_iff.mp (hsq a) b).symm)
    have hpow : ⁅a,b⁆^2=1 := by
      rw [pow_two,commutatorElement_mul_left_eq_conj_mul,mem_center_iff.mp hm a] at hb
      simpa only [mul_inv_cancel_right,←pow_two] using hb
    exact ⟨⟨⁅a,b⁆,hm⟩,Subtype.ext hpow,rfl⟩
  refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
  intro x
  obtain ⟨z,hz,he⟩ := hle x.property
  apply Subtype.ext
  have hh := congrArg Subtype.val (show z^2=1 from hz)
  change (z : G)^2=1 at hh
  change (z : G) = (x : G) at he
  change (x : G)^2=1
  simpa only [he] using hh

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- When Phi(V) = V′, the literal central derived quotient is elementary abelian. -/
theorem derivedCentralSection_elementary (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hPhi : frattini (simpleRemainder Q split j) = _root_.commutator (simpleRemainder Q split j)) :
    IsElementaryAbelian 2 (derivedCentralSection Q split j hKj).Carrier := by
  let V := simpleRemainder Q split j
  let D := ⁅V,V⁆
  let T := ⁅D,V⁆
  let K := T.subgroupOf V
  let : K.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_right _ _)
  let π := QuotientGroup.mk' K
  let f : D →* V ⧸ K := π.comp (inclusion (commutator_le_self V))
  have hD : (D.subgroupOf V).map π = _root_.commutator (V ⧸ K) := by
    have he : D.subgroupOf V = _root_.commutator V := by
      dsimp only [D]
      rw [←map_subtype_commutator,subgroupOf,comap_map_eq_self_of_injective V.subtype_injective]
    rw [he,map_commutator_eq,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective K)]
    rfl
  have hrange : f.range = _root_.commutator (V ⧸ K) := by
    rw [MonoidHom.range_comp]
    have hi : (inclusion (commutator_le_self V)).range = D.subgroupOf V := by
      ext x
      constructor
      · rintro ⟨y,rfl⟩; exact y.property
      · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
    rw [hi,hD]
  have hcomm : _root_.commutator (V ⧸ K) ≤ center (V ⧸ K) := by
    rw [←commutator_top_right_eq_bot_iff_le_center,←hD]
    have hm : ⁅D.subgroupOf V,(⊤ : Subgroup V)⁆ ≤ K := by
      rintro x hx
      have hh := mem_map_of_mem V.subtype hx
      rw [map_commutator,map_subgroupOf_eq_of_le (commutator_le_self V),
        ←MonoidHom.range_eq_map,range_subtype] at hh
      exact hh
    have hh := map_mono (f := π) hm
    rw [map_commutator,←MonoidHom.range_eq_map,
      show π.range = ⊤ from MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective K)] at hh
    apply bot_unique
    apply hh.trans
    rintro x ⟨v,hv,rfl⟩
    exact mem_bot.mpr ((QuotientGroup.eq_one_iff _).mpr hv)
  have hsquare : ∀ x : V ⧸ K, x^2 ∈ center (V ⧸ K) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
      have hx : x^2 ∈ _root_.commutator V := hPhi ▸ pth_power_mem_frattini_of_isPGroup (p := 2) x
      apply hcomm
      have hh := mem_map_of_mem π hx
      rw [map_commutator_eq,show π.range = ⊤ from MonoidHom.range_eq_top.mpr
        (QuotientGroup.mk'_surjective K)] at hh
      exact hh
  have he := elementary_derived_of_central_squares hcomm hsquare
  have hr : IsElementaryAbelian 2 f.range := hrange ▸ he
  let d := derivedCentralSection Q split j hKj
  have hker : f.ker = d.denominator := by
    ext x
    exact QuotientGroup.eq_one_iff _
  let : f.ker.Normal := MonoidHom.normal_ker f
  let : (d.denominator : Subgroup D).Normal := d.normal
  let e₁ : (D ⧸ d.denominator) ≃* (D ⧸ f.ker) :=
    @QuotientGroup.quotientMulEquivOfEq D _ d.denominator f.ker d.normal (MonoidHom.normal_ker f) hker.symm
  let e : d.Carrier ≃* f.range := e₁.trans (QuotientGroup.quotientKerEquivRange f)
  exact hr.of_injective e.toMonoidHom e.injective

/-- The source effective denominator is exactly the actual third lower-central subgroup. -/
theorem derivedCentralSection_effectiveDenominator (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hPhi : frattini (simpleRemainder Q split j) = _root_.commutator (simpleRemainder Q split j)) :
    (derivedCentralSection Q split j hKj).effectiveDenominator =
      (derivedCentralSection Q split j hKj).denominator := by
  let d := derivedCentralSection Q split j hKj
  have he := derivedCentralSection_elementary Q split j hKj hPhi
  rw [d.effectiveDenominator_eq,sup_eq_right]
  exact frattini_le_of_elementary_quotient d.isTwo d.denominator he

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
