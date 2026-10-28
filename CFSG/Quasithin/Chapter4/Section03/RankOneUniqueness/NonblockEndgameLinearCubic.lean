module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSetup
public import Theory.GroupTheory.Commutator.CommutingConjugation
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.PRegularLift
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.CharacteristicCoreCenter

/-!
# The original cubic subgroup in the linear-four nonblock branch

A nontrivial scalar in the common SL₃(4) marking lifts through O₂(K) to
an element of order three in the original O₂,Z(K). The natural section U
and the two dual sections of Q/U show that its fixed subgroup on Q is
trivial. Coprime action then gives [Q,X] = Q.

Scalar conjugation commutes with the original K-action on U. It therefore
preserves W = [U,L] and the literal root C_W(S ∩ L). Since the root is
nontrivial, the cubic acts faithfully on it. It normalizes the secondary
solvable residual and centralizes its quotient by its own two-core. The
same construction bounds the size of its fixed subgroup on the actual R₂
by the relative index of Q.

The final theorem constructs this entire family from MSData and the chosen
module. It supplies the source choice of X; it does not identify XK_Z/O₂(K_Z)
or its representation extension. Construction of MSData and SecondaryData,
and the terminal contradiction, remain with the nonblock source assembly
`qt-d-1222-rankone-uniqueness-nonblock`.

Source: Aschbacher–Smith, conclusion of original 4.3.2, printed pp.618–619,
with the natural and doubled-dual structure in C.1.34(3), printed p.137.
The initial scalar-lift calculation adapts the saved draft from the absorbed
`qt-d-1222-nonblock-endgame-linear-four` task.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface


namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {c : SourceConfiguration T L}

omit [Finite G] in private theorem odd_lift_cube (x : K c) (ho : ¬ 2 ∣ orderOf x)
    (hx : x ^ 3 ∈ pCore 2 (K c)) : x ^ 3 = 1 := by
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := K c)) ⟨x ^ 3, hx⟩
  have hd : orderOf (x ^ 3) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((Nat.prime_two.coprime_iff_not_dvd.mpr ho).pow_left k)
    hd (orderOf_pow_dvd 3))

theorem MSData.exists_cubic_scalar (d : MSData c 2) :
    ∃ (x : K c) (ω : d.field.Carrier),
      orderOf x = 3 ∧ ω ≠ 1 ∧ ω ^ 3 = 1 ∧
      (linearThreeActor d.model x).val = Matrix.scalar (Fin 3) ω ∧
      (x : G) ∈ (K c).coreCenterIn 2 := by
  have hF : Nat.card d.field.Carrier = 4 := by
    rw [d.field.card_eq, d.degree_eq]
    norm_num
  have hu : Nat.card d.field.Carrierˣ = 3 := by rw [Nat.card_units, hF]
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := d.field.Carrierˣ) 3
    (by rw [hu])
  have hω3 : (ω : d.field.Carrier) ^ 3 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, hω] using
      congrArg Units.val (pow_orderOf_eq_one ω)
  have hω1 : (ω : d.field.Carrier) ≠ 1 := by
    intro he
    have : ω = 1 := Units.ext he
    simp [this] at hω
  let z : Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier :=
    ⟨Matrix.scalar (Fin 3) (ω : d.field.Carrier), by simpa using hω3⟩
  have hz3 : z ^ 3 = 1 := by
    apply Subtype.ext
    change (Matrix.scalar (Fin 3) (ω : d.field.Carrier)) ^ 3 = 1
    rw [← map_pow, hω3, map_one]
  have hz1 : z ≠ 1 := by
    intro he
    have he' := congrArg (fun a : Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier => a 0 0) he
    exact hω1 (by simpa [z] using he')
  have hzorder : orderOf z = 3 :=
    orderOf_eq_prime_iff.mpr ⟨hz3, hz1⟩
  have hs : Function.Surjective (linearThreeActor d.model) :=
    d.model.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨x, ho, hx⟩ := (linearThreeActor d.model).exists_pRegular_lift hs
    2 Nat.prime_two z (by rw [hzorder]; decide)
  have hx3 : x ^ 3 = 1 := by
    apply odd_lift_cube x ho
    apply (QuotientGroup.eq_one_iff _).mp
    apply d.model.injective
    change linearThreeActor d.model (x ^ 3) = d.model 1
    rw [map_pow, hx, hz3, map_one]
  have hx1 : x ≠ 1 := by intro he; exact hz1 (by simpa [he] using hx.symm)
  refine ⟨x, ω, orderOf_eq_prime_iff.mpr ⟨hx3, hx1⟩,
    hω1, hω3, congrArg Subtype.val hx, ?_⟩
  refine ⟨x, ?_, rfl⟩
  intro k
  apply (QuotientGroup.eq_one_iff _).mp
  apply d.model.injective
  change linearThreeActor d.model ⁅x,k⁆ = d.model 1
  rw [map_commutatorElement, hx, map_one]
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_center_iff.mp
      (Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨(ω : d.field.Carrier), by simpa [Fintype.card_fin] using hω3, rfl⟩)
      (linearThreeActor d.model k)).symm)

private theorem natural_scalar {F : Type*} [Field F]
    (a : Matrix.SpecialLinearGroup (Fin 3) F) (ω : F)
    (ha : a.val = Matrix.scalar (Fin 3) ω) (v : Fin 3 → F) :
    Representation.specialLinearNatural 3 a v = ω • v := by
  rw [Representation.specialLinearNatural_apply, ha]
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

private theorem natural_fixed_zero {F : Type*} [Field F]
    (a : Matrix.SpecialLinearGroup (Fin 3) F) (ω : F) (hω : ω ≠ 1)
    (ha : a.val = Matrix.scalar (Fin 3) ω) (v : Fin 3 → F)
    (hv : Representation.specialLinearNatural 3 a v = v) : v = 0 := by
  rw [natural_scalar a ω ha] at hv
  have h : (ω - 1) • v = 0 := by rw [sub_smul, one_smul, hv, sub_self]
  exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hω)

private theorem dual_fixed_zero {F : Type*} [Field F]
    (a : Matrix.SpecialLinearGroup (Fin 3) F) (ω : F) (hω : ω ≠ 1)
    (ha : a.val = Matrix.scalar (Fin 3) ω) (f : Module.Dual F (Fin 3 → F))
    (hf : (Representation.specialLinearNatural 3).dual a f = f) : f = 0 := by
  apply LinearMap.ext
  intro v
  have h := LinearMap.congr_fun hf (Representation.specialLinearNatural 3 a v)
  change f (Representation.specialLinearNatural 3 a⁻¹
    (Representation.specialLinearNatural 3 a v)) = _ at h
  rw [Representation.inv_self_apply, natural_scalar a ω ha, map_smul] at h
  have hz : (ω - 1) * f v = 0 := by
    change f v = ω * f v at h
    rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hω)

omit [Finite G] in
private theorem section_fixed_mem_bottom {F A V : Type*} [Field F] [Group A]
    [AddCommGroup V] [Module F V] {J B E : Subgroup G}
    {actor : J →* A} {ρ : Representation F A V}
    (h : HasSectionModel J B E actor ρ) (x : J)
    (hfix : ∀ v : V, ρ (actor x) v = v → v = 0)
    {b : G} (hb : b ∈ B) (hc : x * b * (x : G)⁻¹ = b) : b ∈ E := by
  obtain ⟨_, _, _, hn, e, he⟩ := h
  let := hn
  let b' : B := ⟨b, hb⟩
  have hf := he x b' b' hc.symm
  have hz := hfix _ hf.symm
  have hz' : e (QuotientGroup.mk' _ b') = 1 :=
    Multiplicative.toAdd.injective hz
  have heq : QuotientGroup.mk' _ b' = 1 := e.injective (hz'.trans e.map_one.symm)
  exact (QuotientGroup.eq_one_iff b').mp heq

omit [Finite G] in
/-- A nonidentity scalar in the original quotient fixes no element of Q.
This uses both literal sections U and Q/U with their common marking. -/
theorem MSData.core_fixed_scalar (d : MSData c 2) (x : K c)
    (ω : d.field.Carrier) (hω : ω ≠ 1)
    (hx : (linearThreeActor d.model x).val = Matrix.scalar (Fin 3) ω) :
    Q c ⊓ Subgroup.centralizer (zpowers (x : G) : Set G) = ⊥ := by
  apply bot_unique
  intro b hb
  have hc : (x : G) * b * (x : G)⁻¹ = b := by
    have he := (mem_centralizer_iff.mp hb.2) (x : G) (mem_zpowers _)
    exact mul_inv_eq_iff_eq_mul.mpr he
  have hbU : b ∈ U c := section_fixed_mem_bottom d.doubleDual x
    (fun v hv => Prod.ext
      (dual_fixed_zero _ ω hω hx v.1 (congrArg Prod.fst hv))
      (dual_fixed_zero _ ω hω hx v.2 (congrArg Prod.snd hv))) hb.1 hc
  exact section_fixed_mem_bottom d.natural x
    (natural_fixed_zero _ ω hω hx) hbU hc

/-- The cubic required on printed p.618 lies in the actual O₂,Z(K),
and has trivial fixed subgroup on the original commutator core. -/
theorem MSData.exists_source_cubic (d : MSData c 2) :
    ∃ X : Subgroup G, Nat.card X = 3 ∧ X ≤ (K c).coreCenterIn 2 ∧
      Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
  obtain ⟨x, ω, hx, hω, _, he, hz⟩ := d.exists_cubic_scalar
  refine ⟨zpowers (x : G), ?_, zpowers_le.mpr hz, MSData.core_fixed_scalar d x ω hω he⟩
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]


omit [Finite G] in
private theorem MSData.natural_coordinates (d : MSData c 2) :
    ∃ e : U c ≃* Multiplicative (Fin 3 → d.field.Carrier),
      ∀ (k : K c) (u u' : U c), (u' : G) = k * (u : G) * (k : G)⁻¹ →
        Multiplicative.toAdd (e u') =
          Representation.specialLinearNatural 3 (linearThreeActor d.model k)
            (Multiplicative.toAdd (e u)) := by
  have hm := d.natural
  rw [HasSectionModel, bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,e,he⟩ := hm
  let := hn
  exact ⟨QuotientGroup.quotientBot.symm.trans e, he⟩

omit [Finite G] in
private theorem MSData.scalar_conj_compatible (d : MSData c 2) (x : K c)
    (ω : d.field.Carrier)
    (hx : (linearThreeActor d.model x).val = Matrix.scalar (Fin 3) ω) :
    ∀ l ∈ K c, ∀ u ∈ U c,
      (MulAut.conj (x : G)) (l * u * l⁻¹) = l * (MulAut.conj (x : G)) u * l⁻¹ := by
  obtain ⟨e,he⟩ := d.natural_coordinates
  let a : K c →* MulAut (U c) :=
    (U c).normalizerMonoidHom.comp (inclusion d.natural.2.1)
  have ha (k : K c) (u : U c) : (a k u : G) = k * (u : G) * (k : G)⁻¹ :=
    normalizerMonoidHom_apply_apply_coe (U c) ⟨k,d.natural.2.1 k.property⟩ u
  have hc (k : K c) (u : U c) := he k u (a k u) (ha k u)
  intro l hl u hu
  let l' : K c := ⟨l,hl⟩
  let u' : U c := ⟨u,hu⟩
  have hh : a x (a l' u') = a l' (a x u') := by
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [hc x, natural_scalar _ ω hx, hc l', hc l', hc x, natural_scalar _ ω hx,
      map_smul]
  have hg := congrArg (fun v : U c => (v : G)) hh
  simpa only [ha, l', u', MulAut.conj_apply] using hg

omit [Finite G] in
/-- The chosen central scalar preserves the full source module [U,L]. -/
theorem MSData.scalar_fullModule_normalized (d : MSData c 2) (x : K c)
    (ω : d.field.Carrier)
    (hx : (linearThreeActor d.model x).val = Matrix.scalar (Fin 3) ω) :
    (x : G) ∈ normalizer (W c : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [← d.fullModule]
  exact map_commutator_eq_of_conj_compatible (U c) L (MulAut.conj (x : G))
    (mem_normalizer_iff_map_conj_eq.mp (d.natural.2.1 x.property))
    (fun l hl => d.scalar_conj_compatible x ω hx l (c.le_component hl))

omit [Finite G] in
/-- The cubic scalar normalizes the literal root, including its Sylow fixed condition. -/
theorem MSData.scalar_root_normalized (d : MSData c 2) (x : K c)
    (ω : d.field.Carrier)
    (hx : (linearThreeActor d.model x).val = Matrix.scalar (Fin 3) ω) :
    (x : G) ∈ rootNormalizer c := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hWU : W c ≤ U c := by
    rw [← d.fullModule]
    exact le_normalizer_iff_commutator_le_left.mp
      (c.le_component.trans d.natural.2.1)
  exact map_inf_centralizer_eq_of_conj_compatible (U c) (S c ⊓ L) (W c)
    (MulAut.conj (x : G)) hWU
    (mem_normalizer_iff_map_conj_eq.mp (d.scalar_fullModule_normalized x ω hx))
    (fun l hl => d.scalar_conj_compatible x ω hx l (c.le_component hl.2))


/-- The source cubic generates the whole original commutator core by coprime
commutators, since its fixed subgroup there is trivial. -/
theorem MSData.cubic_core_moved (d : MSData c 2) (X : Subgroup G)
    (hX : Nat.card X = 3) (hXK : X ≤ K c)
    (hfix : Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥) : ⁅Q c,X⁆ = Q c := by
  have hQ : IsPGroup 2 (Q c) :=
    (isPGroup_pCoreIn 2 (K c)).to_le
      (le_normalizer_iff_commutator_le_left.mp ((K c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K c) (pCore 2 (K c)))))
  have hcop : Nat.Coprime (Nat.card X) (Nat.card (Q c)) := by
    obtain ⟨m,hm⟩ := hQ.exists_card_eq
    rw [hX,hm]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  let : Group.IsNilpotent (Q c) := hQ.isNilpotent
  have he := eq_commutator_sup_centralizer_of_solvable_coprime (Q c) X
    (hXK.trans d.doubleDual.2.1) inferInstance hcop
  simpa only [hfix,sup_bot_eq] using he.symm

/-- The cubic fixed subgroup of R₂ has order at most the relative index of Q.
Distinct fixed elements occupy distinct Q-cosets because C_Q(X) is trivial. -/
theorem cubic_radical_fixed_card_le {X : Subgroup G}
    (hfix : Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    Nat.card (R₂ c ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤
      (Q c).relIndex (R₂ c) := by
  let C := R₂ c ⊓ Subgroup.centralizer (X : Set G)
  have hd : Disjoint (Q c) C := disjoint_iff.mpr (bot_unique
    ((inf_le_inf_left _ inf_le_right).trans_eq hfix))
  have hb : (Q c).subgroupOf C = ⊥ := subgroupOf_eq_bot.mpr hd
  have hh := (Q c).relIndex_le_of_le_right (show C ≤ R₂ c from inf_le_left)
    (Subgroup.FiniteIndex.index_ne_zero (H := (Q c).subgroupOf (R₂ c)))
  simpa only [relIndex, hb, index_bot] using hh

omit [Finite G] in
/-- A subgroup of the original K preserving the root also preserves its literal
secondary solvable residual. -/
theorem original_normalizes_secondary {X : Subgroup G}
    (hX : X ≤ K c) (hr : X ≤ rootNormalizer c) :
    X ≤ normalizer (secondary c : Set G) := by
  have hn : X ≤ normalizer (K c ⊓ Subgroup.centralizer (root c : Set G) : Set G) :=
    (le_inf (hX.trans (K c).le_normalizer)
      (hr.trans (normalizer_le_normalizer_centralizer (root c)))).trans
      inf_normalizer_le_normalizer_inf
  exact hn.trans (normalizer_le_normalizer_characteristic_image
    (K c ⊓ Subgroup.centralizer (root c : Set G))
    (solvableResidual (K c ⊓ Subgroup.centralizer (root c : Set G) : Subgroup G)))

omit [Finite G] in
/-- The central scalar lift acts trivially on K₂/O₂(K₂), with the original
secondary group and its intrinsic core. -/
theorem original_coreCenter_secondary_commutator {X : Subgroup G}
    (hX : X ≤ (K c).coreCenterIn 2) (hr : X ≤ rootNormalizer c) :
    ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2 := by
  have hsec : secondary c ≤ K c := (map_subtype_le _).trans inf_le_left
  have hn := original_normalizes_secondary (hX.trans (coreCenterIn_le 2 (K c))) hr
  have hcore : ⁅secondary c,X⁆ ≤ (K c).pCoreIn 2 := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro x hx k hk
    exact ((mem_coreCenterIn_iff 2 (K c) x).mp (hX hx)).2 k (hsec hk)
  exact (le_inf (le_normalizer_iff_commutator_le_left.mp hn) hcore).trans
    (inf_pCoreIn_le_of_le 2 hsec)

private theorem prime_actor_faithful_on_root (d : MSData c 2)
    {V : Subgroup G} (D : Chapter12.Section02.ChosenModule T L V)
    (X : Subgroup G) (hX : Nat.card X = 3)
    (hfix : Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    X ⊓ Subgroup.centralizer (root c : Set G) = ⊥ := by
  have hWU : W c ≤ U c := by
    rw [← d.fullModule]
    exact le_normalizer_iff_commutator_le_left.mp
      (c.le_component.trans d.natural.2.1)
  have hrQ : root c ≤ Q c := inf_le_left.trans (hWU.trans (map_subtype_le _))
  let : Fact (Nat.card X).Prime := ⟨hX ▸ Nat.prime_three⟩
  rcases ((X ⊓ Subgroup.centralizer (root c : Set G)).subgroupOf X).eq_bot_or_eq_top_of_prime_card with hz | ht
  · have hm := congrArg (fun A : Subgroup X => A.map X.subtype) hz
    simpa only [map_subgroupOf_eq_of_le inf_le_left, Subgroup.map_bot] using hm
  · have hc : X ≤ Subgroup.centralizer (root c : Set G) := by
      intro x hx
      have hh : (⟨x,hx⟩ : X) ∈
          (X ⊓ Subgroup.centralizer (root c : Set G)).subgroupOf X := ht.symm ▸ mem_top _
      exact hh.2
    exact (root_ne_bot c D (bot_unique
      ((le_inf hrQ (le_centralizer_iff.mp hc)).trans_eq hfix))).elim

/-- Construction and local placement of the source cubic subgroup in O₂,Z(K).
Its faithful root action separates it from K₂, and its K₂-action is trivial
modulo the actual two-core. This does not identify its action on K_Z. -/
theorem MSData.exists_source_cubic_root (d : MSData c 2)
    {V : Subgroup G} (D : Chapter12.Section02.ChosenModule T L V) :
    ∃ X : Subgroup G, Nat.card X = 3 ∧ X ≤ (K c).coreCenterIn 2 ∧
      X ≤ rootNormalizer c ∧ Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
      X ⊓ Subgroup.centralizer (root c : Set G) = ⊥ ∧
      X ⊓ secondary c = ⊥ ∧ X ≤ normalizer (secondary c : Set G) ∧
      ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2 ∧ ⁅Q c,X⁆ = Q c ∧
      Nat.card (R₂ c ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤
        (Q c).relIndex (R₂ c) := by
  obtain ⟨x,ω,hx,hω,_,he,hz⟩ := d.exists_cubic_scalar
  let X := zpowers (x : G)
  have hc : Nat.card X = 3 := by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hX : X ≤ (K c).coreCenterIn 2 := zpowers_le.mpr hz
  have hr : X ≤ rootNormalizer c := zpowers_le.mpr (d.scalar_root_normalized x ω he)
  have hf : Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥ := d.core_fixed_scalar x ω hω he
  have hfaith := prime_actor_faithful_on_root d D X hc hf
  refine ⟨X,hc,hX,hr,hf,hfaith,?_,
    original_normalizes_secondary (hX.trans (coreCenterIn_le 2 (K c))) hr,
    original_coreCenter_secondary_commutator hX hr,
    d.cubic_core_moved X hc (hX.trans (coreCenterIn_le 2 (K c))) hf,
    cubic_radical_fixed_card_le hf⟩
  exact bot_unique ((inf_le_inf_left _ ((map_subtype_le _).trans inf_le_right)).trans_eq hfaith)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
