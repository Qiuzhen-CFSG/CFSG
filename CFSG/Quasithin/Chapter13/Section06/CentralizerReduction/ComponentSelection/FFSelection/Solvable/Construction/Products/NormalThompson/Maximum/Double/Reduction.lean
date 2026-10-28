module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Normality
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Witness
public import Theory.GroupTheory.ElementaryThompsonFrattini
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.Representation.BinaryOffender.GeneratedCore


/-!
# Maximum elementary witnesses from the two coordinate codimensions

The global elementary Thompson image is contained in the actual offender actor
I. Hence the full inverse image of I has the same elementary Thompson subgroup
as G_v. Its nontrivial maximum-elementary images are offenders on the original
U_v: the proof identifies the internal centralizer quotient and transports the
fixed-space inequality through the literal inclusion of U_v in G_v.

An additive bound for the ranks of the two coordinate projections forces each
such offender to fill its coordinate product. The equality [X,J(G_v)*] = X,
with X = O²(I), then detects both S₃ factors: missing one coordinate would put
the full residual inside the other factor. This argument uses only relative
normality of the factors in I. The resulting intersection witnesses apply to
the original star quotient and give the literal preimage Thompson equality.

The additive projection bound remains an explicit representation-theoretic
premise. Thus this module is a reduction of the double-S₃ branch, not an
unconditional proof of its maximum-elementary construction or of 13.6.13.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.2.4,
printed pp.75–76, B.5.6(3), p.105, and 13.6.13, p.929.
-/

@[expose] public section

open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.SourceInduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Double
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives


variable {G : Type*} [Group G] [Finite G]
/-- Passing to the full inverse image of a subgroup containing J(G_v)*
preserves the global elementary Thompson image. -/
theorem preimage_thompson_eq_global (z v : G) (I : Subgroup (Gstar z v)) (hJI : JGstar z v ≤ I) :
    (elementaryAbelianMaxJ (I.comap (starMk z v))).map (starMk z v) = JGstar z v := by
  have hglob : (elementaryAbelianMaxJ (⊤ : Subgroup (Gv v))).map (starMk z v) = JGstar z v :=
    starImage_intrinsic_thompson z v ⊤ (Gv v)
      (by rw [← MonoidHom.range_eq_map, range_subtype])
  have hJ : elementaryAbelianMaxJ (⊤ : Subgroup (Gv v)) ≤ I.comap (starMk z v) :=
    map_le_iff_le_comap.mp (hglob ▸ hJI)
  rw [elementaryAbelianMaxJ_eq_of_intermediate ⊤ _ hJ le_top, hglob]

private noncomputable def moduleEquiv (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] [IsElementaryAbelian 2 (internalUv z v)] :
    Additive (internalUv z v) ≃ₗ[ZMod 2] Additive (Uv z v) :=
  let e : Additive (internalUv z v) ≃+ Additive (Uv z v) :=
    (subgroupOfEquivOfLe (Uv_le_Gv z v hz)).toAdditive
  e.toLinearEquiv (fun c w => ZMod.map_smul e.toAddMonoidHom c w)

omit [Finite G] in
private theorem moduleEquiv_intertwines (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] [IsElementaryAbelian 2 (internalUv z v)]
    (g : Gstar z v) (w : Additive (internalUv z v)) :
    moduleEquiv z v hz (uvRepresentation z v hz g w) =
      starRepresentation z v g (moduleEquiv z v hz w) := by
  obtain ⟨a, rfl⟩ := starMk_surjective z v g
  apply Additive.toMul.injective
  apply Subtype.ext
  change (((uvRepresentation z v hz (starMk z v a) w).toMul : Gv v) : G) = _
  rw [uvRepresentation_apply, starRepresentation_mk_apply]
  rfl

/-- A nontrivial maximum-elementary image in the full preimage is an
offender for the actual star action on the original U_v. -/
theorem maxElementary_star_isOffender (z v : G) (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (I : Subgroup (Gstar z v)) (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (I.comap (starMk z v)))
    (hne : E.map (starMk z v) ≠ ⊥) :
    IsOffender (starRepresentation z v) (E.map (starMk z v)) := by
  let : IsElementaryAbelian 2 (internalUv z v) :=
    IsElementaryAbelian.subgroupOf (Uv_le_Gv z v hz)
  have hU : internalUv z v ≤ I.comap (starMk z v) := by
    apply le_trans _ (comap_mono (show (⊥ : Subgroup (Gstar z v)) ≤ I from bot_le))
    change internalUv z v ≤ (starMk z v).ker
    rw [starMk_ker_internal z v hz]
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have h := NormalElementaryQuotient.maxElementary_isOffender (internalUv z v)
    (starMk z v) (starMk_surjective z v) (starMk_ker_internal z v hz)
    (I.comap (starMk z v)) E hU hE (fun he => hne ((map_eq_bot_iff E).mpr he))
  have hh := h.map_equivariant (uvRepresentation z v hz) (starRepresentation z v)
    (MonoidHom.id _) Function.injective_id (moduleEquiv z v hz) (moduleEquiv_intertwines z v hz)
  simpa only [Subgroup.map_id] using hh


private def swapProduct {D : Type*} [Group D] {A B : Subgroup D}
    (h : InternalProduct A B) : InternalProduct B A where
  equiv := MulEquiv.prodComm.trans h.equiv
  apply_eq b a := by
    change h.equiv (a, b) = (b : D) * a
    have hc := congrArg h.equiv (show (a, (1 : B)) * (1, b) = (1, b) * (a, 1) by simp)
    rw [map_mul, map_mul, h.apply_eq, h.apply_eq] at hc
    simpa only [h.apply_eq, OneMemClass.coe_one, mul_one, one_mul] using hc

private theorem residual_not_le_second {D : Type*} [Group D] [Finite D]
    {A B : Subgroup D} (h : InternalProduct A B) (e : A ≃* Equiv.Perm (Fin 3)) :
    ¬ pResidual 2 D ≤ B := by
  intro hle
  have hsur : Function.Surjective h.fst := by
    intro a
    refine ⟨h.equiv (a, 1), ?_⟩
    exact congrArg Prod.fst (h.equiv.symm_apply_apply (a, 1))
  have hz : (pResidual 2 D).map h.fst = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (h.ker_fst.symm ▸ hle)
  rw [map_pResidual_of_surjective 2 h.fst hsur] at hz
  have hc : Nat.card (pResidual 2 A) = 3 := by
    rw [← card_map_of_injective (K := pResidual 2 A) (f := e.toMonoidHom) e.injective,
      map_pResidual, Equiv.Perm.twoResidual_eq_alternating, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [hz, card_bot] at hc
  omega

private theorem commutator_actor_not_le_second {D : Type*} [Group D] [Finite D]
    {A B : Subgroup D} (h : InternalProduct A B) (e : A ≃* Equiv.Perm (Fin 3))
    (J : Subgroup D) (hcomm : ⁅pResidual 2 D, J⁆ = pResidual 2 D) : ¬ J ≤ B := by
  let : B.Normal := h.second_normal
  intro hJB
  exact residual_not_le_second h e
    (hcomm.ge.trans ((commutator_mono le_rfl hJB).trans (commutator_le_right _ _)))

private theorem exists_maximum_intersection {C D : Type*} [Group C] [Group D]
    (q : C →* D) (P : Subgroup C) (A B : Subgroup D)
    (hn : ¬ (elementaryAbelianMaxJ P).map q ≤ B)
    (hsplit : ∀ E ∈ elementaryAbelianMaxSubgroups P,
      E.map q = (E.map q ⊓ A) ⊔ (E.map q ⊓ B)) :
    ∃ E ∈ elementaryAbelianMaxSubgroups P, E.map q ⊓ A ≠ ⊥ := by
  by_contra! hnone
  apply hn
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro E hE
  apply map_le_iff_le_comap.mp
  rw [hsplit E hE, hnone E hE, bot_sup_eq]
  exact inf_le_right

private theorem elementary_card_pow_rank {D : Type*} [Group D] [Finite D]
    (A : Subgroup D) (hA : IsElementaryAbelian 2 A) : Nat.card A = 2 ^ rank A := by
  let : IsElementaryAbelian 2 A := hA
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  rw [rank, hn, Nat.log_pow Nat.one_lt_two]

private theorem offender_splits_of_projection_bound
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {F K : Subgroup D} (h : InternalProduct F K)
    (A : Subgroup D) (hA : IsOffender ρ A)
    (hbound : rank (A.map h.fst) + rank (A.map h.snd) ≤ fixedCodim ρ A) :
    A = (A ⊓ F) ⊔ (A ⊓ K) := by
  let : IsElementaryAbelian 2 A := hA.1.2
  let R := ((A.map h.fst).prod (A.map h.snd)).map h.equiv.toMonoidHom
  have hAR : A ≤ R := by
    intro a ha
    exact ⟨h.equiv.symm a, ⟨mem_map_of_mem h.fst ha, mem_map_of_mem h.snd ha⟩,
      h.equiv.apply_symm_apply a⟩
  have heq : A = R := by
    apply eq_of_le_of_card_ge hAR
    change Nat.card (((A.map h.fst).prod (A.map h.snd)).map h.equiv.toMonoidHom) ≤ _
    rw [card_map_of_injective h.equiv.injective,
      Nat.card_congr (Subgroup.prodEquiv (A.map h.fst) (A.map h.snd)).toEquiv, Nat.card_prod,
      elementary_card_pow_rank _ (hA.1.2.map h.fst),
      elementary_card_pow_rank _ (hA.1.2.map h.snd),
      elementary_card_pow_rank _ hA.1.2, ← pow_add]
    exact Nat.pow_le_pow_right Nat.zero_lt_two (hbound.trans hA.2)
  apply le_antisymm _ (sup_le inf_le_left inf_le_left)
  intro a ha
  obtain ⟨⟨x,y⟩, ⟨hx,hy⟩, hxy⟩ := heq ▸ ha
  have hxA : (x : D) ∈ A := by
    rw [heq]
    exact ⟨(x, 1), ⟨hx, one_mem _⟩, by
      change h.equiv (x, 1) = (x : D)
      simp only [h.apply_eq, OneMemClass.coe_one, mul_one]⟩
  have hyA : (y : D) ∈ A := by
    rw [heq]
    exact ⟨(1, y), ⟨one_mem _, hy⟩, by
      change h.equiv (1, y) = (y : D)
      simp only [h.apply_eq, OneMemClass.coe_one, one_mul]⟩
  change h.equiv (x,y) = a at hxy
  rw [← hxy, h.apply_eq]
  exact ((A ⊓ F) ⊔ (A ⊓ K)).mul_mem
    ((le_sup_left : A ⊓ F ≤ (A ⊓ F) ⊔ (A ⊓ K)) ⟨hxA, x.property⟩)
    ((le_sup_right : A ⊓ K ≤ (A ⊓ F) ⊔ (A ⊓ K)) ⟨hyA, y.property⟩)

/-- The full residual commutator detects both coordinates once offenders split.
The splitting premise is a representation-theoretic obligation, not a claim
that a maximum image is contained in just one factor. -/
theorem minimalSolvable_twoFactor_maxima_of_offender_split
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      pResidual 2 (FFFactors.offenderActor (starRepresentation z v)))
    (hsplit : ∀ A : Subgroup (FFFactors.offenderActor (starRepresentation z v)),
      IsOffender (FFFactors.offenderRepresentation (starRepresentation z v)) A →
      A = (A ⊓ c.first) ⊔ (A ⊓ c.second)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H₁ := c.first.map I.subtype
    let H₂ := c.second.map I.subtype
    ∃ E₁ E₂ : Subgroup (Gv v),
      E₁ ∈ elementaryAbelianMaxSubgroups (I.comap (starMk z v)) ∧
      E₂ ∈ elementaryAbelianMaxSubgroups (I.comap (starMk z v)) ∧
      E₁.map (starMk z v) ⊓ H₁ ≠ ⊥ ∧ E₂.map (starMk z v) ⊓ H₂ ≠ ⊥ := by
  intro I H₁ H₂
  let P := I.comap (starMk z v)
  have hg := minimalSolvable_global_thompson L T z v hz S hS hX
  have hXI := XFamily_le_star_offender L T z v hz S hS hX.1
  have hJ : (elementaryAbelianMaxJ P).map (starMk z v) = JGstar z v :=
    preimage_thompson_eq_global z v I hg.1
  have hcomm : ⁅pResidual 2 I, (JGstar z v).subgroupOf I⁆ = pResidual 2 I := by
    rw [← hF]
    apply map_injective I.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hXI,
      map_subgroupOf_eq_of_le hg.1, hg.2]
  have hs (E : Subgroup (Gv v)) (hE : E ∈ elementaryAbelianMaxSubgroups P) :
      E.map (starMk z v) = (E.map (starMk z v) ⊓ H₁) ⊔
        (E.map (starMk z v) ⊓ H₂) := by
    by_cases he : E.map (starMk z v) = ⊥
    · simp only [he, bot_inf_eq, bot_sup_eq]
    have hEI : E.map (starMk z v) ≤ I := map_le_iff_le_comap.mpr hE.1
    have hoff := (maxElementary_star_isOffender z v hz I E hE he).subgroupOf
      (starRepresentation z v) hEI
    have hh := congrArg (Subgroup.map I.subtype) (hsplit _ hoff)
    simpa only [Subgroup.map_sup, Subgroup.map_inf _ _ _ I.subtype_injective,
      map_subgroupOf_eq_of_le hEI] using hh
  have hnot₁ : ¬ (elementaryAbelianMaxJ P).map (starMk z v) ≤ H₂ := by
    rw [hJ]
    intro hle
    apply commutator_actor_not_le_second c.product e₁ _ hcomm
    intro x hx
    exact (mem_map_iff_mem I.subtype_injective).mp (hle hx)
  have hnot₂ : ¬ (elementaryAbelianMaxJ P).map (starMk z v) ≤ H₁ := by
    rw [hJ]
    intro hle
    apply commutator_actor_not_le_second (swapProduct c.product) e₂ _ hcomm
    intro x hx
    exact (mem_map_iff_mem I.subtype_injective).mp (hle hx)
  obtain ⟨E₁, hE₁, hn₁⟩ := exists_maximum_intersection (starMk z v) P H₁ H₂ hnot₁ hs
  obtain ⟨E₂, hE₂, hn₂⟩ := exists_maximum_intersection (starMk z v) P H₂ H₁ hnot₂
    (fun E hE => (hs E hE).trans (sup_comm _ _))
  exact ⟨E₁, E₂, hE₁, hE₂, hn₁, hn₂⟩


/-- Application to the literal star preimage. Only the displayed offender
splitting premise remains to be supplied by the double-factor module argument. -/
theorem minimalSolvable_twoFactor_thompson_of_offender_split
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      pResidual 2 (FFFactors.offenderActor (starRepresentation z v)))
    (hsplit : ∀ A : Subgroup (FFFactors.offenderActor (starRepresentation z v)),
      IsOffender (FFFactors.offenderRepresentation (starRepresentation z v)) A →
      A = (A ⊓ c.first) ⊔ (A ⊓ c.second)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    starImage z v (elementaryAbelianMaxJ (starPreimage z v I)) = I := by
  intro I
  obtain ⟨E₁, E₂, hE₁, hE₂, hn₁, hn₂⟩ :=
    minimalSolvable_twoFactor_maxima_of_offender_split L T z v hz S hS hX c e₁ e₂ hF hsplit
  have hgen : c.first.map I.subtype ⊔ c.second.map I.subtype = I := by
    rw [← Subgroup.map_sup, c.product.sup_eq_top, ← MonoidHom.range_eq_map, range_subtype]
  exact star_thompson_eq_of_two_intersections z v I _ _
    ((c.first.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e₁)
    ((c.second.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e₂)
    hgen E₁ E₂ hE₁ hE₂ hn₁ hn₂


/-- Cardinal comparison reduces the maximum-elementary construction to the
additive fixed-codimension bound on the two literal coordinate projections.
This retains all native source module clauses in c. -/
theorem minimalSolvable_twoFactor_maxima_of_projection_bound
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      pResidual 2 (FFFactors.offenderActor (starRepresentation z v)))
    (hbound : ∀ A : Subgroup (FFFactors.offenderActor (starRepresentation z v)),
      IsElementaryAbelian 2 A →
      rank (A.map c.product.fst) + rank (A.map c.product.snd) ≤
        fixedCodim (FFFactors.offenderRepresentation (starRepresentation z v)) A) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H₁ := c.first.map I.subtype
    let H₂ := c.second.map I.subtype
    ∃ E₁ E₂ : Subgroup (Gv v),
      E₁ ∈ elementaryAbelianMaxSubgroups (I.comap (starMk z v)) ∧
      E₂ ∈ elementaryAbelianMaxSubgroups (I.comap (starMk z v)) ∧
      E₁.map (starMk z v) ⊓ H₁ ≠ ⊥ ∧ E₂.map (starMk z v) ⊓ H₂ ≠ ⊥ := by
  apply minimalSolvable_twoFactor_maxima_of_offender_split L T z v hz S hS hX c e₁ e₂ hF
  intro A hA
  exact offender_splits_of_projection_bound _ c.product A hA (hbound A hA.1.2)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Double
end
