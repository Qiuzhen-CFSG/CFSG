module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.CubicFF.Constituents
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SectionCoordinates
public import Theory.Representation.BinaryOffender.CentralSectionSplitting
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Saturation of an odd cubic constituent pair

For the external cubic branch, an odd-dimensional binary Irr⁺ constituent
with zero central kernel is disjoint from its cubic conjugate. A cubic action
preserving it would have one fixed vector, giving |I| = 1 modulo 3, whereas
odd binary dimension gives |I| = 2 modulo 3. Irreducible minimality then
makes the intersection of the two distinct constituents zero.

The actual central projection and the equivariant map (i,j) ↦ i + xj identify
the pair's fixed codimension with twice the constituent codimension. The
supplied numerical bound rules out a strong offender. For an offender all
inequalities are equalities, so A centralizes the quotient by the pair;
K = [K,A] centralizes it as well. The Irr⁺ commutator clauses give the reverse
containment, identifying the pair with [V,K], without asserting V = [V,K].

For every ambient invariant realization W of this moved space, the literal
W/0 section has canonical inverter-fixed multiplicity. Its two coordinates
provide a nonzero K-equivariant projection of I to the multiplicity space.
Irreducibility makes this injective, and the two pair decompositions give
equal dimensions. Its inverse is the required equivariant equivalence.

These are conditional linear steps with exactly the central-disjointness,
odd-dimension and numerical inputs supplied by the parent cubic-FF argument.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.1.5,
B.4.2, F.9.18(6), and the proof of 13.8.20(a), printed pp.954–955.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender
open InvertedCubicTensor
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.CubicFF.PairSaturation
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) D V) (K A : Subgroup D) [K.Normal]

private theorem odd_not_cubic_stable (s : S₃ →* D)
    (hfree : ∀ v, ρ (s cubic) v = v → v = 0)
    (I : Submodule (ZMod 2) V) (ho : Odd (Module.finrank (ZMod 2) I)) :
    I.map (ρ (s cubic)) ≠ I := by
  classical
  intro he
  let f : Function.End I := fun v => ⟨ρ (s cubic) v, he.le ⟨v,v.property,rfl⟩⟩
  have hf : f ^ 3 ^ 1 = 1 := by
    funext v
    apply Subtype.ext
    change ρ (s cubic) (ρ (s cubic) (ρ (s cubic) v)) = v
    change (ρ (s cubic) * ρ (s cubic) * ρ (s cubic)) v = v
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, cubic_cube, map_one, map_one,
      Module.End.one_apply]
  let : Fintype I := Fintype.ofFinite I
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hfix : ∀ v : Function.fixedPoints f, v.val = 0 := by
    intro v
    apply Subtype.ext
    exact hfree v.val (congrArg Subtype.val v.property)
  let : Unique (Function.fixedPoints f) :=
    ⟨⟨0, Subtype.ext (map_zero _)⟩, fun v => Subtype.ext ((hfix v).trans rfl)⟩
  have hc := Equiv.Perm.card_fixedPoints_modEq hf
  rw [Fintype.card_unique (α := Function.fixedPoints f), ← Nat.card_eq_fintype_card,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := I), Nat.card_zmod] at hc
  obtain ⟨n, hn⟩ := ho
  have hm : (2 ^ Module.finrank (ZMod 2) I) % 3 = 2 := by
    rw [hn, pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  change _ % 3 = _ % 3 at hc
  omega

/-- An odd-dimensional central-free Irr⁺ constituent is disjoint from its cubic conjugate. -/
theorem cubic_pair_disjoint (s : S₃ →* D)
    (hfree : ∀ v, ρ (s cubic) v = v → v = 0)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hd : Disjoint I (fixedSpace ρ K)) (ho : Odd (Module.finrank (ZMod 2) I)) :
    Disjoint I (I.map (ρ (s cubic))) := by
  have hJ := hI.map_normalizer ρ (a := s cubic) (by rw [Subgroup.normalizer_eq_top]; trivial)
  have hs : K ≤ subspaceStabilizer ρ (I ⊓ I.map (ρ (s cubic))) := by
    apply le_subspaceStabilizer
    intro k hk v hv
    exact ⟨(hI.choose hk v).2 hv.1, (hJ.choose hk v).2 hv.2⟩
  rcases hI.eq_or_le_fixedSpace ρ hs inf_le_left with he | hc
  · have hle : I ≤ I.map (ρ (s cubic)) := he.ge.trans inf_le_right
    exact False.elim (odd_not_cubic_stable ρ s hfree I ho (hI.eq_of_le ρ hJ hle).symm)
  · rw [Submodule.disjoint_def]
    intro v hi hj
    exact Submodule.disjoint_def.mp hd v hi (hc ⟨hi,hj⟩)

private def conjugatePairEquiv (I : Submodule (ZMod 2) V) (x : D)
    (hd : Disjoint I (I.map (ρ x))) :
    (I × I) ≃ₗ[ZMod 2] (I ⊔ I.map (ρ x) : Submodule (ZMod 2) V) := by
  let f : (I × I) →ₗ[ZMod 2] V := I.subtype.coprod ((ρ x).comp I.subtype)
  let g := f.codRestrict (I ⊔ I.map (ρ x)) (fun v =>
    Submodule.mem_sup.mpr ⟨v.1, v.1.property, _, ⟨v.2, v.2.property, rfl⟩, rfl⟩)
  apply LinearEquiv.ofBijective g
  constructor
  · apply (injective_iff_map_eq_zero g).mpr
    intro v hv
    have he : (v.1 : V) + ρ x v.2 = 0 := congrArg Subtype.val hv
    have hzero : (v.1 : V) = 0 := by
      apply Submodule.disjoint_def.mp hd _ v.1.property
      rw [eq_neg_of_add_eq_zero_left he]
      exact (I.map (ρ x)).neg_mem ⟨v.2,v.2.property,rfl⟩
    have hz : ρ x v.2 = 0 := by simpa only [hzero, zero_add] using he
    have hz2 : (v.2 : V) = 0 := by
      have hh := congrArg (ρ x⁻¹) hz
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply, map_zero] using hh
    exact Prod.ext (Subtype.ext hzero) (Subtype.ext hz2)
  · intro v
    obtain ⟨i,hi,j,⟨w,hw,rfl⟩,he⟩ := Submodule.mem_sup.mp v.property
    exact ⟨(⟨i,hi⟩,⟨w,hw⟩), Subtype.ext he⟩

omit [Finite V] in
private theorem conjugate_stable (I : Submodule (ZMod 2) V) (x : D) (B : Subgroup D)
    (hB : B ≤ subspaceStabilizer ρ I) (hx : ∀ b ∈ B, Commute b x) :
    B ≤ subspaceStabilizer ρ (I.map (ρ x)) := by
  apply le_subspaceStabilizer
  rintro b hb _ ⟨i,hi,rfl⟩
  refine ⟨ρ b i, (hB hb i).2 hi, ?_⟩
  change (ρ x * ρ b) i = (ρ b * ρ x) i
  rw [← map_mul, ← map_mul, (hx b hb).eq]

open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.CubicFF

omit [Finite V] in
/-- The literal central projection identifies constituent and subspace fixed codimensions. -/
theorem constituent_fixedCodim (I : Submodule (ZMod 2) V)
    (hI : K ≤ subspaceStabilizer ρ I) (hAI : A ≤ subspaceStabilizer ρ I)
    (hd : Disjoint I (fixedSpace ρ K)) :
    fixedCodim (constituentUpper ρ K A I hI hAI).toRepresentation (A.subgroupOf (K ⊔ A)) =
      fixedCodim (constituentAction ρ K A I hI hAI) (A.subgroupOf (K ⊔ A)) := by
  have he := fixedCodim_map_equivariant
    (constituentUpper ρ K A I hI hAI).toRepresentation
    (constituentAction ρ K A I hI hAI) (MonoidHom.id _)
    (centralSectionEquiv ρ K I hd) (fun _ _ => rfl) (A.subgroupOf (K ⊔ A))
  simpa only [Subgroup.map_id] using he

private def pairUpper (I : Submodule (ZMod 2) V)
    (hI : K ≤ subspaceStabilizer ρ I) (hAI : A ≤ subspaceStabilizer ρ I)
    (x : D) (hKx : ∀ k ∈ K, Commute k x) (hAx : ∀ a ∈ A, Commute a x) :
    Subrepresentation (ρ.comp (K ⊔ A).subtype) :=
  constituentUpper ρ K A (I ⊔ I.map (ρ x))
    (subspaceStabilizer_sup ρ hI (conjugate_stable ρ I x K hI hKx))
    (subspaceStabilizer_sup ρ hAI (conjugate_stable ρ I x A hAI hAx))

private theorem pair_fixedCodim (I : Submodule (ZMod 2) V)
    (hI : K ≤ subspaceStabilizer ρ I) (hAI : A ≤ subspaceStabilizer ρ I)
    (hd : Disjoint I (fixedSpace ρ K))
    (x : D) (hKx : ∀ k ∈ K, Commute k x) (hAx : ∀ a ∈ A, Commute a x)
    (hpair : Disjoint I (I.map (ρ x))) :
    fixedCodim (pairUpper ρ K A I hI hAI x hKx hAx).toRepresentation
      (A.subgroupOf (K ⊔ A)) =
      2 * fixedCodim (constituentAction ρ K A I hI hAI) (A.subgroupOf (K ⊔ A)) := by
  let σ := (constituentUpper ρ K A I hI hAI).toRepresentation
  let P := pairUpper ρ K A I hI hAI x hKx hAx
  have hc : ∀ g : (K ⊔ A : Subgroup D), Commute (g : D) x := by
    have hle : K ⊔ A ≤ centralizer ({x} : Set D) := by
      apply sup_le
      · intro k hk y hy
        obtain rfl : y = x := hy
        exact (hKx k hk).symm.eq
      · intro a ha y hy
        obtain rfl : y = x := hy
        exact (hAx a ha).symm.eq
    intro g
    exact (hle g.property x rfl).symm
  have he := fixedCodim_map_equivariant (σ.prod σ) P.toRepresentation
    (MonoidHom.id _) (conjugatePairEquiv ρ I x hpair) (fun g v => by
      apply Subtype.ext
      change ρ g v.1 + ρ x (ρ g v.2) = ρ g ((v.1 : V) + ρ x v.2)
      rw [map_add]
      congr 1
      change (ρ x * ρ g) v.2 = (ρ g * ρ x) v.2
      rw [← map_mul, ← map_mul, (hc g).eq]) (A.subgroupOf (K ⊔ A))
  rw [Subgroup.map_id, fixedCodim_prod] at he
  rw [← he, ← constituent_fixedCodim ρ K A I hI hAI hd]
  change _ + _ = 2 * fixedCodim σ _
  omega

/-- The two commuting conjugate constituents together pay the full rank of the actor. -/
theorem rank_le_fixedCodim (s : S₃ →* D)
    (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hfree : ∀ v, ρ (s cubic) v = v → v = 0)
    (hAx : ∀ a ∈ A, Commute a (s cubic))
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hAI : A ≤ subspaceStabilizer ρ I)
    (hd : Disjoint I (fixedSpace ρ K)) (ho : Odd (Module.finrank (ZMod 2) I))
    (hnum : rank A ≤ 2 * fixedCodim (constituentAction ρ K A I hI.choose hAI)
      (A.subgroupOf (K ⊔ A))) : rank A ≤ fixedCodim ρ A := by
  let hKx := fun k hk => hs ⟨k,hk⟩ cubic
  let P := pairUpper ρ K A I hI.choose hAI (s cubic) hKx hAx
  have he := pair_fixedCodim ρ K A I hI.choose hAI hd (s cubic) hKx hAx
    (cubic_pair_disjoint ρ K s hfree I hI hd ho)
  have hle := fixedCodim_subrepresentation_le (ρ.comp (K ⊔ A).subtype) P
    (A.subgroupOf (K ⊔ A))
  have hc : fixedCodim (ρ.comp (K ⊔ A).subtype) (A.subgroupOf (K ⊔ A)) =
      fixedCodim ρ A := by
    unfold fixedCodim
    rw [fixedSpace_comp_map, map_subgroupOf_eq_of_le (show A ≤ K ⊔ A from le_sup_right)]
  change fixedCodim P.toRepresentation _ = _ at he
  omega

/-- For an offender the codimension inequalities are equalities, and the pair is exactly [V,K]. -/
theorem moved_eq_pair (s : S₃ →* D)
    (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hfree : ∀ v, ρ (s cubic) v = v → v = 0)
    (hAx : ∀ a ∈ A, Commute a (s cubic)) (hKA : ⁅K,A⁆ = K)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hAI : A ≤ subspaceStabilizer ρ I)
    (hd : Disjoint I (fixedSpace ρ K)) (ho : Odd (Module.finrank (ZMod 2) I))
    (hnum : rank A ≤ 2 * fixedCodim (constituentAction ρ K A I hI.choose hAI)
      (A.subgroupOf (K ⊔ A))) (hoff : IsOffender ρ A) :
    subspaceCommutator ρ ⊤ K = I ⊔ I.map (ρ (s cubic)) := by
  let E := K ⊔ A
  let hKx := fun k hk => hs ⟨k,hk⟩ cubic
  let P := pairUpper ρ K A I hI.choose hAI (s cubic) hKx hAx
  let A₀ := A.subgroupOf E
  let K₀ := K.subgroupOf E
  have he := pair_fixedCodim ρ K A I hI.choose hAI hd (s cubic) hKx hAx
    (cubic_pair_disjoint ρ K s hfree I hI hd ho)
  have hle := fixedCodim_subrepresentation_le (ρ.comp E.subtype) P A₀
  have hc : fixedCodim (ρ.comp E.subtype) A₀ = fixedCodim ρ A := by
    unfold fixedCodim
    rw [fixedSpace_comp_map, map_subgroupOf_eq_of_le (show A ≤ E from le_sup_right)]
  have heq : fixedCodim P.toRepresentation A₀ = fixedCodim (ρ.comp E.subtype) A₀ := by
    change fixedCodim P.toRepresentation A₀ = _ at he
    have := hoff.2
    omega
  have ht := quotient_trivial_of_sup_fixedSpace (ρ.comp E.subtype) P A₀
    ((fixedCodim_subrepresentation_eq_iff (ρ.comp E.subtype) P A₀).mp heq)
  have hKA₀ : ⁅K₀,A₀⁆ = K₀ := by
    apply Subgroup.map_injective E.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le (show K ≤ E from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ E from le_sup_right), hKA]
  have hk := trivial_sup_of_commutator_eq P.quotientRepresentation K₀ A₀ hKA₀ ht
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k,hkK,v,_,rfl⟩
    have hh := hk ⟨k,mem_sup_left hkK⟩ (mem_sup_right (show (⟨k,mem_sup_left hkK⟩ : E) ∈ K₀ from hkK))
      (P.toSubmodule.mkQ v)
    exact (Submodule.Quotient.eq P.toSubmodule).mp hh
  · have hJ := hI.map_normalizer ρ (a := s cubic) (by rw [Subgroup.normalizer_eq_top]; trivial)
    rw [← hI.sup_commutator ρ hJ]
    exact subspaceCommutator_mono_left ρ le_top K


omit [Finite V] [K.Normal] in
set_option backward.isDefEq.respectTransparency false in
/-- Removing the central kernel makes the original Irr⁺ subspace irreducible. -/
theorem constituent_irreducible (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hd : Disjoint I (fixedSpace ρ K)) :
    IsIrreducible (invariantSubspace ρ K I hI.choose).toRepresentation := by
  let : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr (hI.ne_bot ρ)
  let σ : Representation (ZMod 2) K I := (invariantSubspace ρ K I hI.choose).toRepresentation
  change IsSimpleOrder (Subrepresentation σ)
  rw [isSimpleOrder_iff]
  refine ⟨inferInstance, ?_⟩
  intro S
  let J := S.toSubmodule.map I.subtype
  have hJ : K ≤ subspaceStabilizer ρ J := by
    apply le_subspaceStabilizer
    rintro k hk _ ⟨i,hi,rfl⟩
    exact ⟨(invariantSubspace ρ K I hI.choose).toRepresentation ⟨k,hk⟩ i,
      S.apply_mem_toSubmodule ⟨k,hk⟩ hi, rfl⟩
  rcases hI.eq_or_le_fixedSpace ρ hJ (Submodule.map_subtype_le _ _) with he | hf
  · right
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.map_injective_of_injective I.subtype_injective
    change J = (⊤ : Submodule (ZMod 2) I).map I.subtype
    rw [Submodule.map_top, Submodule.range_subtype]
    exact he
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_bot_iff.mp
    intro v hv
    exact Subtype.ext (Submodule.disjoint_def.mp hd v v.property (hf ⟨v,hv,rfl⟩))

open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections

private def bottomSectionEquiv (W : Subrepresentation ρ) :
    W.toSubmodule ≃ₗ[ZMod 2] SectionSpace ρ ⊥ W :=
  LinearEquiv.ofBijective (sectionLower ρ ⊥ W).toSubmodule.mkQ ⟨by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero (sectionLower ρ ⊥ W).toSubmodule).mp hv,
    Submodule.mkQ_surjective _⟩

omit [Finite V] in
private theorem bottomSection_fixedFree (s : S₃ →* D)
    (hfree : ∀ v, ρ (s cubic) v = v → v = 0) (W : Subrepresentation ρ) :
    ∀ v, sectionRepresentation ρ ⊥ W (s cubic) v = v → v = 0 := by
  apply fixedFree_of_surjective (W.toRepresentation.comp s)
    ((sectionRepresentation ρ ⊥ W).comp s)
    (bottomSectionEquiv ρ W).toLinearMap (bottomSectionEquiv ρ W).surjective
    (fun v => rfl)
  exact fixedFree_of_injective (ρ.comp s) (W.toRepresentation.comp s)
    W.toSubmodule.subtype W.toSubmodule.subtype_injective (fun v => rfl) hfree

omit [K.Normal] in
set_option backward.isDefEq.respectTransparency false in
/-- An irreducible cubic pair identifies the literal section multiplicity with either constituent. -/
theorem multiplicity_coordinates (s : S₃ →* D)
    (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hfree : ∀ v, ρ (s cubic) v = v → v = 0)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hd : Disjoint I (fixedSpace ρ K))
    (hpair : Disjoint I (I.map (ρ (s cubic))))
    (W : Subrepresentation ρ) (hW : W.toSubmodule = I ⊔ I.map (ρ (s cubic))) :
    ∃ a : SectionMultiplicity ρ s ⊥ W ≃ₗ[ZMod 2] I,
      ∀ k v, a (sectionMultiplicityAction ρ K.subtype s hs ⊥ W k v) =
        (invariantSubspace ρ K I hI.choose).toRepresentation k (a v) := by
  let τ := sectionRepresentation ρ ⊥ W
  let M := SectionMultiplicity ρ s ⊥ W
  let μ : Representation (ZMod 2) K M := sectionMultiplicityAction ρ K.subtype s hs ⊥ W
  let σ : Representation (ZMod 2) K I := (invariantSubspace ρ K I hI.choose).toRepresentation
  let e := pairEquiv (τ.comp s) (bottomSection_fixedFree ρ s hfree W)
  let b := bottomSectionEquiv ρ W
  have hIW : I ≤ W.toSubmodule := by rw [hW]; exact le_sup_left
  let j : I →ₗ[ZMod 2] M × M := e.symm.toLinearMap.comp
    (b.toLinearMap.comp (Submodule.inclusion hIW))
  have hj : Function.Injective j := e.symm.injective.comp
    (b.injective.comp (Submodule.inclusion_injective hIW))
  have hje (k : K) (v : I) : j (σ k v) = (μ k (j v).1, μ k (j v).2) := by
    apply e.injective
    calc
      e (j (σ k v)) = b (Submodule.inclusion hIW (σ k v)) := e.apply_symm_apply _
      _ = τ k (b (Submodule.inclusion hIW v)) := rfl
      _ = τ k (e (j v)) := congrArg (τ k) (e.apply_symm_apply _).symm
      _ = e (μ k (j v).1, μ k (j v).2) :=
        (pairEquiv_equivariant (τ.comp s) (τ.comp K.subtype)
          (ambient_commute τ K.subtype s hs) _ k (j v)).symm
  let f : IntertwiningMap σ μ :=
    { toLinearMap := (LinearMap.fst (ZMod 2) M M).comp j
      isIntertwining' k := by apply LinearMap.ext; intro v; exact congrArg Prod.fst (hje k v) }
  let g : IntertwiningMap σ μ :=
    { toLinearMap := (LinearMap.snd (ZMod 2) M M).comp j
      isIntertwining' k := by apply LinearMap.ext; intro v; exact congrArg Prod.snd (hje k v) }
  let : IsIrreducible σ := constituent_irreducible ρ K I hI hd
  have hdim : Module.finrank (ZMod 2) I = Module.finrank (ZMod 2) M := by
    have h1 := (conjugatePairEquiv ρ I (s cubic) hpair).finrank_eq
    have h2 := e.finrank_eq
    have h3 := b.finrank_eq
    have h4 := congrArg (fun N : Submodule (ZMod 2) V => Module.finrank (ZMod 2) N) hW
    rw [Module.finrank_prod] at h1 h2
    change Module.finrank (ZMod 2) M + Module.finrank (ZMod 2) M =
      Module.finrank (ZMod 2) (SectionSpace ρ ⊥ W) at h2
    change _ = Module.finrank (ZMod 2) (SectionSpace ρ ⊥ W) at h3
    omega
  have hex : ∃ f : IntertwiningMap σ μ, Function.Injective f := by
    rcases IsIrreducible.injective_or_eq_zero f with hf | hf
    · exact ⟨f,hf⟩
    rcases IsIrreducible.injective_or_eq_zero g with hg | hg
    · exact ⟨g,hg⟩
    have hz (v : I) : v = 0 := by
      apply hj
      apply Prod.ext
      · have hh := DFunLike.congr_fun hf v
        change (j v).1 = 0 at hh
        simpa only [map_zero, Prod.fst_zero, Prod.snd_zero] using hh
      · have hh := DFunLike.congr_fun hg v
        change (j v).2 = 0 at hh
        simpa only [map_zero, Prod.fst_zero, Prod.snd_zero] using hh
    have hn : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr (hI.ne_bot ρ)
    obtain ⟨v,hv⟩ := exists_ne (0 : I)
    exact False.elim (hv (hz v))
  obtain ⟨f,hf⟩ := hex
  let a : I ≃ₗ[ZMod 2] M := f.toLinearMap.linearEquivOfInjective hf hdim
  refine ⟨a.symm, ?_⟩
  intro k v
  apply a.injective
  exact (a.apply_symm_apply (μ k v)).trans
    ((congrArg (μ k) (a.apply_symm_apply v).symm).trans
      (IntertwiningMap.isIntertwining σ μ f k (a.symm v)).symm)


/-- Every actual realization of the moved space has the original constituent as its
canonical inverter-fixed multiplicity, equivariantly for the original copy of K. -/
theorem offender_multiplicity_coordinates (s : S₃ →* D)
    (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hfree : ∀ v, ρ (s cubic) v = v → v = 0)
    (hAx : ∀ a ∈ A, Commute a (s cubic)) (hKA : ⁅K,A⁆ = K)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hAI : A ≤ subspaceStabilizer ρ I)
    (hd : Disjoint I (fixedSpace ρ K)) (ho : Odd (Module.finrank (ZMod 2) I))
    (hnum : rank A ≤ 2 * fixedCodim (constituentAction ρ K A I hI.choose hAI)
      (A.subgroupOf (K ⊔ A))) (hoff : IsOffender ρ A)
    (W : Subrepresentation ρ) (hW : W.toSubmodule = subspaceCommutator ρ ⊤ K) :
    ∃ a : SectionMultiplicity ρ s ⊥ W ≃ₗ[ZMod 2] I,
      ∀ k v, a (sectionMultiplicityAction ρ K.subtype s hs ⊥ W k v) =
        (invariantSubspace ρ K I hI.choose).toRepresentation k (a v) := by
  exact multiplicity_coordinates ρ K s hs hfree I hI hd
    (cubic_pair_disjoint ρ K s hfree I hI hd ho) W
    (hW.trans (moved_eq_pair ρ K A s hs hfree hAx hKA I hI hAI hd ho hnum hoff))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.CubicFF.PairSaturation
