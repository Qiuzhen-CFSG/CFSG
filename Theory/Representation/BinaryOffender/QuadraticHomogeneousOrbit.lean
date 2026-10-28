module

public import Theory.Representation.BinaryOffender.FaithfulInvariantSection
public import Theory.Representation.BinaryOffender.IrreducibleOrbitGeometry
public import Theory.Representation.BinaryOffender.Homogeneous.Existence
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Quadratic supplements preserve homogeneous constituents

A quadratic elementary actor has at most two translates of a member of an
independent subspace orbit. If it moves a constituent on which its pointwise
kernel is trivial, its order is two. Its fixed codimension then bounds the
constituent dimension by two. A nontrivial perfect binary action has larger
dimension, since every permutation group on at most four vectors is solvable.

For a centerless quasisimple normal subgroup with an elementary quadratic
supplement, these facts make an irreducible whole-actor module irreducible on
the component whenever that component acts nontrivially. Homogeneous selection
is performed in the actual central quotient; irreducibility removes its center.

Source: the quadratic orbit argument in Aschbacher–Smith D.3.5(1–3), pp.195–196,
specialized to an elementary supplement, and the homogeneous selection A.1.42.
The consuming normal-component argument is 15.3.65, printed p.1152.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A quadratic actor has at most two translates of any member of an independent orbit. -/
theorem quadratic_orbit_eq_self_or_moving
    (I : Submodule (ZMod 2) V) (hI : I ≠ ⊥) (A : Subgroup G) [IsMulCommutative A]
    (hq : IsQuadratic ρ A) (hind : sSupIndep (subspaceOrbit ρ A I))
    {a : G} (ha : a ∈ A) (ha2 : a * a = 1)
    (haI : I.map (ρ a) ≠ I) {b : G} (hb : b ∈ A) :
    I.map (ρ b) = I ∨ I.map (ρ b) = I.map (ρ a) := by
  classical
  by_contra hn
  have hbI : I.map (ρ b) ≠ I := fun h => hn (Or.inl h)
  have hbaI : I.map (ρ (b * a)) ≠ I := by
    intro he
    apply hn
    right
    have hh := congrArg (fun J : Submodule (ZMod 2) V => J.map (ρ a)) he
    have hab : a * b = b * a := congrArg Subtype.val
      (mul_comm (⟨a,ha⟩ : A) ⟨b,hb⟩)
    rw [← subspace_map_mul, show a * (b * a) = b by rw [← mul_assoc, hab, mul_assoc, ha2, mul_one]] at hh
    exact hh
  have hImem : I ∈ subspaceOrbit ρ A I := by
    refine ⟨1, ?_⟩
    simp only [Subgroup.coe_one, map_one, Module.End.one_eq_id, Submodule.map_id]
  have hdis := hind hImem
  have hrest (c : G) (hc : c ∈ A) (hne : I.map (ρ c) ≠ I) :
      I.map (ρ c) ≤ sSup (subspaceOrbit ρ A I \ {I}) :=
    le_sSup ⟨⟨⟨c,hc⟩,rfl⟩,hne⟩
  apply hI
  apply bot_unique
  intro v hv
  have hva := (hrest a ha haI) (show ρ a v ∈ I.map (ρ a) from ⟨v,hv,rfl⟩)
  have hvb := (hrest b hb hbI) (show ρ b v ∈ I.map (ρ b) from ⟨v,hv,rfl⟩)
  have hvba := (hrest (b*a) (A.mul_mem hb ha) hbaI)
    (show ρ (b*a) v ∈ I.map (ρ (b*a)) from ⟨v,hv,rfl⟩)
  have he := hq b hb a ha v
  rw [map_sub, ← Module.End.mul_apply, ← map_mul] at he
  have hvrest : v ∈ sSup (subspaceOrbit ρ A I \ {I}) := by
    have hvEq : v = ρ a v + ρ b v - ρ (b*a) v := by
      calc
        v = ρ a v - (ρ a v - v) := (sub_sub_cancel _ _).symm
        _ = ρ a v - (ρ (b*a) v - ρ b v) := by rw [he]
        _ = _ := by abel
    rw [hvEq]
    exact (sSup (subspaceOrbit ρ A I \ {I})).sub_mem
      ((sSup (subspaceOrbit ρ A I \ {I})).add_mem hva hvb) hvba
  exact (Submodule.disjoint_def.mp hdis) v hv hvrest

/-- On an independent orbit, a quadratic actor faithful on the chosen summand
has order two if it moves that summand. -/
theorem quadratic_moving_actor_card_eq_two [Finite G]
    (I : Submodule (ZMod 2) V) (hI : I ≠ ⊥) (A : Subgroup G)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hind : sSupIndep (subspaceOrbit ρ A I))
    (hfaith : ∀ b ∈ A, (∀ v ∈ I, ρ b v = v) → b = 1)
    {a : G} (ha : a ∈ A) (haI : I.map (ρ a) ≠ I) : Nat.card A = 2 := by
  let : IsElementaryAbelian 2 A := hA.2
  have ha2 : a * a = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  have hImem : I ∈ subspaceOrbit ρ A I := by
    refine ⟨1, ?_⟩
    simp only [Subgroup.coe_one, map_one, Module.End.one_eq_id, Submodule.map_id]
  have hdis : Disjoint I (I.map (ρ a)) :=
    hind.pairwiseDisjoint hImem ⟨⟨a,ha⟩,rfl⟩ haI.symm
  have hstab : A ⊓ subspaceStabilizer ρ I = ⊥ := by
    apply bot_unique
    rintro b ⟨hb, hbs⟩
    apply Subgroup.mem_bot.mpr
    exact hfaith b hb (quadratic_fixes_disjoint_summand ρ I hq ha hb hdis
      (fun v hv => (hbs v).2 hv))
  have hinj := subspace_orbitMap_injective ρ hstab
  have ha1 : a ≠ 1 := by
    intro he
    apply haI
    simp only [he, map_one, Module.End.one_eq_id, Submodule.map_id]
  apply Nat.card_eq_two_iff.mpr
  refine ⟨1, ⟨a,ha⟩, ?_, ?_⟩
  · intro he
    exact ha1 (congrArg Subtype.val he).symm
  · apply Set.eq_univ_of_forall
    intro b
    rcases quadratic_orbit_eq_self_or_moving ρ I hI A hq hind ha ha2 haI b.property with hb | hb
    · have hb1 : b = 1 := hinj (by simpa only [Subgroup.coe_one, map_one, Module.End.one_eq_id, Submodule.map_id] using hb)
      simp only [hb1, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
    · have hba : b = ⟨a,ha⟩ := hinj hb
      simp only [hba, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]

/-- A faithful quadratic actor of ratio at most two preserves a summand of
dimension greater than two in any independent orbit. -/
theorem quadratic_stabilizes_of_independent_orbit [Finite G]
    [FiniteDimensional (ZMod 2) V]
    (I : Submodule (ZMod 2) V) (A : Subgroup G)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hind : sSupIndep (subspaceOrbit ρ A I))
    (hfaith : ∀ b ∈ A, (∀ v ∈ I, ρ b v = v) → b = 1)
    (hdim : 2 < Module.finrank (ZMod 2) I)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) : A ≤ subspaceStabilizer ρ I := by
  intro a ha
  apply (subspace_map_eq_iff ρ I a).mp
  by_contra hmove
  have hI : I ≠ ⊥ := Submodule.nontrivial_iff_ne_bot.mp
    (Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) I))
  have hcard := quadratic_moving_actor_card_eq_two ρ I hI A hA hq hind hfaith ha hmove
  have hrank : rank A = 1 := by simp only [rank, hcard]; decide
  have hImem : I ∈ subspaceOrbit ρ A I := by
    refine ⟨1, ?_⟩
    simp only [Subgroup.coe_one, map_one, Module.End.one_eq_id, Submodule.map_id]
  have hdis : Disjoint I (I.map (ρ a)) :=
    hind.pairwiseDisjoint hImem ⟨⟨a,ha⟩,rfl⟩ (fun he => hmove he.symm)
  have hd := finrank_diagonal_eq_of_disjoint ρ I a hdis
  let f := ρ a - LinearMap.id
  have hf : fixedSpace ρ A ≤ f.ker := by
    intro v hv
    exact sub_eq_zero.mpr (hv ⟨a,ha⟩)
  have him : diagonalSubspace ρ I a ≤ f.range := by
    rintro _ ⟨v,_,rfl⟩
    exact ⟨v,rfl⟩
  have himdim := Submodule.finrank_mono him
  have hkdim := Submodule.finrank_mono hf
  have hr := f.finrank_range_add_finrank_ker
  have hcodim := fixedCodim_add_finrank ρ A
  rw [hrank] at hbound
  omega

end Representation.BinaryOffender

namespace Representation.BinaryOffender
open Subgroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A perfect group acts trivially on a binary space of dimension at most two. -/
theorem representation_eq_one_of_isPerfect_of_finrank_le_two
    [Group.IsPerfect G] (ρ : Representation (ZMod 2) G V)
    (hd : Module.finrank (ZMod 2) V ≤ 2) (g : G) : ρ g = 1 := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Fintype V := Fintype.ofFinite V
  let τ : G →* Equiv.Perm V :=
    { toFun := fun g =>
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V
          (ρ.asGroupHom g)).toEquiv
      map_one' := by ext v; simp
      map_mul' := by intro g h; ext v; simp }
  have hcard : Fintype.card V ≤ Fintype.card (Fin 4) := by
    rw [Fintype.card_fin, Module.card_eq_pow_finrank (K := ZMod 2)]
    simpa using (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd)
  let e : V ↪ Fin 4 := Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm V) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  let := Group.IsPerfect.range τ
  have hs : Subsingleton τ.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable τ.range inferInstance
  have he : τ g = 1 := congrArg Subtype.val
    (Subsingleton.elim (τ.rangeRestrict g) 1)
  ext v
  exact congrArg (fun a : Equiv.Perm V => a v) he

/-- Every noncentral Irr⁺ constituent for a perfect actor has dimension greater
than two over the binary prime field. -/
theorem IsIrrPlus.finrank_gt_two
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [Group.IsPerfect K]
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ K I) :
    2 < Module.finrank (ZMod 2) I := by
  by_contra hn
  have hd : Module.finrank (ZMod 2) I ≤ 2 := Nat.le_of_not_gt hn
  apply hI.not_le_fixedSpace ρ
  intro v hv k
  exact congrArg (fun f => (f (⟨v,hv⟩ : I) : V))
    (representation_eq_one_of_isPerfect_of_finrank_le_two
      (invariantSubspace ρ K I hI.choose).toRepresentation hd k)
end Representation.BinaryOffender


namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- When the component has no fixed vectors, homogeneous central-image
independence is independence of the original constituent orbit. -/
theorem IsIrrPlusWith.independent_orbit_of_fixedSpace_eq_bot
    {K A : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K A I) (hfix : fixedSpace ρ K = ⊥) :
    sSupIndep (subspaceOrbit ρ A I) := by
  classical
  let q := (fixedSpace ρ K).mkQ
  have hq : Function.Injective q := LinearMap.ker_eq_bot.mp
    ((Submodule.ker_mkQ _).trans hfix)
  let e := Submodule.orderIsoMapComapOfBijective q
    ⟨hq, (fixedSpace ρ K).mkQ_surjective⟩
  let S := quotientImage ρ K I hI.invariant
  let Ω := centralOrbit ρ K A hI.normalizes S
  let f : subspaceOrbit ρ A I → Ω := fun J =>
    ⟨centralRightConjugate ρ K A hI.normalizes S (Classical.choose J.property)⁻¹,
      ⟨(Classical.choose J.property)⁻¹,rfl⟩⟩
  have hfmap (J : subspaceOrbit ρ A I) : (f J).val.toSubmodule = e J.val := by
    change (centralRightConjugate ρ K A hI.normalizes S
      (Classical.choose J.property)⁻¹).toSubmodule = J.val.map q
    rw [centralRightConjugate_toSubmodule]
    change (I.map q).map (normalizerQuotientRepresentation ρ K
      ⟨((Classical.choose J.property : A)⁻¹ : G)⁻¹, _⟩) = _
    rw [← quotientImage_map_normalizer]
    simp only [inv_inv]
    have hJ : I.map (ρ (Classical.choose J.property : A)) = J.val :=
      Classical.choose_spec J.property
    exact congrArg (fun N : Submodule (ZMod 2) V => N.map q) hJ
  have hfinj : Function.Injective f := by
    intro J L he
    apply Subtype.ext
    apply e.injective
    exact (hfmap J).symm.trans ((congrArg (fun U : Ω => U.val.toSubmodule) he).trans (hfmap L))
  have hh := (hI.orbit_decomposition ρ).1.comp hfinj
  change iSupIndep (fun J : subspaceOrbit ρ A I => (f J).val.toSubmodule) at hh
  simp only [hfmap] at hh
  exact (sSupIndep_iff _).mpr ((iSupIndep_map_orderIso_iff e).mp hh)

/-- The common quadratic actor preserves a homogeneous constituent with no
central error, provided its action on the constituent is faithful. -/
theorem IsIrrPlusWith.quadratic_stabilizes [Finite G]
    [FiniteDimensional (ZMod 2) V]
    {K A : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K A I) (hfix : fixedSpace ρ K = ⊥)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hfaith : ∀ b ∈ A, (∀ v ∈ I, ρ b v = v) → b = 1)
    (hdim : 2 < Module.finrank (ZMod 2) I)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) : A ≤ subspaceStabilizer ρ I :=
  quadratic_stabilizes_of_independent_orbit ρ I A hA hq
    (hI.independent_orbit_of_fixedSpace_eq_bot ρ hfix) hfaith hdim hbound

end Representation.BinaryOffender.Homogeneous


namespace Representation.BinaryOffender
open Subgroup Theory.GroupTheory
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Centerlessness removes the kernel on every noncentral constituent of a
quasisimple actor. -/
theorem IsIrrPlus.component_faithful
    (K : Subgroup G) [IsQuasisimple K] {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ K I) (hZ : center K = ⊥) :
    ∀ k ∈ K, (∀ v ∈ I, ρ k v = v) → k = 1 := by
  let σ := (invariantSubspace ρ K I hI.choose).toRepresentation
  let f := actionHom σ
  have hker : f.ker ≤ center K := by
    rcases IsQuasisimple.normal_le_center_or_eq_top f.ker with hc | ht
    · exact hc
    · exfalso
      apply hI.not_le_fixedSpace ρ
      intro v hv k
      have hk : k ∈ f.ker := ht.symm ▸ (show k ∈ (⊤ : Subgroup K) from mem_top k)
      exact congrArg Subtype.val ((actionHom_eq_one_iff σ k).mp hk ⟨v,hv⟩)
  intro k hk hfix
  have hkf : (⟨k,hk⟩ : K) ∈ f.ker := (actionHom_eq_one_iff σ ⟨k,hk⟩).mpr (by
    intro v
    exact Subtype.ext (hfix v v.property))
  have he : (⟨k,hk⟩ : K) = 1 := mem_bot.mp (hZ ▸ hker hkf)
  exact congrArg (fun x : K => (x : G)) he

/-- With no component-fixed vectors, a top Irr⁺ member is an irreducible
representation of the component on the original space. -/
theorem component_irreducible_of_top_isIrrPlus
    (K : Subgroup G) (hI : IsIrrPlus ρ K ⊤) (hfix : fixedSpace ρ K = ⊥) :
    IsIrreducible (ρ.comp K.subtype) := by
  let q := (fixedSpace ρ K).mkQ
  let Q := Homogeneous.quotientImage ρ K ⊤ hI.choose
  let f : V →ₗ[ZMod 2] Q.toSubmodule := q.codRestrict Q.toSubmodule
    (fun v => ⟨v,Submodule.mem_top,rfl⟩)
  have hq : Function.Injective q := LinearMap.ker_eq_bot.mp
    ((Submodule.ker_mkQ _).trans hfix)
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact hq (congrArg Subtype.val h)
    · rintro ⟨v,w,hw,rfl⟩
      exact ⟨w,rfl⟩
  let e : RepEquiv (ρ.comp K.subtype) Q.toRepresentation :=
    { toLinearEquiv := LinearEquiv.ofBijective f hf
      isIntertwining' := by intro k; ext v; rfl }
  exact (RepEquiv.irreducible_euqiv e).mpr (Homogeneous.quotientImage_irreducible ρ hI)

/-- A quadratic elementary supplement of ratio at most two cannot permute
nontrivial homogeneous constituents of a centerless quasisimple component.
Thus an irreducible whole-actor module stays irreducible on the component. -/
theorem component_irreducible_of_quadratic_supplement
    [Finite G] [FiniteDimensional (ZMod 2) V]
    (K A : Subgroup G) [K.Normal] [IsQuasisimple K]
    (hZ : center K = ⊥) (hgen : K ⊔ A = ⊤)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set G) = ⊥)
    (hi : IsIrreducible ρ) (hn : ¬ (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ K) :
    IsIrreducible (ρ.comp K.subtype) := by
  let C : Subrepresentation ρ :=
    ⟨fixedSpace ρ K, fun g v hv => (fixedSpace_stable_of_normal ρ K (mem_top g) v).2 hv⟩
  have hfix : fixedSpace ρ K = ⊥ := by
    rcases hi.eq_bot_or_eq_top C with hb | ht
    · exact congrArg Subrepresentation.toSubmodule hb
    · exact (hn (congrArg Subrepresentation.toSubmodule ht).ge).elim
  obtain ⟨J,hJ⟩ := exists_isIrrPlus_of_not_fixed ρ K hn
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨I,_,hI⟩ := Homogeneous.exists_isIrrPlusWith_le_orbitSpan ρ
    (show A ≤ normalizer (K : Set G) from le_normalizer_of_normal)
    (IsElementaryAbelian.isPGroup 2 A) hJ
  have hf := actor_faithful_on_section ρ K A I hI.invariant
    (hI.isIrrPlus.component_faithful ρ K hZ) hI.normalizes hAC
  have hs := hI.quadratic_stabilizes ρ hfix hA hq hf
    (hI.isIrrPlus.finrank_gt_two ρ K) hc
  let S : Subrepresentation ρ := ⟨I, by
    intro g v hv
    have hg : g ∈ K ⊔ A := hgen ▸ mem_top g
    exact ((sup_le hI.invariant hs) hg v).2 hv⟩
  have hItop : I = ⊤ := by
    rcases hi.eq_bot_or_eq_top S with hb | ht
    · exact (hI.isIrrPlus.ne_bot ρ (congrArg Subrepresentation.toSubmodule hb)).elim
    · exact congrArg Subrepresentation.toSubmodule ht
  exact component_irreducible_of_top_isIrrPlus ρ K (hItop ▸ hI.isIrrPlus) hfix
end Representation.BinaryOffender
