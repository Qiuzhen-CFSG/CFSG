module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.SplitExtension
public import Theory.Mathieu.M24.LocalGeometry.OctadOrder
public import Theory.ElementaryAbelian.Basic
public import Theory.PGroupCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect octad stabilizers and their elementary two-cores

For the octad obtained by adjoining the distinguished point to the native
M₂₃ heptad, restriction identifies the pointwise octad kernel with the
already constructed heptad translation group of order sixteen. The known
octad-stabilizer order makes its permutation image an index-two subgroup
of S₈, hence exactly A₈.

The heptad complement contains a three-cycle acting without nonidentity
fixed points on the translation kernel. Its commutator map is bijective,
so the whole kernel lies in the derived subgroup. Perfectness of A₈ then
makes the octad stabilizer perfect. Every normal two-subgroup has trivial
image in A₈ and therefore lies in the elementary pointwise kernel.
Octad transitivity transports both conclusions to every native octad.

All inclusions use the proved native M₂₃--M₂₄ point-stabilizer equivalence;
no comparison with a separate code model or splitting of the octad group
is assumed.

Source: GLS, volume 3, Table 5.3e, E₁₆.A₈; Aschbacher--Smith,
A.3.12(14), combined manuscript of 1 March 2004, printed pp.47--48.
The heptad kernel and fixed-point-free action are constructed in
`Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.SplitExtension`.
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M23Geometry
open scoped Pointwise IsMulCommutative commutatorElement

namespace Sporadic.Mathieu.M24LocalGeometry.LinearFourCore

private theorem heptadKernel_le_commutator : heptadKernel ≤ commutator heptadStabilizer := by
  let : IsMulCommutative heptadKernel := ⟨⟨heptadKernel_mul_comm⟩⟩
  let a := heptadConjugation AlternatingSection.c
  let d : heptadKernel →* heptadKernel := a.toMonoidHom * (MonoidHom.id _)⁻¹
  have hd : Function.Injective d := by
    apply (MonoidHom.ker_eq_bot_iff d).mp
    apply bot_unique
    intro u hu
    have h : a u * u⁻¹ = 1 := hu
    have hf : a u = u := mul_inv_eq_one.mp h
    exact (heptadConjugation_cycle_fixed_iff u).mp hf
  have hs : Function.Surjective d := Finite.surjective_of_injective hd
  intro u hu
  obtain ⟨v, hv⟩ := hs ⟨u, hu⟩
  have he : (d v : heptadStabilizer) = ⁅AlternatingSection.s AlternatingSection.c,
      (v : heptadStabilizer)⁆ := by
    change (a v : heptadStabilizer) * (v : heptadStabilizer)⁻¹ = _
    rw [heptadConjugation_coe]
    rfl
  have hv' := congrArg (fun w : heptadKernel => (w : heptadStabilizer)) hv
  rw [he] at hv'
  change ⁅AlternatingSection.s AlternatingSection.c, (v : heptadStabilizer)⁆ = u at hv'
  rw [← hv']
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The octad extending the chosen native W₂₃ heptad. -/
noncomputable def seedOctad : Octad := ⟨m23AugmentedBlock omega, by
  rw [omega_eq_block, m23AugmentedBlockAt_eq_m24BlockAt]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩

/-- The chosen octad consists of the distinguished point and the embedded heptad. -/
theorem mem_seedOctad (i : Fin 24) : i ∈ seedOctad.val ↔
    i = (24 : Fin 24) ∨ ∃ j ∈ omega, m23PointEmbedding j = i := by
  simp [seedOctad, m23AugmentedBlock, m23LiftBlock]

/-- Restriction of native octad-stabilizer permutations to the octad itself. -/
noncomputable def action (O : Octad) : octadStabilizer O →* Equiv.Perm O.val where
  toFun g := g.val.val.subtypePerm (MulAction.mem_stabilizer_finset.mp g.property)
  map_one' := by ext a; rfl
  map_mul' g h := by ext a; rfl

/-- The restriction kernel consists exactly of the pointwise octad fixers. -/
theorem mem_action_ker (O : Octad) (g : octadStabilizer O) :
    g ∈ (action O).ker ↔ ∀ a ∈ O.val, (g : M24) • a = a := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h a ha
    exact congrArg Subtype.val (Equiv.congr_fun h ⟨a, ha⟩)
  · intro h
    exact Equiv.ext (fun a => Subtype.ext (h a.val a.property))

private noncomputable def pointLift : M23 →* MulAction.stabilizer M24 (24 : Fin 24) :=
  (m23ExtendHom.codRestrict M24 m23Extend_mem_M24).codRestrict _
    (fun g => m23ExtendHom_apply_24 g)

private theorem pointLift_surjective : Function.Surjective pointLift := by
  have hi : Function.Injective pointLift := by
    intro g h he
    apply m23ExtendHom_injective
    exact congrArg (fun k : MulAction.stabilizer M24 (24 : Fin 24) =>
      (k.val : Equiv.Perm (Fin 24))) he
  exact ((Nat.bijective_iff_injective_and_card pointLift).mpr
    ⟨hi, Nat.card_congr m23EquivM24PointStabilizer.toEquiv⟩).2

/-- Extend the native heptad stabilizer into the chosen octad stabilizer. -/
noncomputable def heptadLift : heptadStabilizer →* octadStabilizer seedOctad :=
  ((MulAction.stabilizer M24 (24 : Fin 24)).subtype.comp
    (pointLift.comp heptadStabilizer.subtype)).codRestrict _ (by
      intro g
      apply MulAction.mem_stabilizer_finset'.mpr
      intro i hi
      rcases (mem_seedOctad i).mp hi with rfl | ⟨j, hj, rfl⟩
      · apply (mem_seedOctad _).mpr
        left
        exact m23ExtendHom_apply_24 g.val
      · apply (mem_seedOctad _).mpr
        right
        refine ⟨g.val • j, (MulAction.mem_stabilizer_finset'.mp g.property) hj, ?_⟩
        exact (m23ExtendHom_apply_embedded g.val j).symm)

/-- The lift retains the actual extension permutation on the 24 points. -/
theorem heptadLift_coe (g : heptadStabilizer) :
    ((heptadLift g : M24) : Equiv.Perm (Fin 24)) = m23ExtendHom g.val := by
  apply Equiv.ext
  intro i
  rfl

/-- The lift is faithful because the native point extension is faithful. -/
theorem heptadLift_injective : Function.Injective heptadLift := by
  intro g h he
  apply Subtype.ext
  apply m23ExtendHom_injective
  exact congrArg (fun k : octadStabilizer seedOctad => (k.val : Equiv.Perm (Fin 24))) he

/-- Pointwise heptad fixers extend to pointwise octad fixers. -/
noncomputable def kernelLift : heptadKernel →* (action seedOctad).ker :=
  (heptadLift.comp heptadKernel.subtype).codRestrict _ (by
    intro u
    apply (mem_action_ker seedOctad _).mpr
    intro i hi
    rcases (mem_seedOctad i).mp hi with rfl | ⟨j, hj, rfl⟩
    · exact m23ExtendHom_apply_24 u.val.val
    · change m23ExtendHom u.val.val (m23PointEmbedding j) = m23PointEmbedding j
      rw [m23ExtendHom_apply_embedded]
      exact congrArg m23PointEmbedding ((mem_heptadKernel u.val).mp u.property j hj))

/-- Every pointwise octad fixer restricts uniquely to a pointwise heptad fixer. -/
theorem kernelLift_bijective : Function.Bijective kernelLift := by
  constructor
  · intro u v h
    apply Subtype.ext
    apply heptadLift_injective
    exact congrArg Subtype.val h
  · intro u
    have hfix := (mem_action_ker seedOctad u.val).mp u.property
    let x : MulAction.stabilizer M24 (24 : Fin 24) :=
      ⟨u.val.val, hfix _ ((mem_seedOctad _).mpr (Or.inl rfl))⟩
    obtain ⟨g, hg⟩ := pointLift_surjective x
    have he : m23ExtendHom g = (u.val.val : Equiv.Perm (Fin 24)) :=
      congrArg (fun k : MulAction.stabilizer M24 (24 : Fin 24) =>
        (k.val : Equiv.Perm (Fin 24))) hg
    have hgfix (j : Fin 23) (hj : j ∈ omega) : g • j = j := by
      apply m23PointEmbedding.injective
      change m23PointEmbedding (g.val j) = m23PointEmbedding j
      rw [← m23ExtendHom_apply_embedded, he]
      exact hfix _ ((mem_seedOctad _).mpr (Or.inr ⟨j, hj, rfl⟩))
    let k : heptadStabilizer := ⟨g, MulAction.mem_stabilizer_finset'.mpr (by
      intro j hj
      rw [hgfix j hj]
      exact hj)⟩
    refine ⟨⟨k, (mem_heptadKernel k).mpr hgfix⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact he

/-- The actual pointwise octad kernel is the native heptad translation group. -/
noncomputable def kernelEquiv : heptadKernel ≃* (action seedOctad).ker :=
  MulEquiv.ofBijective kernelLift kernelLift_bijective

/-- The pointwise octad kernel has order sixteen. -/
theorem kernel_card : Nat.card (action seedOctad).ker = 16 :=
  (Nat.card_congr kernelEquiv.toEquiv).symm.trans heptadKernel_card

/-- Every pointwise octad fixer squares to the identity. -/
theorem kernel_sq (u : (action seedOctad).ker) : u ^ 2 = 1 := by
  obtain ⟨v, rfl⟩ := kernelEquiv.surjective u
  rw [← map_pow, heptadKernel_sq, map_one]

/-- The pointwise octad kernel is commutative. -/
theorem kernel_mul_comm (u v : (action seedOctad).ker) : u * v = v * u := by
  obtain ⟨a, rfl⟩ := kernelEquiv.surjective u
  obtain ⟨b, rfl⟩ := kernelEquiv.surjective v
  rw [← map_mul, ← map_mul, heptadKernel_mul_comm]

/-- The fixed-point-free heptad three-cycle puts the kernel in the derived subgroup. -/
theorem kernel_le_commutator : (action seedOctad).ker ≤ commutator (octadStabilizer seedOctad) := by
  intro u hu
  obtain ⟨v, hv⟩ := kernelLift_bijective.2 ⟨u, hu⟩
  have he : heptadLift v.val = u := congrArg Subtype.val hv
  rw [← he]
  have hm : (commutator heptadStabilizer).map heptadLift ≤
      commutator (octadStabilizer seedOctad) := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  exact hm ⟨v.val, heptadKernel_le_commutator v.property, rfl⟩

/-- The chosen octad has eight points. -/
theorem seed_card : Nat.card seedOctad.val = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact m24Blocks_card _ seedOctad.property

/-- Its full permutation group has order 40320. -/
theorem seed_perm_card : Nat.card (Equiv.Perm seedOctad.val) = 40320 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, seed_card]
  decide

/-- The octad action image has order 20160. -/
theorem action_range_card : Nat.card (action seedOctad).range = 20160 := by
  have hc := Subgroup.card_mul_index (action seedOctad).ker
  rw [kernel_card, octadStabilizer_card, Subgroup.index_ker] at hc
  omega

/-- The octad action image has index two in the full permutation group. -/
theorem action_range_index : (action seedOctad).range.index = 2 := by
  have hc := Subgroup.card_mul_index (action seedOctad).range
  rw [action_range_card, seed_perm_card] at hc
  omega

/-- The actual octad action image is precisely A₈. -/
theorem action_range : (action seedOctad).range = alternatingGroup seedOctad.val := by
  have : (action seedOctad).range.Normal :=
    Subgroup.normal_of_index_eq_two action_range_index
  have : IsCyclic (Equiv.Perm seedOctad.val ⧸ (action seedOctad).range) :=
    isCyclic_of_prime_card action_range_index
  have hle : alternatingGroup seedOctad.val ≤ (action seedOctad).range := by
    rw [← alternatingGroup.commutator_perm_eq (by rw [seed_card]; decide)]
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  have : Nontrivial seedOctad.val := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [seed_card]; decide)
  rw [action_range_card, nat_card_alternatingGroup, seed_card]
  decide

/-- The chosen octad stabilizer is perfect: its kernel and quotient are generated by commutators. -/
theorem seed_perfect : Group.IsPerfect (octadStabilizer seedOctad) := by
  have hm : (commutator (octadStabilizer seedOctad)).map (action seedOctad) =
      (action seedOctad).range := by
    rw [map_commutator_eq, action_range,
      commutator_alternatingGroup_eq_self (by rw [seed_card]; decide)]
  have h := Subgroup.map_eq_range_iff.mp hm
  rw [codisjoint_iff, sup_eq_left.mpr kernel_le_commutator] at h
  exact ⟨h⟩

/-- The octad restriction with its exact alternating codomain. -/
noncomputable def alternatingAction : octadStabilizer seedOctad →*
    alternatingGroup seedOctad.val :=
  (action seedOctad).codRestrict _ (fun g => action_range ▸ ⟨g, rfl⟩)

/-- Every even octad permutation is induced by an element of the native stabilizer. -/
theorem alternatingAction_surjective : Function.Surjective alternatingAction := by
  intro a
  have h : a.val ∈ (action seedOctad).range := action_range.symm ▸ a.property
  obtain ⟨g, hg⟩ := h
  exact ⟨g, Subtype.ext hg⟩

/-- The intrinsic two-core fixes the octad pointwise, since A₈ has no normal two-subgroup. -/
theorem core_le_kernel : pCore 2 (octadStabilizer seedOctad) ≤ (action seedOctad).ker := by
  let N := (pCore 2 (octadStabilizer seedOctad)).map alternatingAction
  have : N.Normal := Subgroup.Normal.map inferInstance alternatingAction alternatingAction_surjective
  have hn : N = ⊥ := by
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top
      (by rw [seed_card]; decide) (N := N) with hn | hn
    · exact hn
    · have hp : IsPGroup 2 N := pCore_isPGroup.map alternatingAction
      obtain ⟨n, hncard⟩ := hp.exists_card_eq
      have : Nontrivial seedOctad.val := Finite.one_lt_card_iff_nontrivial.mp (by
        rw [seed_card]; decide)
      rw [hn, Subgroup.card_top, nat_card_alternatingGroup, seed_card] at hncard
      have hd : 3 ∣ 2 ^ n := hncard ▸ (by decide : 3 ∣ Nat.factorial 8 / 2)
      have hf : 3 ∣ 2 := (by decide : Nat.Prime 3).dvd_of_dvd_pow hd
      norm_num at hf
  intro g hg
  have hm : alternatingAction g ∈ N := ⟨g, hg, rfl⟩
  rw [hn] at hm
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hm)

/-- The intrinsic two-core of the chosen octad stabilizer is elementary abelian. -/
theorem seed_core_elementary : IsElementaryAbelian 2 (pCore 2 (octadStabilizer seedOctad)) := by
  let f : pCore 2 (octadStabilizer seedOctad) →* (action seedOctad).ker :=
    Subgroup.inclusion core_le_kernel
  have hf : Function.Injective f := Subgroup.inclusion_injective core_le_kernel
  exact {
    is_comm := ⟨fun u v => hf (by simpa only [map_mul] using kernel_mul_comm (f u) (f v))⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun u =>
      hf (by simpa only [map_pow, map_one] using kernel_sq (f u))) }

/-- Every native octad stabilizer is perfect and has elementary abelian intrinsic two-core. -/
theorem octad_core_structure (O : Octad) : Group.IsPerfect (octadStabilizer O) ∧
    IsElementaryAbelian 2 (pCore 2 (octadStabilizer O)) := by
  obtain ⟨g, hg⟩ := exists_smul_octad_eq seedOctad O
  have hs : octadStabilizer O = (octadStabilizer seedOctad).map (MulAut.conj g).toMonoidHom := by
    change MulAction.stabilizer M24 O.val = (MulAction.stabilizer M24 seedOctad.val).map _
    rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  let e : octadStabilizer seedOctad ≃* octadStabilizer O :=
    ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr hs.symm)
  have : Group.IsPerfect (octadStabilizer seedOctad) := seed_perfect
  have : IsElementaryAbelian 2 (pCore 2 (octadStabilizer seedOctad)) := seed_core_elementary
  refine ⟨Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  have h := IsElementaryAbelian.map (p := 2) (A := pCore 2 (octadStabilizer seedOctad)) e.toMonoidHom
  rwa [pCore_map_iso] at h

end Sporadic.Mathieu.M24LocalGeometry.LinearFourCore
