module

public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.LocalClassification.QuotientOrders
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Parabolics
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PairQuotients

/-!
# Orders of native M₂₂ Sylow overgroups in pair and hexad stabilizers

The genuine actions have kernels of order sixteen. An ambient Sylow
two-subgroup contains the relevant kernel, so the order of its overgroup is
sixteen times its image order. A relatively normal solvable seed remains
relatively normal and solvable in the image. Its factor of three survives:
the kernel of the restriction to the seed has order dividing sixteen.
The A₆ and S₅ order reductions therefore give image order 24 and native order
384. Actual M₂₂ conjugation carries the marked-pair calculation to every pair.

The exposed hexad homomorphism is the genuine six-point restriction, with its
permutation coordinates recorded by `hexadRestriction_apply`. No abstract
extension shape replaces that action.

Source: Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973). These order
results do not yet classify the native conjugacy types or place the pair
branch in a hexad.
-/

public section

open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Mathieu.M22SolvableSylow.LocalClassification

private theorem normal_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (D X : Subgroup G) (hDX : D ≤ X)
    (hN : (D.subgroupOf X).Normal) :
    ((D.map f).subgroupOf (X.map f)).Normal := by
  apply (normal_subgroupOf_iff (map_mono hDX)).mpr
  rintro _ _ ⟨d, hd, rfl⟩ ⟨x, hx, rfl⟩
  simpa only [map_mul, map_inv] using
    mem_map_of_mem f ((normal_subgroupOf_iff hDX).mp hN d x hd hx)

private theorem three_dvd_map {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (hk : Nat.card f.ker = 16) (D : Subgroup G)
    (h3 : 3 ∣ Nat.card D) : 3 ∣ Nat.card (D.map f) := by
  have he := (f.ker.subgroupOf D).card_mul_index
  change Nat.card (f.ker.subgroupOf D) * f.ker.relIndex D = _ at he
  rw [relIndex_ker] at he
  have hd : Nat.card (f.ker.subgroupOf D) ∣ 16 := by
    rw [← card_map_of_injective D.subtype_injective, subgroupOf_map_subtype, ← hk]
    exact card_dvd_of_le inf_le_left
  rw [← he] at h3
  rcases Nat.prime_three.dvd_mul.mp h3 with h | h
  · exact (by decide : ¬ 3 ∣ 16) (dvd_trans h hd) |>.elim
  · exact h

private theorem restricted_seed_image {G H : Type*} [Group G] [Group H] [Finite G]
    (L X D : Subgroup G) (hXL : X ≤ L) (hDX : D ≤ X)
    (hN : (D.subgroupOf X).Normal) (hsol : Group.IsSolvable D) (h3 : 3 ∣ Nat.card D)
    (f : L →* H) (hk : Nat.card f.ker = 16) :
    let I := (X.subgroupOf L).map f
    let E := (D.subgroupOf L).map f
    E ≤ I ∧ (E.subgroupOf I).Normal ∧ Group.IsSolvable E ∧ 3 ∣ Nat.card E := by
  have hDL := hDX.trans hXL
  have hle : D.subgroupOf L ≤ X.subgroupOf L := fun _ hd => hDX hd
  have hn : ((D.subgroupOf L).subgroupOf (X.subgroupOf L)).Normal := by
    apply (normal_subgroupOf_iff hle).mpr
    intro d x hd hx
    exact (normal_subgroupOf_iff hDX).mp hN d.val x.val hd hx
  have hs : Group.IsSolvable (D.subgroupOf L) := by
    let := hsol
    exact Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hDL).toMonoidHom) (subgroupOfEquivOfLe hDL).injective
  let := hs
  refine ⟨map_mono hle, normal_map f _ _ hle hn,
    Group.isSolvable_of_surjective (f.subgroupMap_surjective _), three_dvd_map f hk _ ?_⟩
  rwa [Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv]

private theorem image_card_mul {G H : Type*} [Group G] [Group H]
    (f : G →* H) (X : Subgroup G) (hk : f.ker ≤ X) :
    Nat.card f.ker * Nat.card (X.map f) = Nat.card X := by
  have h := (f.ker.subgroupOf X).card_mul_index
  change Nat.card (f.ker.subgroupOf X) * f.ker.relIndex X = _ at h
  rw [relIndex_ker, Nat.card_congr (subgroupOfEquivOfLe hk).toEquiv] at h
  exact h

private theorem sylow_card (U : Sylow 2 M22) : Nat.card U = 128 := by
  rw [U.card_eq_multiplicity, m22_order]
  decide +kernel

/-- The actual restriction to the six points, with codomain A₆. -/
@[expose] noncomputable def hexadRestriction {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    stabilizer M22 B →* alternatingGroup (Fin 6) :=
  (m22HexadQuotientAlternatingEquiv hB).toMonoidHom.comp
    (QuotientGroup.mk' (m22SetAction B).ker)

theorem hexadRestriction_surjective {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Function.Surjective (hexadRestriction hB) :=
  (m22HexadQuotientAlternatingEquiv hB).surjective.comp (QuotientGroup.mk'_surjective _)

theorem hexadRestriction_ker {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (hexadRestriction hB).ker = (m22SetAction B).ker := by
  dsimp [hexadRestriction]
  rw [MonoidHom.ker_mulEquiv_comp, QuotientGroup.ker_mk']

@[simp] theorem hexadRestriction_apply {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : stabilizer M22 B) :
    (hexadRestriction hB g : Equiv.Perm (Fin 6)) = m22HexadAction hB g := rfl

/-- The genuine restriction kernel lies in every ambient Sylow overgroup
inside this hexad stabilizer. -/
theorem hexadRestriction_ker_le {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (X : Subgroup M22) (hXB : X ≤ stabilizer M22 B)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) :
    (hexadRestriction hB).ker ≤ X.subgroupOf (stabilizer M22 B) := by
  obtain ⟨U, hU⟩ := hU
  rw [hexadRestriction_ker]
  intro u hu
  exact hU (kernel_le_of_sylow hB U (hU.trans hXB) ⟨u, hu, rfl⟩)

/-- The order formula retains the actual six-point image and the kernel of
order sixteen. -/
theorem hexad_card_formula {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (X : Subgroup M22) (hXB : X ≤ stabilizer M22 B)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) :
    Nat.card X = 16 * Nat.card ((X.subgroupOf (stabilizer M22 B)).map
      (hexadRestriction hB)) := by
  have hm := image_card_mul (hexadRestriction hB) (X.subgroupOf _)
    (hexadRestriction_ker_le hB X hXB hU)
  rw [hexadRestriction_ker, m22HexadKernel_card hB,
    Nat.card_congr (subgroupOfEquivOfLe hXB).toEquiv] at hm
  exact hm.symm

/-- A Sylow overgroup in a hexad stabilizer has image of order 24 in its genuine
A₆ quotient if it has a relatively normal solvable seed divisible by three. -/
theorem hexad_image_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (X D : Subgroup M22) (hXB : X ≤ stabilizer M22 B) (hDX : D ≤ X)
    (hN : (D.subgroupOf X).Normal) (hsol : Group.IsSolvable D) (h3 : 3 ∣ Nat.card D)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) :
    Nat.card ((X.subgroupOf (stabilizer M22 B)).map (hexadRestriction hB)) = 24 := by
  obtain ⟨U, hU⟩ := hU
  have hk : Nat.card (hexadRestriction hB).ker = 16 := by
    rw [hexadRestriction_ker, m22HexadKernel_card hB]
  obtain ⟨hle, hn, hs, ht⟩ := restricted_seed_image _ X D hXB hDX hN hsol h3
    (hexadRestriction hB) hk
  apply a6_card_of_seed _ _ hle hn hs ht
  have hm := hexad_card_formula hB X hXB ⟨U, hU⟩
  have hdiv : 128 ∣ Nat.card X := (sylow_card U) ▸ card_dvd_of_le hU
  omega

/-- The native order consequence in every hexad. -/
theorem hexad_order {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (X D : Subgroup M22) (hXB : X ≤ stabilizer M22 B) (hDX : D ≤ X)
    (hN : (D.subgroupOf X).Normal) (hsol : Group.IsSolvable D) (h3 : 3 ∣ Nat.card D)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) : Nat.card X = 384 := by
  have hi := hexad_image_card hB X D hXB hDX hN hsol h3 hU
  have hm := hexad_card_formula hB X hXB hU
  rw [hi] at hm
  exact hm

open M22ValueBound.Concrete

/-- The five-hexad kernel is contained in every ambient Sylow overgroup
inside the marked pair stabilizer. -/
theorem pairAction_ker_le (X : Subgroup M22) (hX : X ≤ first)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) :
    pairAction.ker ≤ X.subgroupOf first := by
  obtain ⟨U, hU⟩ := hU
  have hkU := (IsPGroup.of_card (n := 4) pairAction_ker_card).le_sylow_of_normal
    (U.subtype (hU.trans hX))
  exact fun u hu => hU (hkU hu)

/-- The order formula for the actual action on the five hexads through the
marked pair. -/
theorem pair_card_formula (X : Subgroup M22) (hX : X ≤ first)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) :
    Nat.card X = 16 * Nat.card ((X.subgroupOf first).map pairAction) := by
  have hm := image_card_mul pairAction (X.subgroupOf first) (pairAction_ker_le X hX hU)
  rw [pairAction_ker_card, Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv] at hm
  exact hm.symm

/-- The five-hexad action of a Sylow overgroup in the marked pair stabilizer has
image of order 24. Normality of the solvable seed is only relative to X. -/
theorem pair_image_card (X D : Subgroup M22) (hX : X ≤ first) (hDX : D ≤ X)
    (hN : (D.subgroupOf X).Normal) (hsol : Group.IsSolvable D) (h3 : 3 ∣ Nat.card D)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) :
    Nat.card ((X.subgroupOf first).map pairAction) = 24 := by
  obtain ⟨U, hU⟩ := hU
  obtain ⟨hle, hn, hs, ht⟩ := restricted_seed_image first X D hX hDX hN hsol h3
    pairAction pairAction_ker_card
  apply s5_card_of_seed _ _ hle hn hs ht
  have hm := pair_card_formula X hX ⟨U, hU⟩
  have hdiv : 128 ∣ Nat.card X := (sylow_card U) ▸ card_dvd_of_le hU
  omega

/-- The order consequence for the marked pair stabilizer. -/
theorem standard_pair_order (X D : Subgroup M22) (hX : X ≤ first) (hDX : D ≤ X)
    (hN : (D.subgroupOf X).Normal) (hsol : Group.IsSolvable D) (h3 : 3 ∣ Nat.card D)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) : Nat.card X = 384 := by
  have hi := pair_image_card X D hX hDX hN hsol h3 hU
  have hm := pair_card_formula X hX hU
  rw [hi] at hm
  exact hm

/-- Two-transitivity carries any actual pair to the marked pair. -/
theorem exists_smul_pair_eq_standard {S : Finset (Fin 22)} (hS : S.card = 2) :
    ∃ g : M22, g • S = m22Pair12 := by
  rcases Finset.card_eq_two.mp hS with ⟨x, y, hxy, rfl⟩
  obtain ⟨g, hg1, hg2⟩ := (MulAction.is_two_pretransitive_iff.mp m22_isTwoPretransitive)
    hxy (by decide : (1 : Fin 22) ≠ 2)
  refine ⟨g, ?_⟩
  rw [Finset.smul_finset_insert, Finset.smul_finset_singleton, hg1, hg2]
  rfl

/-- The same native order conclusion holds in every pair stabilizer. -/
theorem pair_order {S : Finset (Fin 22)} (hS : S.card = 2)
    (X D : Subgroup M22) (hX : X ≤ stabilizer M22 S) (hDX : D ≤ X)
    (hN : (D.subgroupOf X).Normal) (hsol : Group.IsSolvable D) (h3 : 3 ∣ Nat.card D)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) : Nat.card X = 384 := by
  obtain ⟨g, hg⟩ := exists_smul_pair_eq_standard hS
  let e := MulAut.conj g
  have hX' : X.map e.toMonoidHom ≤ first := by
    have hm := map_mono (f := e.toMonoidHom) hX
    rwa [← stabilizer_smul_eq_stabilizer_map_conj g S, hg] at hm
  have hs : Group.IsSolvable (D.map e.toMonoidHom) := by
    let := hsol
    exact Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective D)
  have ht : 3 ∣ Nat.card (D.map e.toMonoidHom) := by
    rwa [card_map_of_injective e.injective]
  have hU' : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X.map e.toMonoidHom := by
    obtain ⟨U, hU⟩ := hU
    exact ⟨U.mapSurjective e.surjective, map_mono hU⟩
  have hc := standard_pair_order (X.map e.toMonoidHom) (D.map e.toMonoidHom)
    hX' (map_mono hDX) (normal_map e.toMonoidHom D X hDX hN) hs ht hU'
  rwa [card_map_of_injective e.injective] at hc

end Sporadic.Mathieu.M22SolvableSylow.LocalClassification
