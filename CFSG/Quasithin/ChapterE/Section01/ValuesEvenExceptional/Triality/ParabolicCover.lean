module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.SpecificGroups.Triality.SylowParabolicExtensions
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The genuine triality parabolic cover in an outer two-extension

An actual equivalence from a normal subgroup L to the D4 graph-field carrier
transports its two root parabolics to G. Sylow conjugacy aligns T intersect L
with the positive root group. The two different Borel indices force every
element of T to preserve each parabolic. Consequently their joins with T
are proper, intersect L in the original parabolics, and generate G = LT.
The quotient of each join by its parabolic is a two-group. These assertions
include q = 2 and do not assume that the outer extension splits.

The positive root group has order q^12; its embedding proves even order of G.
These are geometric inputs to E.1.12, not the local E-generation calculation
or the lower obstruction required for E.1.14(2).

Source: Aschbacher--Smith, E.1.12 and E.1.14(2), printed p.214, and
F.1.12(I)(4), printed pp.263--264 (`refs/quasithin.pdf`). The standard
carrier and its root geometry follow GLS3 §§2.3--2.6.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Triality
open Subgroup
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open scoped Pointwise

variable {G : Type*} [Group G] {f : ℕ} {hf : 0 < f}

/-- The embedding comes from the genuine graph-field model equivalence. -/
def modelEmbedding (L : Subgroup G) (e : L ≃* BinaryCarrier f hf) :
    BinaryCarrier f hf →* G := L.subtype.comp e.symm.toMonoidHom

theorem modelEmbedding_injective (L : Subgroup G) (e : L ≃* BinaryCarrier f hf) :
    Function.Injective (modelEmbedding L e) := L.subtype_injective.comp e.symm.injective

theorem modelEmbedding_range (L : Subgroup G) (e : L ≃* BinaryCarrier f hf) :
    (modelEmbedding L e).range = L := by
  rw [modelEmbedding, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
    ← MonoidHom.range_eq_map, L.range_subtype]

def ambientParabolic (L : Subgroup G) (e : L ≃* BinaryCarrier f hf) (a : Node) :
    Subgroup G := (parabolic (binaryParameters f hf) a).map (modelEmbedding L e)

def parabolicOvergroup (L T : Subgroup G) (e : L ≃* BinaryCarrier f hf) (a : Node) :
    Subgroup G := ambientParabolic L e a ⊔ T

def parabolicOvergroups (L T : Subgroup G) (e : L ≃* BinaryCarrier f hf) :
    Set (Subgroup G) := Set.range (parabolicOvergroup L T e)

theorem ambientParabolic_le (L : Subgroup G) (e : L ≃* BinaryCarrier f hf) (a : Node) :
    ambientParabolic L e a ≤ L := by
  exact (map_le_range (H := parabolic (binaryParameters f hf) a)
    (f := modelEmbedding L e)).trans_eq (modelEmbedding_range L e)

theorem le_parabolicOvergroup (L T : Subgroup G) (e : L ≃* BinaryCarrier f hf)
    (a : Node) : T ≤ parabolicOvergroup L T e a := le_sup_right

theorem ambientParabolics_generate (L : Subgroup G) (e : L ≃* BinaryCarrier f hf) :
    ambientParabolic L e .arms ⊔ ambientParabolic L e .central = L := by
  rw [ambientParabolic, ambientParabolic, ← Subgroup.map_sup,
    parabolic_sup_binary _ rfl, ← MonoidHom.range_eq_map, modelEmbedding_range]

/-- An actual two-element family of T-overgroups generates G. -/
theorem parabolicOvergroups_generate (L T : Subgroup G) (e : L ≃* BinaryCarrier f hf)
    (hLT : L ⊔ T = ⊤) : sSup (parabolicOvergroups L T e) = ⊤ := by
  apply top_unique
  rw [← hLT]
  conv_lhs => rw [← ambientParabolics_generate L e]
  exact sup_le
    (sup_le (le_sup_left.trans (le_sSup (Set.mem_range_self Node.arms)))
      (le_sup_left.trans (le_sSup (Set.mem_range_self Node.central))))
    (le_sup_right.trans (le_sSup (Set.mem_range_self Node.arms)))

theorem even_card_of_model (L : Subgroup G) (e : L ≃* BinaryCarrier f hf) :
    Even (Nat.card G) := by
  let U := unipotent (binaryParameters f hf)
  have hd : Nat.card U ∣ Nat.card G := by
    rw [Nat.card_congr (U.equivMapOfInjective (modelEmbedding L e)
      (modelEmbedding_injective L e)).toEquiv]
    exact (U.map (modelEmbedding L e)).card_subgroup_dvd_card
  have hc : Nat.card U = (2 ^ f) ^ 12 := card_unipotent_binary _ rfl
  apply even_iff_two_dvd.mpr
  apply dvd_trans _ hd
  rw [hc]
  exact (dvd_pow_self 2 (Nat.ne_of_gt hf)).trans (dvd_pow_self (2 ^ f) (by decide))

/-- The source family predicate supplies even order through an actual embedding. -/
theorem not_odd_card_of_triality (L : Subgroup G)
    (hmodel : IsTrialityGroupAt (2 ^ f) L) (hf : 0 < f) : ¬ Odd (Nat.card G) := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff L f hf).mp hmodel
  exact Nat.not_odd_iff_even.mpr (even_card_of_model L e)

variable [Finite G]

/-- Conjugating the model equivalence aligns the actual intersection T ∩ L. -/
theorem exists_sylow_aligned_equiv (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf) :
    ∃ a : L ≃* BinaryCarrier f hf,
      ((T : Subgroup G).subgroupOf L).map a.toMonoidHom =
        unipotent (binaryParameters f hf) := by
  obtain ⟨Q, hQ⟩ := T.exists_subgroupOf_eq_of_normal L
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (BinaryCarrier f hf) Q'
    (unipotentSylow (binaryParameters f hf) rfl)
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have hm := congrArg Sylow.toSubgroup hg
  change ((Q : Subgroup L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at hm
  rw [hQ, map_map] at hm
  exact hm

/-- Sylow invariance fixes both nodes, including in the smallest triality group. -/
theorem sylow_normalizes_ambientParabolic (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) (a : Node) :
    (T : Subgroup G) ≤ normalizer (ambientParabolic L e a : Set G) := by
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  let b := MulAut.conjNormal (H := L) t
  let β : MulAut (BinaryCarrier f hf) := (e.symm.trans b).trans e
  have transport (K : Subgroup L) :
      (K.map e.toMonoidHom).map β.toMonoidHom =
        (K.map b.toMonoidHom).map e.toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change e (b (e.symm (e x))) = e (b x)
    rw [e.symm_apply_apply]
  have hfixed : ((T : Subgroup G).subgroupOf L).map b.toMonoidHom =
      (T : Subgroup G).subgroupOf L := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact ((T : Subgroup G).le_normalizer ht (x : G)).mp hx
    · rw [card_map_of_injective (f := b.toMonoidHom) b.injective]
  have hU : (unipotent (binaryParameters f hf)).map β.toMonoidHom =
      unipotent (binaryParameters f hf) := by
    rw [← he, transport, hfixed]
  have hPi := parabolic_map_eq_of_unipotent_invariant (binaryParameters f hf) rfl a β hU
  have hcomp : (modelEmbedding L e).comp β.toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp (modelEmbedding L e) := by
    ext x
    change ((e.symm (e (b (e.symm x))) : L) : G) =
      t * ((e.symm x : L) : G) * t⁻¹
    rw [e.symm_apply_apply]
    rfl
  change ((parabolic (binaryParameters f hf) a).map (modelEmbedding L e)).map
    (MulAut.conj t).toMonoidHom = _
  rw [map_map, ← hcomp, ← map_map, hPi]
  rfl

omit [Finite G] in
theorem sylow_inf_le_ambientParabolic (L : Subgroup G) (T : Sylow 2 G)
    (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) (a : Node) :
    (T : Subgroup G) ⊓ L ≤ ambientParabolic L e a := by
  intro x hx
  have hxU : e ⟨x, hx.2⟩ ∈ unipotent (binaryParameters f hf) :=
    he ▸ mem_map_of_mem _ hx.1
  have hxP := ((unipotent_le_borel _).trans (borel_le_parabolic _ a)) hxU
  refine ⟨e ⟨x, hx.2⟩, hxP, ?_⟩
  change ((e.symm (e ⟨x, hx.2⟩) : L) : G) = x
  rw [e.symm_apply_apply]

/-- The join with T introduces exactly the outer part of T. -/
theorem parabolicOvergroup_inf_socle (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) (a : Node) :
    parabolicOvergroup L T e a ⊓ L = ambientParabolic L e a := by
  apply le_antisymm
  · intro x hx
    have hm : x ∈ (ambientParabolic L e a : Set G) * ((T : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _
        (sylow_normalizes_ambientParabolic L T e he a)]
      exact hx.1
    obtain ⟨y, hy, t, ht, rfl⟩ := hm
    have htL : t ∈ L := by
      have h := L.mul_mem (L.inv_mem (ambientParabolic_le L e a hy)) hx.2
      simpa using h
    exact (ambientParabolic L e a).mul_mem hy
      (sylow_inf_le_ambientParabolic L T e he a ⟨ht, htL⟩)
  · exact le_inf le_sup_left (ambientParabolic_le L e a)

theorem parabolicOvergroup_ne_top (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) (a : Node) :
    parabolicOvergroup L T e a ≠ ⊤ := by
  intro h
  have hi := parabolicOvergroup_inf_socle L T e he a
  rw [h, top_inf_eq] at hi
  apply parabolic_ne_top_binary (binaryParameters f hf) rfl a
  apply map_injective (modelEmbedding_injective L e)
  rw [← MonoidHom.range_eq_map, modelEmbedding_range]
  exact hi.symm

/-- Normality is in the parabolic T-overgroup, not in G. -/
theorem ambientParabolic_normal_in_overgroup (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) (a : Node) :
    ((ambientParabolic L e a).subgroupOf (parabolicOvergroup L T e a)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (sup_le (ambientParabolic L e a).le_normalizer
      (sylow_normalizes_ambientParabolic L T e he a))

theorem parabolicOvergroup_quotient_isTwoGroup (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) (a : Node) :
    let _ := ambientParabolic_normal_in_overgroup L T e he a
    IsPGroup 2 ((parabolicOvergroup L T e a) ⧸
      (ambientParabolic L e a).subgroupOf (parabolicOvergroup L T e a)) := by
  let _ := ambientParabolic_normal_in_overgroup L T e he a
  apply isPGroup_quotient_of_sup_eq_top _
    ((T : Subgroup G).subgroupOf (parabolicOvergroup L T e a))
    T.isPGroup'.comap_subtype
  rw [← subgroupOf_sup (show ambientParabolic L e a ≤ parabolicOvergroup L T e a
      from le_sup_left) (le_parabolicOvergroup L T e a)]
  exact subgroupOf_self _

/-- Source-level construction with the model equivalence and alignment discharged. -/
theorem exists_proper_parabolic_cover (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (hf : 0 < f) (hmodel : IsTrialityGroupAt (2 ^ f) L)
    (hLT : L ⊔ (T : Subgroup G) = ⊤) :
    ∃ e : L ≃* BinaryCarrier f hf,
      ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
        unipotent (binaryParameters f hf) ∧
      sSup (parabolicOvergroups L T e) = ⊤ ∧
      ∀ a : Node, (T : Subgroup G) ≤ parabolicOvergroup L T e a ∧
        parabolicOvergroup L T e a ≠ ⊤ ∧
        parabolicOvergroup L T e a ⊓ L = ambientParabolic L e a := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff L f hf).mp hmodel
  obtain ⟨e, he⟩ := exists_sylow_aligned_equiv L T e
  exact ⟨e, he, parabolicOvergroups_generate L T e hLT, fun a =>
    ⟨le_parabolicOvergroup L T e a, parabolicOvergroup_ne_top L T e he a,
      parabolicOvergroup_inf_socle L T e he a⟩⟩

end CFSG.Quasithin.ChapterE.ExceptionalValues.Triality
