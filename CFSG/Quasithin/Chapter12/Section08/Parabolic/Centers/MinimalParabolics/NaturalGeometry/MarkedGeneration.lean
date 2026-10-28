module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.MinimalParabolics.NaturalGeometry
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.SylowFlags
public import Theory.ElementaryAbelian.AutomorphismLinearModelEight
public import Theory.SpecificGroups.BinaryLinear.OrderedFlagGeneration

/-!
# Marking the natural flag and generating LT

Convert the actual multiplicative automorphisms of the elementary abelian seed
into linear maps, then change coordinates in the vector space. The resulting
actor equivalence intertwines the action pointwise. The image of the original
ambient Sylow is a Sylow of the full linear group, hence the stabilizer of one
complete binary flag. Its invariant subspaces are exactly the cuts; their
dimensions identify each original Vi with the correctly labeled cut.

Thus every original minimal parabolic maps to the minimal parabolic with the
same deleted cut, under this one actor equivalence and basis. Elementary matrix
generation, proved in `BinaryLinear.OrderedFlagGeneration`, gives generation
in the natural image. The existing kernel-containment adapter lifts it to the
literal ordered parabolics of LT. No residual equality or conjugator generation
is assumed. The exported common marking also supplies the e and b needed by
the independent residual-conjugator argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Hypothesis 12.8.1, Notation 12.8.2(2), and
Lemma 12.8.3(1), printed pp.849–850; the ordinary generation step in
Lemma 12.8.10(5), printed p.854 (PDF p.871), `refs/quasithin.pdf`.
The automorphism-to-linear conversion follows
`Theory.ElementaryAbelian.AutomorphismLinearModelEight`.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G}
  [IsElementaryAbelian 2 V] {m : ℕ}

/-- Coordinates obtained from the original seed order, without choosing a new action. -/
noncomputable def naturalFlagCoordinates [Finite G] (F : InvariantFlag T V (m + 1)) :
    Additive V ≃ₗ[ZMod 2] Space (m + 1) := by
  have hc : Nat.card V = 2 ^ (m + 1) := F.last ▸ F.card (m + 1) le_rfl
  have hd : Module.finrank (ZMod 2) (Additive V) = m + 1 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    exact (h.trans (by rw [Nat.card_zmod])).symm.trans hc
  exact (Module.finBasisOfFinrankEq (ZMod 2) (Additive V) hd).equivFun

/-- Conjugation by the specified coordinates, including the additive conversion. -/
noncomputable def naturalFlagActorEquiv (β : Additive V ≃ₗ[ZMod 2] Space (m + 1)) :
    MulAut V ≃* LinearGroup (m + 1) :=
  let a : MulAut V ≃* (Additive V ≃ₗ[ZMod 2] Additive V) :=
    { toFun := fun f => { f.toAdditive with map_smul' := ZMod.map_smul f.toAdditive }
      invFun := fun f => MulEquiv.toAdditive.symm f.toAddEquiv
      left_inv := by intro f; ext; rfl
      right_inv := by intro f; ext; rfl
      map_mul' := by intro f g; ext; rfl }
  a.trans
    { toFun := fun f => β.symm.trans (f.trans β)
      invFun := fun f => β.trans (f.trans β.symm)
      left_inv := by intro f; ext v; simp
      right_inv := by intro f; ext v; simp
      map_mul' := by intro f g; ext v; simp }

theorem naturalFlagActorEquiv_intertwines
    (β : Additive V ≃ₗ[ZMod 2] Space (m + 1)) (a : MulAut V) (v : V) :
    naturalFlagActorEquiv β a (β (Additive.ofMul v)) = β (Additive.ofMul (a v)) := by
  change β (Additive.ofMul (a (β.symm (β (Additive.ofMul v))).toMul)) = _
  rw [β.symm_apply_apply]
  rfl

/-- The original subgroup, as a binary subspace in the specified coordinates. -/
noncomputable def naturalFlagSpace (F : InvariantFlag T V (m + 1))
    (β : Additive V ≃ₗ[ZMod 2] Space (m + 1)) (i : ℕ) :
    Submodule (ZMod 2) (Space (m + 1)) :=
  ((AddSubgroup.toZModSubmodule 2) ((F.Vi i).subgroupOf V).toAddSubgroup).map β.toLinearMap

theorem mem_naturalFlagSpace (F : InvariantFlag T V (m + 1))
    (β : Additive V ≃ₗ[ZMod 2] Space (m + 1)) (i : ℕ) (v : V) :
    β (Additive.ofMul v) ∈ F.naturalFlagSpace β i ↔ (v : G) ∈ F.Vi i := by
  rw [naturalFlagSpace, Submodule.mem_map_equiv, β.symm_apply_apply]
  rfl

theorem naturalFlagSpace_finrank [Finite G] (F : InvariantFlag T V (m + 1))
    (β : Additive V ≃ₗ[ZMod 2] Space (m + 1)) (i : ℕ) (hi : i ≤ m + 1) :
    Module.finrank (ZMod 2) (F.naturalFlagSpace β i) = i := by
  let W := (AddSubgroup.toZModSubmodule 2) ((F.Vi i).subgroupOf V).toAddSubgroup
  have hc : Nat.card W = 2 ^ i := by
    change Nat.card ((F.Vi i).subgroupOf V) = _
    rw [Nat.card_congr (subgroupOfEquivOfLe (F.le_seed i)).toEquiv, F.card i hi]
  have hd : Module.finrank (ZMod 2) W = i := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    exact (h.trans (by rw [Nat.card_zmod])).symm.trans hc
  change Module.finrank (ZMod 2) (W.map β.toLinearMap) = i
  rw [← hd]
  exact (W.equivMapOfInjective β.toLinearMap β.injective).finrank_eq.symm

/-- The initial member is the zero subspace in any of the specified coordinates. -/
theorem naturalFlagSpace_zero [Finite G] (F : InvariantFlag T V (m + 1))
    (β : Additive V ≃ₗ[ZMod 2] Space (m + 1)) : F.naturalFlagSpace β 0 = ⊥ :=
  Submodule.finrank_eq_zero.mp (F.naturalFlagSpace_finrank β 0 (Nat.zero_le _))

/-- The last original member fills the coordinate space. -/
theorem naturalFlagSpace_last [Finite G] (F : InvariantFlag T V (m + 1))
    (β : Additive V ≃ₗ[ZMod 2] Space (m + 1)) : F.naturalFlagSpace β (m + 1) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [F.naturalFlagSpace_finrank β (m + 1) le_rfl, Module.finrank_fin_fun]

theorem naturalFlagStabilizer_map (F : InvariantFlag T V (m + 1))
    (β : Additive V ≃ₗ[ZMod 2] Space (m + 1)) (i : ℕ) :
    (F.naturalFlagStabilizer i).map (naturalFlagActorEquiv β).toMonoidHom =
      parabolic (F.naturalFlagSpace β i) := by
  ext a
  obtain ⟨a, rfl⟩ := (naturalFlagActorEquiv β).surjective a
  rw [mem_map_equiv, MulEquiv.symm_apply_apply]
  change (∀ v : V, (a v : G) ∈ F.Vi i ↔ (v : G) ∈ F.Vi i) ↔
    ∀ w, naturalFlagActorEquiv β a w ∈ F.naturalFlagSpace β i ↔ w ∈ F.naturalFlagSpace β i
  constructor
  · intro h w
    obtain ⟨v, rfl⟩ := β.surjective w
    obtain ⟨v, rfl⟩ := Additive.ofMul.surjective v
    change naturalFlagActorEquiv β a (β (Additive.ofMul v)) ∈ _ ↔ _
    rw [naturalFlagActorEquiv_intertwines, mem_naturalFlagSpace, mem_naturalFlagSpace]
    exact h _
  · intro h v
    simpa only [naturalFlagActorEquiv_intertwines, mem_naturalFlagSpace] using h (β (Additive.ofMul v))

/-- A Sylow of the full natural action recovers all original cuts by dimension. -/
theorem exists_naturalFlag_marking [Finite G] (F : InvariantFlag T V (m + 1))
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G))
    (β : Additive V ≃ₗ[ZMod 2] Space (m + 1)) :
    ∃ b : Basis m,
      (F.naturalFlagSylow L hL hfull : Subgroup (MulAut V)).map
        (naturalFlagActorEquiv β).toMonoidHom = cutStabilizer b Set.univ ∧
      ∀ i : Fin m, F.naturalFlagSpace β (i.val + 1) = cutSpace b i := by
  let e := naturalFlagActorEquiv β
  let S := (F.naturalFlagSylow L hL hfull).mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨b, hb⟩ := sylow_eq_cutStabilizer S
  refine ⟨b, hb, ?_⟩
  intro i
  have hd := F.naturalFlagSpace_finrank β (i.val + 1) (by have := i.isLt; omega)
  have h0 : F.naturalFlagSpace β (i.val + 1) ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hd; omega
  have h1 : F.naturalFlagSpace β (i.val + 1) ≠ ⊤ := by
    intro h; rw [h, finrank_top, Module.finrank_fin_fun] at hd
    have := i.isLt; omega
  have hle : cutStabilizer b Set.univ ≤ parabolic (F.naturalFlagSpace β (i.val + 1)) := by
    rw [← hb, ← F.naturalFlagStabilizer_map β (i.val + 1)]
    exact map_mono (F.naturalFlagSylow_le_stabilizer L hL hfull (i.val + 1))
  obtain ⟨j, hj⟩ := fullFlag_invariant_subspace b _ h0 h1 hle
  have he : j = i := by
    have := cutSpace_finrank b j
    rw [hj] at hd
    exact Fin.ext (by omega)
  simpa only [he] using hj

/-- Deleting the j-th original cut deletes exactly the model node j-1. -/
theorem naturalOrderedParabolic_map_of_marking (F : InvariantFlag T V (m + 1))
    (β : Additive V ≃ₗ[ZMod 2] Space (m + 1)) (b : Basis m)
    (hcuts : ∀ i : Fin m, F.naturalFlagSpace β (i.val + 1) = cutSpace b i)
    (i : Fin m) :
    (F.naturalOrderedParabolic (i.val + 1)).map (naturalFlagActorEquiv β).toMonoidHom =
      minimalParabolic b i := by
  ext a
  obtain ⟨a, rfl⟩ := (naturalFlagActorEquiv β).surjective a
  have hc (j : Fin m) : a ∈ F.naturalFlagStabilizer (j.val + 1) ↔
      naturalFlagActorEquiv β a ∈ parabolic (cutSpace b j) := by
    rw [← hcuts j, ← F.naturalFlagStabilizer_map β (j.val + 1),
      mem_map_equiv, MulEquiv.symm_apply_apply]
  rw [mem_map_equiv, MulEquiv.symm_apply_apply]
  simp only [naturalOrderedParabolic, minimalParabolic, cutStabilizer, mem_iInf,
    Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · intro ha j hji
    apply (hc j).mp
    apply ha (j.val + 1)
    have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
    have := j.isLt
    exact ⟨by omega, by omega, by omega⟩
  · intro ha j hj
    let k : Fin m := ⟨j - 1, by omega⟩
    have hk : k.val + 1 = j := by dsimp [k]; omega
    have hki : k ≠ i := by intro he; have := congrArg Fin.val he; omega
    have h := (hc k).mpr (ha k hki)
    simpa only [hk] using h

/-- One common marking retains the pointwise action, the original Sylow,
all original cuts, and every labeled minimal parabolic. -/
theorem exists_marked_naturalFlag [Finite G] (F : InvariantFlag T V (m + 1))
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G)) :
    ∃ (β : Additive V ≃ₗ[ZMod 2] Space (m + 1))
      (e : MulAut V ≃* LinearGroup (m + 1)) (b : Basis m),
      (∀ (a : MulAut V) (v : V), e a (β (Additive.ofMul v)) = β (Additive.ofMul (a v))) ∧
      (∀ i : Fin m, F.naturalFlagSpace β (i.val + 1) = cutSpace b i) ∧
      (F.naturalFlagSylow L hL hfull : Subgroup (MulAut V)).map e.toMonoidHom =
        cutStabilizer b Set.univ ∧
      ∀ i : Fin m, (F.naturalOrderedParabolic (i.val + 1)).map e.toMonoidHom =
        minimalParabolic b i := by
  let β := F.naturalFlagCoordinates
  obtain ⟨b, hb, hc⟩ := F.exists_naturalFlag_marking L hL hfull β
  exact ⟨β, naturalFlagActorEquiv β, b, naturalFlagActorEquiv_intertwines β,
    hc, hb, F.naturalOrderedParabolic_map_of_marking β b hc⟩

/-- Generation in the full automorphism group, with the original ordered flag. -/
theorem naturalOrderedParabolic_generation [Finite G] (F : InvariantFlag T V (m + 1))
    (hm : 1 ≤ m) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G)) :
    (⨆ j : ℕ, ⨆ (_ : 1 ≤ j ∧ j < m + 1), F.naturalOrderedParabolic j) = ⊤ := by
  obtain ⟨β, e, b, _, _, _, hp⟩ := F.exists_marked_naturalFlag L hL hfull
  let A : Subgroup (MulAut V) :=
    ⨆ j : ℕ, ⨆ (_ : 1 ≤ j ∧ j < m + 1), F.naturalOrderedParabolic j
  have hle : (⨆ i : Fin m, minimalParabolic b i) ≤ A.map e.toMonoidHom := by
    apply iSup_le
    intro i
    rw [← hp i]
    apply map_mono
    exact le_iSup_of_le (i.val + 1) (le_iSup_of_le
      (show 1 ≤ i.val + 1 ∧ i.val + 1 < m + 1 by have := i.isLt; omega) le_rfl)
  rw [iSup_minimalParabolic_eq_top hm b] at hle
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [map_top_of_surjective e.toMonoidHom e.surjective]
  exact top_unique hle

/-- The source full-action input 12.8.3(1) discharges ordinary LT generation
in the induction of 12.8.10(5), retaining every original ambient stabilizer. -/
theorem orderedParabolic_generation_of_full_binary_action [Finite G]
    (F : InvariantFlag T V (m + 1)) (hm : 1 ≤ m)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G)) :
    (⨆ j : ℕ, ⨆ (_ : 1 ≤ j ∧ j < m + 1), F.orderedParabolic L j) =
      L ⊔ (T : Subgroup G) :=
  F.orderedParabolic_generation_of_natural (by omega) L hL hfull
    (F.naturalOrderedParabolic_generation hm L hL hfull)

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
