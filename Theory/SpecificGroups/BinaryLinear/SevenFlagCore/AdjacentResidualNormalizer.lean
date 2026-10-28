module
public import Theory.SpecificGroups.BinaryLinear.PerfectRadicalRows
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.ResidualNormalizers.KernelReduction
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.InvariantSubspaces
public import Theory.SpecificGroups.BinaryLinear.FourPlaneRank
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# The larger parabolic normalizes an adjacent-flag perfect residual

The perfect residual fixes the small two-dimensional block. Its kernel
in the larger parabolic lies in the adjacent flag and is normal in that
parabolic, so residual invariance gives the larger normalizer. Its two
nontrivial diagonal factors supply three-rank at least two.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.SevenFlagCore
open SmallParabolicLevi OuterCyclic InvariantNodeActions
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private instance : Finite V := Module.finite_of_finite (ZMod 2)
private instance : Finite (BinaryLinear.GL V) := Finite.of_injective (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective

omit [FiniteDimensional (ZMod 2) V] in
private theorem subspace_kernel_le_pair (U W : Submodule (ZMod 2) V) (hUW : U ≤ W) :
    (subspaceAction W).ker.map (parabolic W).subtype ≤ parabolic U ⊓ parabolic W := by
  rintro _ ⟨g,hg,rfl⟩
  refine ⟨?_,g.property⟩
  have hfix (w : V) (hw : w ∈ W) : g.val w = w :=
    congrArg Subtype.val (LinearEquiv.congr_fun hg (⟨w,hw⟩ : W))
  intro v
  change g.val v ∈ U ↔ v ∈ U
  constructor
  · intro hv
    have hw : v ∈ W := (g.property v).mp (hUW hv)
    rwa [hfix v hw] at hv
  · intro hv
    rwa [hfix v (hUW hv)]

omit [FiniteDimensional (ZMod 2) V] in
private theorem quotient_kernel_le_pair (U W : Submodule (ZMod 2) V) (hUW : U ≤ W) :
    (quotientAction U).ker.map (parabolic U).subtype ≤ parabolic U ⊓ parabolic W := by
  rintro _ ⟨g,hg,rfl⟩
  refine ⟨g.property,?_⟩
  intro v
  change g.val v ∈ W ↔ v ∈ W
  have hd : g.val v - v ∈ U :=
    (Submodule.Quotient.eq U).mp (LinearEquiv.congr_fun hg (U.mkQ v))
  constructor
  · intro hv
    have hh := W.sub_mem hv (hUW hd)
    simpa only [sub_sub_cancel] using hh
  · intro hv
    have hh := W.add_mem (hUW hd) hv
    simpa only [sub_add_cancel] using hh

private theorem subspace_pair_normalizes_residual
    (U W : Submodule (ZMod 2) V) (hUW : U ≤ W) (hd : Module.finrank (ZMod 2) W=2)
    (B : Subgroup (BinaryLinear.GL V)) [Group.IsPerfect B]
    (hB : (pResidual 2 (parabolic U ⊓ parabolic W : Subgroup (BinaryLinear.GL V))).map (parabolic U ⊓ parabolic W).subtype=B) :
    parabolic W ≤ normalizer (B : Set (BinaryLinear.GL V)) := by
  let P := parabolic U ⊓ parabolic W
  have hBP : B ≤ P := hB ▸ map_subtype_le _
  let f : B →* parabolic W := inclusion (hBP.trans inf_le_right)
  have hf := perfect_subspaceAction_eq_one W f hd
  have hBK : B ≤ (subspaceAction W).ker.map (parabolic W).subtype := by
    intro g hg
    have hgk : (subspaceAction W) (f ⟨g,hg⟩)=1 := DFunLike.congr_fun hf ⟨g,hg⟩
    exact mem_map.mpr ⟨f ⟨g,hg⟩,hgk,rfl⟩
  rw [←hB]
  apply le_normalizer_embedded_pResidual_of_sandwich 2
    ((subspaceAction W).ker.map (parabolic W).subtype) P (parabolic W)
    (subspace_kernel_le_pair U W hUW) (hB ▸ hBK) (map_subtype_le _)
  have hn := (subspaceAction W).ker.le_normalizer_map (parabolic W).subtype
  simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hn

private theorem quotient_pair_normalizes_residual
    (U W : Submodule (ZMod 2) V) (hUW : U ≤ W)
    (hd : Module.finrank (ZMod 2) (V ⧸ U)=2)
    (B : Subgroup (BinaryLinear.GL V)) [Group.IsPerfect B]
    (hB : (pResidual 2 (parabolic U ⊓ parabolic W : Subgroup (BinaryLinear.GL V))).map (parabolic U ⊓ parabolic W).subtype=B) :
    parabolic U ≤ normalizer (B : Set (BinaryLinear.GL V)) := by
  let P := parabolic U ⊓ parabolic W
  have hBP : B ≤ P := hB ▸ map_subtype_le _
  let f : B →* parabolic U := inclusion (hBP.trans inf_le_left)
  have hf := perfect_quotientAction_eq_one U f hd
  have hBK : B ≤ (quotientAction U).ker.map (parabolic U).subtype := by
    intro g hg
    have hgk := DFunLike.congr_fun hf (⟨g,hg⟩ : B)
    change quotientAction U (f ⟨g,hg⟩)=1 at hgk
    exact mem_map.mpr ⟨f ⟨g,hg⟩,hgk,rfl⟩
  rw [←hB]
  apply le_normalizer_embedded_pResidual_of_sandwich 2
    ((quotientAction U).ker.map (parabolic U).subtype) P (parabolic U)
    (quotient_kernel_le_pair U W hUW) (hB ▸ hBK) (map_subtype_le _)
  have hn := (quotientAction U).ker.le_normalizer_map (parabolic U).subtype
  simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hn

private theorem blocks_rank (r s : ℕ) (hr : r=2 ∨ r=3) (hs : s=2 ∨ s=3) :
    2 ≤ primeRank 3 (LinearGroup r × LinearGroup s) := by
  have hpos (n : ℕ) (hn : n=2 ∨ n=3) : 1 ≤ primeRank 3 (LinearGroup n) := by
    have hc : 3 ∣ Nat.card (LinearGroup n) := by
      rcases hn with rfl | rfl
      · rw [Nat.card_congr linearTwoEquivSymmetricThree.toEquiv,Nat.card_perm,Nat.card_fin]
        decide
      · rw [←Nat.card_congr (slEquivLinear 3).toEquiv,Matrix.PSL3Two.card_SL]
        decide
    have hne : primeRank 3 (LinearGroup n) ≠ 0 := by
      intro he
      exact (PrimeRank.eq_zero_iff_not_dvd_card.mp he) hc
    omega
  rw [primeRank_prod_eq_add]
  have := hpos r hr
  have := hpos s hs
  omega

private theorem middle_parabolic_rank (W : Submodule (ZMod 2) (Space 5))
    (hW : Module.finrank (ZMod 2) W=2 ∨ Module.finrank (ZMod 2) W=3) :
    2 ≤ primeRank 3 (parabolic W) := by
  let r := Module.finrank (ZMod 2) W
  let s := Module.finrank (ZMod 2) (Space 5 ⧸ W)
  have hsum : r+s=5 := by
    have hh := W.finrank_quotient_add_finrank
    simpa only [Space,Module.finrank_pi,Fintype.card_fin,Nat.add_comm] using hh
  let a := (Module.finBasis (ZMod 2) W).equivFun
  let b := (Module.finBasis (ZMod 2) (Space 5 ⧸ W)).equivFun
  rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
    (pCore 2 (parabolic W)) pCore_isPGroup,
    primeRank_equiv 3 (quotientTwoCoreEquivOfCoordinates W a b)]
  exact blocks_rank r s hW (by rcases hW with hW | hW <;> dsimp [r] at hsum <;> omega)

private theorem pair_eq (b : Basis 4) (i j : Fin 4) :
    cutStabilizer b ({i,j} : Set (Fin 4)) = parabolic (cutSpace b i) ⊓ parabolic (cutSpace b j) := by
  ext g
  simp only [cutStabilizer,mem_iInf,Set.mem_insert_iff,Set.mem_singleton_iff,
    forall_eq_or_imp,forall_eq,mem_inf]

/-- The actual perfect two-residual of either surviving adjacent flag has
normalizer of three-rank at least two in GL5(2). -/
theorem adjacent_perfect_residual_normalizer_rank
    (b : Basis 4) (last : Bool) (B : Subgroup (LinearGroup 5)) [Group.IsPerfect B]
    (hB : let cuts : Set (Fin 4) := if last then {2,3} else {0,1}
      let P := cutStabilizer b cuts
      (pResidual 2 P).map P.subtype=B) :
    2 ≤ primeRank 3 (normalizer (B : Set (LinearGroup 5))) := by
  cases last
  · change (pResidual 2 (cutStabilizer b ({0,1} : Set (Fin 4)))).map (cutStabilizer b ({0,1} : Set (Fin 4))).subtype=B at hB
    rw [pair_eq] at hB
    have hn := subspace_pair_normalizes_residual (cutSpace b 0) (cutSpace b 1)
      (cutSpace_mono b (by decide)) (by rw [cutSpace_finrank]; rfl) B hB
    exact (middle_parabolic_rank (cutSpace b 1) (Or.inl (by rw [cutSpace_finrank]; rfl))).trans
      (primeRank_mono 3 hn)
  · change (pResidual 2 (cutStabilizer b ({2,3} : Set (Fin 4)))).map (cutStabilizer b ({2,3} : Set (Fin 4))).subtype=B at hB
    rw [pair_eq] at hB
    have hd : Module.finrank (ZMod 2) (Space 5 ⧸ cutSpace b 2)=2 := by
      have hh := (cutSpace b 2).finrank_quotient_add_finrank
      have hW : Module.finrank (ZMod 2) (cutSpace b 2)=3 := by rw [cutSpace_finrank]; rfl
      have hV : Module.finrank (ZMod 2) (Space 5)=5 := by simp [Space]
      change Module.finrank (ZMod 2) (Space 5 ⧸ cutSpace b 2) +
        Module.finrank (ZMod 2) (cutSpace b 2) = Module.finrank (ZMod 2) (Space 5) at hh
      rw [hW,hV] at hh
      omega
    have hn := quotient_pair_normalizes_residual (cutSpace b 2) (cutSpace b 3)
      (cutSpace_mono b (by decide)) hd B hB
    exact (middle_parabolic_rank (cutSpace b 2) (Or.inr (by rw [cutSpace_finrank]; rfl))).trans
      (primeRank_mono 3 hn)

end BinaryLinear.SevenFlagCore
