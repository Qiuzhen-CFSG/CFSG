module

public import Theory.SpecificGroups.SymmetricSeven.LocalResidualModels
public import Theory.Representation.BinaryPermutation.OddOffenderTransport
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Bounds for the three concrete seven-point residual actions

For either tetrahedral action, a fixed full vector is determined by four
orbit coordinates. Passing to the natural module in odd degree removes one
fixed dimension, leaving at most three. For the three-point cyclic action,
every displacement is supported on those three points and has zero coordinate
sum, so its commutator space has dimension at most two.

Conjugation preserves these bounds. The final conditional application uses
the literal embedded two-residual and retains both seed conditions: fixedness
under its two-core and generation by residual commutators. Recognition of an
arbitrary index-three Sylow overgroup as one of these actions remains a
separate group-theoretic premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), final proof of
15.3.1, printed p.1155; the permutation geometry is developed in I.5.
-/

@[expose] public section

open Subgroup Module Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSeven.LocalResidualModels
namespace BinaryPermutation.LocalResidualSeed

private def readCoordinates {m : ℕ} (s : Fin m → Fin 7) :
    Full (Fin 7) →ₗ[ZMod 2] (Fin m → ZMod 2) where
  toFun v := v ∘ s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem duad_full_bound :
    finrank (ZMod 2) (fixedSpace (representation (Fin 7)) (duadResidual7.pCoreIn 2)) ≤ 4 := by
  let f := (readCoordinates ![0,1,2,6]).domRestrict
    (fixedSpace (representation (Fin 7)) (duadResidual7.pCoreIn 2))
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro v hv
    have hz (j : Fin 4) : v.val (![0,1,2,6] j) = 0 := congrFun hv j
    have h0 := hz 0
    have h1 := hz 1
    have h2 := hz 2
    have h6 := hz 3
    have h3 := congrFun (v.property ⟨common7, common7_mem_duad_core⟩) 2
    have h4 := congrFun (v.property ⟨duadOther7, duadOther7_mem_core⟩) 2
    have h5 := congrFun (v.property ⟨common7, common7_mem_duad_core⟩) 4
    change v.val 3 = v.val 2 at h3
    change v.val 4 = v.val 2 at h4
    change v.val 5 = v.val 4 at h5
    apply Subtype.ext
    ext i
    fin_cases i <;> simp_all
  simpa using LinearMap.finrank_le_finrank_of_injective hf

private theorem syntheme_full_bound :
    finrank (ZMod 2) (fixedSpace (representation (Fin 7)) (synthemeResidual7.pCoreIn 2)) ≤ 4 := by
  let f := (readCoordinates ![0,2,4,6]).domRestrict
    (fixedSpace (representation (Fin 7)) (synthemeResidual7.pCoreIn 2))
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro v hv
    have hz (j : Fin 4) : v.val (![0,2,4,6] j) = 0 := congrFun hv j
    have h0 := hz 0
    have h2 := hz 1
    have h4 := hz 2
    have h6 := hz 3
    have h1 := congrFun (v.property ⟨synthemeOther7, synthemeOther7_mem_core⟩) 0
    have h3 := congrFun (v.property ⟨common7, common7_mem_syntheme_core⟩) 2
    have h5 := congrFun (v.property ⟨common7, common7_mem_syntheme_core⟩) 4
    change v.val 1 = v.val 0 at h1
    change v.val 3 = v.val 2 at h3
    change v.val 5 = v.val 4 at h5
    apply Subtype.ext
    ext i
    fin_cases i <;> simp_all
  simpa using LinearMap.finrank_le_finrank_of_injective hf

private theorem natural_bound_of_full (K : Subgroup S7)
    (h : finrank (ZMod 2) (fixedSpace (representation (Fin 7)) K) ≤ 4) :
    finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 7)) K) ≤ 3 := by
  have hcod := fixedCodim_natural_eq_full_odd (Fin 7) (by decide) K
  have hfull := fixedCodim_add_finrank (representation (Fin 7)) K
  have hnat := fixedCodim_add_finrank (naturalRepresentation (Fin 7)) K
  rw [finrank_full, Fintype.card_fin] at hfull
  rw [finrank_natural_odd (Fin 7) (by decide), Fintype.card_fin] at hnat
  omega

theorem duadResidual7_fixed_bound :
    finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 7)) (duadResidual7.pCoreIn 2)) ≤ 3 :=
  natural_bound_of_full _ duad_full_bound

theorem synthemeResidual7_fixed_bound :
    finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 7)) (synthemeResidual7.pCoreIn 2)) ≤ 3 :=
  natural_bound_of_full _ syntheme_full_bound

private noncomputable def toFull7 : natural (Fin 7) →ₗ[ZMod 2] Full (Fin 7) :=
  (core (Fin 7)).subtype.comp (coreEquivNatural (Fin 7) (by decide)).symm.toLinearMap

private theorem toFull7_injective : Function.Injective toFull7 :=
  Subtype.val_injective.comp (coreEquivNatural (Fin 7) (by decide)).symm.injective

private theorem toFull7_action (g : S7) (v : natural (Fin 7)) :
    toFull7 (naturalRepresentation (Fin 7) g v) = representation (Fin 7) g (toFull7 v) := by
  have h := coreEquivNatural_equivariant (Fin 7) (by decide) g
    ((coreEquivNatural (Fin 7) (by decide)).symm v)
  have he : (coreEquivNatural (Fin 7) (by decide)).symm
      (naturalRepresentation (Fin 7) g v) =
      coreRepresentation (Fin 7) g ((coreEquivNatural (Fin 7) (by decide)).symm v) := by
    apply (coreEquivNatural (Fin 7) (by decide)).injective
    simpa using h.symm
  exact congrArg Subtype.val he

private theorem cubic7_fixes_first (g : S7) (hg : g ∈ cubicResidual7) (i : Fin 4) :
    g (i.castLE (by decide : 4 ≤ 7)) = i.castLE (by decide : 4 ≤ 7) := by
  have h : cubicResidual7 ≤ MulAction.stabilizer S7 (i.castLE (by decide : 4 ≤ 7)) := by
    apply zpowers_le.mpr
    change cubic7 (i.castLE (by decide : 4 ≤ 7)) = i.castLE (by decide : 4 ≤ 7)
    fin_cases i <;> decide
  exact h hg

/-- The three-point residual has at most two displacement dimensions, including
when its two-core is trivial. -/
theorem cubicResidual7_commutator_bound (U : Submodule (ZMod 2) (natural (Fin 7))) :
    finrank (ZMod 2) (subspaceCommutator (naturalRepresentation (Fin 7)) U cubicResidual7) ≤ 2 := by
  let C := subspaceCommutator (naturalRepresentation (Fin 7)) U cubicResidual7
  have hz (v : C) (i : Fin 4) : toFull7 v.val (i.castLE (by decide : 4 ≤ 7)) = 0 := by
    let f : natural (Fin 7) →ₗ[ZMod 2] ZMod 2 :=
      (LinearMap.proj (i.castLE (by decide : 4 ≤ 7))).comp toFull7
    have hC : C ≤ f.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, w, _, rfl⟩
      change toFull7 (naturalRepresentation (Fin 7) g w - w) _ = 0
      rw [map_sub, toFull7_action]
      change toFull7 w (g.symm _) - toFull7 w _ = 0
      rw [g.symm_apply_eq.mpr (cubic7_fixes_first g hg i).symm, sub_self]
    exact hC v.property
  let f := ((readCoordinates ![4,5]).comp toFull7).domRestrict C
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro v hv
    have h0 := hz v 0
    have h1 := hz v 1
    have h2 := hz v 2
    have h3 := hz v 3
    change toFull7 v.val 0 = 0 at h0
    change toFull7 v.val 1 = 0 at h1
    change toFull7 v.val 2 = 0 at h2
    change toFull7 v.val 3 = 0 at h3
    have h4 : toFull7 v.val 4 = 0 := congrFun hv 0
    have h5 : toFull7 v.val 5 = 0 := congrFun hv 1
    have hs := (mem_core (Fin 7) _).mp
      ((coreEquivNatural (Fin 7) (by decide)).symm v.val).property
    change (∑ i, toFull7 v.val i) = 0 at hs
    have h6 : toFull7 v.val 6 = 0 := by
      simpa [Fin.sum_univ_succ, h0, h1, h2, h3, h4, h5] using hs
    apply Subtype.ext
    apply toFull7_injective
    ext i
    fin_cases i <;> simp_all
  simpa using LinearMap.finrank_le_finrank_of_injective hf

private theorem commutator_conj_le {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (K : Subgroup G) (g : G) (U : Submodule (ZMod 2) V) :
    subspaceCommutator ρ U (K.map (MulAut.conj g).toMonoidHom) ≤
      (subspaceCommutator ρ ⊤ K).map (ρ g) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨k, hk, rfl⟩, v, _, rfl⟩
  refine ⟨ρ k (ρ g⁻¹ v) - ρ g⁻¹ v, Submodule.subset_span ⟨k, hk, _, trivial, rfl⟩, ?_⟩
  rw [map_sub]
  change ρ g (ρ k (ρ g⁻¹ v)) - ρ g (ρ g⁻¹ v) = ρ (g * k * g⁻¹) v - v
  simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, mul_assoc]

theorem cubicResidual7_conjugate_commutator_bound (g : S7)
    (U : Submodule (ZMod 2) (natural (Fin 7))) :
    finrank (ZMod 2) (subspaceCommutator (naturalRepresentation (Fin 7)) U
      (cubicResidual7.map (MulAut.conj g).toMonoidHom)) ≤ 2 := by
  exact (Submodule.finrank_mono (commutator_conj_le (naturalRepresentation (Fin 7))
    cubicResidual7 g U)).trans ((Submodule.finrank_map_le _ _).trans
      (cubicResidual7_commutator_bound ⊤))

private theorem seven_core_conj (L : Subgroup S7) (g : S7) :
    (L.map (MulAut.conj g).toMonoidHom).pCoreIn 2 =
      (L.pCoreIn 2).map (MulAut.conj g).toMonoidHom := by
  let e := MulAut.conj g
  let eL : L ≃* L.map e.toMonoidHom := e.subgroupMap L
  rw [pCoreIn, pCoreIn, ← pCore_map_iso 2 eL, map_map, map_map]
  rfl

/-- Once the literal seven-point residual has been recognized in its permutation
action, its marked seed is impossible. The residual-recognition premise is
separate from the dimension calculation. -/
theorem seven_of_residual_conjugacy (P : Subgroup S7)
    (hmodel : ∃ g : S7,
      (pResidual 2 P).map P.subtype = duadResidual7.map (MulAut.conj g).toMonoidHom ∨
      (pResidual 2 P).map P.subtype = synthemeResidual7.map (MulAut.conj g).toMonoidHom ∨
      (pResidual 2 P).map P.subtype = cubicResidual7.map (MulAut.conj g).toMonoidHom)
    (U : Submodule (ZMod 2) (natural (Fin 7))) (hdim : finrank (ZMod 2) U = 4)
    (hfix : U ≤ fixedSpace (naturalRepresentation (Fin 7))
      (((pResidual 2 P).map P.subtype).pCoreIn 2))
    (hcomm : subspaceCommutator (naturalRepresentation (Fin 7)) U
      ((pResidual 2 P).map P.subtype) = U) : False := by
  obtain ⟨g, h | h | h⟩ := hmodel
  · have hu := Submodule.finrank_mono hfix
    rw [h, seven_core_conj,
      ← (fixedSpaceConjEquiv (naturalRepresentation (Fin 7)) (duadResidual7.pCoreIn 2) g).finrank_eq] at hu
    have hb := duadResidual7_fixed_bound
    omega
  · have hu := Submodule.finrank_mono hfix
    rw [h, seven_core_conj,
      ← (fixedSpaceConjEquiv (naturalRepresentation (Fin 7)) (synthemeResidual7.pCoreIn 2) g).finrank_eq] at hu
    have hb := synthemeResidual7_fixed_bound
    omega
  · have hb := cubicResidual7_conjugate_commutator_bound g U
    rw [← h, hcomm, hdim] at hb
    omega

end BinaryPermutation.LocalResidualSeed
