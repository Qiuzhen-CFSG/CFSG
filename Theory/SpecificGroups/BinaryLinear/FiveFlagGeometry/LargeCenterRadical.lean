module
public import Theory.SpecificGroups.BinaryLinear.RadicalCardinality
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.ParabolicAutomorphisms
public import Theory.SpecificGroups.BinaryLinear.NestedRadicals
public import Theory.Representation.BinaryRadicalFlag.Normalizer
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Large central subgroups identify binary five-space radicals

The canonical flag of a two-radical subgroup P has a nonzero proper cut W.
The full radical at W lies in P, since it is a normal two-subgroup of the
flag stabilizer N(P). A central subgroup E of P lies in that radical's
centralizer, hence in the radical itself. If E has order 64, displacement
cardinality forces dim(W) = 2 or 3 and E to be the entire radical. Its
self-centralization then gives P = E.

Consequently every automorphism preserving this particular radical is
inner: it preserves a maximal parabolic in odd dimension five. This keeps
the actual source subgroup and avoids any global inner-automorphism claim.
Source application: Aschbacher--Smith C.2.7 and C.4.8, printed pp.145--154,
in the ordinary L₅(2) branch of 12.1.11, printed p.794.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear.FiveFlagGeometry
open OuterCyclic InvariantNodeActions

private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5))
    DFunLike.coe_injective

private def natural : Representation (ZMod 2) (LinearGroup 5) (Space 5) where
  toFun g := g.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem natural_injective : Function.Injective natural := by
  intro g h he
  exact LinearEquiv.ext (LinearMap.congr_fun he)

private theorem exists_radical_cut (P : Subgroup (LinearGroup 5))
    (hP : P.IsPRadical 2) :
    ∃ W : Submodule (ZMod 2) (Space 5),
      W ≠ ⊥ ∧ W ≠ ⊤ ∧ radical W ≤ P := by
  obtain ⟨k,W,hk,_,hs,hproper,hN⟩ :=
    Representation.BinaryRadical.exists_partialFlag_normalizer natural natural_injective P hP
  let i : Fin k := ⟨0,hk⟩
  have hN' : normalizer (P : Set (LinearGroup 5)) = ⨅ j, parabolic (W j) := hN
  refine ⟨W i,(hproper i).1,(hproper i).2,?_⟩
  have hle : radical (W i) ≤ (normalizer (P : Set (LinearGroup 5))).pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes (radical_two _) ?_ ?_
    · rw [hN']
      intro g hg
      simp only [mem_iInf]
      intro j
      rcases le_total i j with hij | hji
      · exact radical_le_nested_parabolic (hs.monotone hij) hg
      · exact radical_le_smaller_parabolic (hs.monotone hji) hg
    · apply le_trans _ (parabolic_le_normalizer (W i))
      rw [hN']
      exact iInf_le _ i
  exact hle.trans_eq hP.2

private theorem exists_basis_cut (W : Submodule (ZMod 2) (Space 5))
    (hd : Module.finrank (ZMod 2) W = 2 ∨ Module.finrank (ZMod 2) W = 3) :
    ∃ (b : FiveBasis) (i : Fin 4), (i = 1 ∨ i = 2) ∧ W = flagSpace b i := by
  let b : FiveBasis := Pi.basisFun (ZMod 2) (Fin 5)
  have h (i : Fin 4) (hi : i = 1 ∨ i = 2)
      (hdim : Module.finrank (ZMod 2) W = i.val + 1) :
      ∃ (b : FiveBasis) (i : Fin 4), (i = 1 ∨ i = 2) ∧ W = flagSpace b i := by
    obtain ⟨g,hg⟩ := FourParabolicAction.exists_linearEquiv_map_eq (flagSpace b i) W
      ((cutSpace_finrank b i).trans hdim.symm)
    refine ⟨b.map g,i,hi,?_⟩
    exact (hg.symm.trans (cutSpace_map b g i).symm)
  rcases hd with hd | hd
  · exact h 1 (Or.inl rfl) hd
  · exact h 2 (Or.inr rfl) hd

/-- A central subgroup of order 64 fills the actual radical and identifies
its normalizer as a marked middle maximal parabolic. -/
theorem radical_eq_middle_of_central_sixtyFour
    (P E : Subgroup (LinearGroup 5)) (hP : P.IsPRadical 2)
    (hE : Nat.card E = 64) (hEP : E ≤ (center P).map P.subtype) :
    P = E ∧ ∃ (b : FiveBasis) (i : Fin 4),
      (i = 1 ∨ i = 2) ∧ P = radical (flagSpace b i) ∧
      normalizer (P : Set (LinearGroup 5)) = flagStabilizer b {i} := by
  obtain ⟨W,hW0,hWt,hWP⟩ := exists_radical_cut P hP
  have hER : E ≤ radical W := by
    intro e he
    apply centralizer_radical_le hW0 hWt
    apply mem_centralizer_iff.mpr
    intro g hg
    obtain ⟨z,hz,rfl⟩ := hEP he
    exact congrArg P.subtype (mem_center_iff.mp hz ⟨g,hWP hg⟩)
  have hcard : 64 ≤ 2 ^ (Module.finrank (ZMod 2) W *
      (5 - Module.finrank (ZMod 2) W)) := by
    calc
      64 = Nat.card E := hE.symm
      _ ≤ Nat.card (radical W) :=
        Nat.card_le_card_of_injective (inclusion hER) (inclusion_injective hER)
      _ ≤ _ := by simpa only [Module.finrank_fin_fun] using radical_card_le W
  have hdim_le : Module.finrank (ZMod 2) W ≤ 5 := by
    simpa only [Module.finrank_fin_fun] using Submodule.finrank_le W
  have hd : Module.finrank (ZMod 2) W = 2 ∨ Module.finrank (ZMod 2) W = 3 := by
    interval_cases h : Module.finrank (ZMod 2) W <;> norm_num at hcard
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hRE : radical W = E := by
    apply (eq_of_le_of_card_ge hER ?_).symm
    rw [hE]
    have hc := radical_card_le W
    rcases hd with hd | hd <;> simpa [Module.finrank_fin_fun,hd] using hc
  have hPE : P = E := by
    apply le_antisymm _ (hRE ▸ hWP)
    rw [←hRE]
    intro p hp
    apply centralizer_radical_le hW0 hWt
    apply mem_centralizer_iff.mpr
    intro g hg
    obtain ⟨z,hz,rfl⟩ := hEP (hRE ▸ hg)
    exact (congrArg P.subtype (mem_center_iff.mp hz ⟨p,hp⟩)).symm
  obtain ⟨b,i,hi,hWi⟩ := exists_basis_cut W hd
  have hPR : P = radical (flagSpace b i) := hPE.trans (hRE.symm.trans (congrArg radical hWi))
  refine ⟨hPE,b,i,hi,hPR,?_⟩
  rw [hPR,normalizer_radical (flagSpace_ne_bot b i),flagStabilizer_singleton]

/-- Automorphisms preserving the original radical with a central 64-group
are inner, without assuming that every ambient automorphism is inner. -/
theorem radical_preserving_is_inner_of_central_sixtyFour
    (P E : Subgroup (LinearGroup 5)) (hP : P.IsPRadical 2)
    (hE : Nat.card E = 64) (hEP : E ≤ (center P).map P.subtype)
    (a : MulAut (LinearGroup 5)) (ha : P.map a.toMonoidHom = P) :
    a ∈ MulAut.innerSubgroup (LinearGroup 5) := by
  obtain ⟨_,b,i,_,_,hN⟩ := radical_eq_middle_of_central_sixtyFour P E hP hE hEP
  apply singleton_flag_preserving_is_inner b i a
  rw [←hN,map_normalizer_eq_of_bijective _ a.bijective,ha]

end BinaryLinear.FiveFlagGeometry
