/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianZeroRoots.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianEdgeRoots
public import Theory.AtlasPort.Janko2.Lattices.IcosianAxisRoots
public import Theory.AtlasPort.Janko2.Lattices.IcosianRootNormShapes

/-!
# Icosian Zero Roots

Roots with first coordinate zero are exactly two axis families and
the norm-two edge pairs. Their explicit disjoint parametrization
gives the cardinality 1200.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianZeroRoots.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra

/-- With the first coordinate zero, only two axis families and the norm-two pair remain. -/
theorem icosianRoot_zero_structure (r : IcosianRoot) (hz : r.val 0=0) :
    r.val 1=0 ∨ r.val 2=0 ∨
      (icosianNorm (r.val 1).val=2 ∧ icosianNorm (r.val 2).val=2) := by
  let n := fun i => icosianIntegralNorm (r.val i)
  have hn0 : n 0=0 := by
    apply goldenIntegerToRational_injective
    rw [icosianIntegralNorm_spec,hz]
    simp [icosianNorm]
  have hzero (i : Fin 3) (hi : n i=0) : r.val i=0 := by
    apply (icosianIntegralNorm_real_zero _).mp
    change (n i).re=0
    rw [hi]; rfl
  rcases icosianRoot_norm_shapes r.val r.property.1 r.property.2 with hA | hB | hC | hD
  · change List.Perm [n 0,n 1,n 2] [0,0,4] at hA
    rw [hn0] at hA
    have hm : (0 : GoldenInteger)∈[n 1,n 2] := hA.cons_inv.mem_iff.mpr (by simp)
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hm
    rcases hm with h | h
    · exact Or.inl (hzero 1 h.symm)
    · exact Or.inr (Or.inl (hzero 2 h.symm))
  · change List.Perm [n 0,n 1,n 2] [0,2,2] at hB
    rw [hn0] at hB
    have h1 : n 1=2 := by simpa using hB.cons_inv.mem_iff.mp (show n 1∈[n 1,n 2] by simp)
    have h2 : n 2=2 := by simpa using hB.cons_inv.mem_iff.mp (show n 2∈[n 1,n 2] by simp)
    dsimp only [n] at h1 h2
    refine Or.inr (Or.inr ⟨?_,?_⟩)
    · rw [← icosianIntegralNorm_spec,h1]; rfl
    · rw [← icosianIntegralNorm_spec,h2]; rfl
  · have hm := hC.mem_iff.mp (show (0 : GoldenInteger)∈[n 0,n 1,n 2] by rw [hn0]; simp)
    norm_num at hm
  · have hm := hD.mem_iff.mp (show (0 : GoldenInteger)∈[n 0,n 1,n 2] by rw [hn0]; simp)
    norm_num [QuadraticAlgebra.ext_iff] at hm

abbrev IcosianZeroRoot := {r : IcosianRoot // r.val 0=0}
abbrev IcosianZeroAxisParameters := {i : Fin 3 // i≠0} × icosianNormOneGroup

def icosianZeroRootEncode : (IcosianZeroAxisParameters ⊕ IcosianEdgePair) → IcosianZeroRoot
  | .inl p => ⟨icosianAxisRoot (p.1.val,p.2),by
      simp [icosianAxisRoot,icosianSingle,Ne.symm p.1.property]⟩
  | .inr p => ⟨icosianEdgeRootBase p,icosianEdgeRootBase_zero p⟩

theorem icosianZeroRootEncode_injective : Function.Injective icosianZeroRootEncode := by
  intro x y h
  have he := congrArg Subtype.val h
  cases x with
  | inl p =>
    cases y with
    | inl q =>
      have hh := icosianAxisRoot_injective he
      have h1 := congrArg Prod.fst hh
      have h2 := congrArg Prod.snd hh
      exact congrArg Sum.inl (Prod.ext (Subtype.ext h1) h2)
    | inr q =>
      change icosianAxisRoot (p.1.val,p.2)=icosianEdgeRootBase q at he
      have ha := icosianRoot_single_norm (icosianAxisRoot (p.1.val,p.2)) p.1.val
        (fun j hj => by simp [icosianAxisRoot,icosianSingle,hj])
      rw [he] at ha
      rw [icosianEdgeRootBase_norm q p.1.val p.1.property] at ha
      have hh := congrArg QuadraticAlgebra.re ha
      norm_num [QuadraticAlgebra.re_ofNat] at hh
  | inr p =>
    cases y with
    | inl q =>
      change icosianEdgeRootBase p=icosianAxisRoot (q.1.val,q.2) at he
      have ha := icosianRoot_single_norm (icosianAxisRoot (q.1.val,q.2)) q.1.val
        (fun j hj => by simp [icosianAxisRoot,icosianSingle,hj])
      rw [← he] at ha
      rw [icosianEdgeRootBase_norm p q.1.val q.1.property] at ha
      have hh := congrArg QuadraticAlgebra.re ha
      norm_num [QuadraticAlgebra.re_ofNat] at hh
    | inr q =>
      apply congrArg Sum.inr
      apply Subtype.ext
      exact Prod.ext (Subtype.ext (congrArg (fun r : IcosianRoot => r.val 1) he))
        (Subtype.ext (congrArg (fun r : IcosianRoot => r.val 2) he))

theorem icosianZeroRootEncode_surjective : Function.Surjective icosianZeroRootEncode := by
  rintro ⟨r,hz⟩
  have haxis (ha : IsIcosianAxisRoot r) :
      ∃ x,icosianZeroRootEncode x=⟨r,hz⟩ := by
    obtain ⟨p,hp⟩ := icosianAxisRoot_surjective ⟨r,ha⟩
    have hi : p.1≠0 := by
      intro h0
      have hn := icosianAxisRoot_nonzero p
      rw [hp,h0,hz] at hn
      exact hn rfl
    exact ⟨Sum.inl (⟨p.1,hi⟩,p.2),Subtype.ext hp⟩
  rcases icosianRoot_zero_structure r hz with h1 | h2 | hn
  · apply haxis
    refine ⟨2,?_⟩
    intro j hj
    fin_cases j
    · exact hz
    · exact h1
    · exact (hj rfl).elim
  · apply haxis
    refine ⟨1,?_⟩
    intro j hj
    fin_cases j
    · exact hz
    · exact (hj rfl).elim
    · exact h2
  · obtain ⟨p,hp⟩ := icosianEdgeRootBase_reconstruct r hz hn.1 hn.2
    exact ⟨Sum.inr p,Subtype.ext hp⟩

def icosianZeroRootEquiv : (IcosianZeroAxisParameters ⊕ IcosianEdgePair) ≃ IcosianZeroRoot :=
  Equiv.ofBijective icosianZeroRootEncode
    ⟨icosianZeroRootEncode_injective,icosianZeroRootEncode_surjective⟩

theorem icosianZeroRoots_card : Nat.card IcosianZeroRoot=1200 := by
  rw [← Nat.card_congr icosianZeroRootEquiv,Nat.card_sum]
  change Nat.card ({i : Fin 3 // i≠0} × icosianNormOneGroup)+_=1200
  rw [Nat.card_prod,icosianNormOneGroup_card,icosianEdgePairs_card]
  have h : Nat.card {i : Fin 3 // i≠0}=2 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  rw [h]

end Atlas.Lattices
