/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianRootCDFamilies.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianRootCDCounts
public import Theory.AtlasPort.Janko2.Lattices.IcosianRootPermutations
public import Theory.AtlasPort.Janko2.GroupTheory.TriplePermutation

/-!
# Icosian Root CDFamilies

Permutations extend the two fixed-position families to all roots of
these norm shapes. Their norm words prove injectivity and recognition,
giving family cardinalities 23040 and 11520.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianRootCDFamilies.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra
open scoped Matrix QuadraticAlgebra

def icosianRootNormWord (r : IcosianRoot) : Fin 3 → GoldenInteger :=
  fun i => icosianIntegralNorm (r.val i)

theorem icosianRootNormWord_of_norm (r : IcosianRoot) (i : Fin 3) (a : GoldenInteger)
    (h : icosianNorm (r.val i).val=goldenIntegerToRational a) : icosianRootNormWord r i=a := by
  apply goldenIntegerToRational_injective
  exact (icosianIntegralNorm_spec _).trans h

theorem icosianRootCStandard_word (r : IcosianRootCStandard) (i : Fin 3) :
    icosianRootNormWord r.val i=icosianRootCNorms i :=
  icosianRootNormWord_of_norm r.val i _ (r.property i)

theorem icosianRootDStandard_word (r : IcosianRootDStandard) (i : Fin 3) :
    icosianRootNormWord r.val i=icosianRootDNorms i :=
  icosianRootNormWord_of_norm r.val i _ (r.property i)

@[simp] theorem icosianRootNormWord_permute (p : Equiv.Perm (Fin 3)) (r : IcosianRoot) (i : Fin 3) :
    icosianRootNormWord (icosianRootPermute p r) i=icosianRootNormWord r (p.symm i) := rfl

def icosianRootCParameter (p : Fin 3 × IcosianRootCStandard) : IcosianRoot :=
  icosianRootPermute (Equiv.swap 2 p.1) p.2.val

theorem icosianRootCParameter_word (p : Fin 3 × IcosianRootCStandard) (j : Fin 3) :
    icosianRootNormWord (icosianRootCParameter p) j=if j=p.1 then 2 else 1 := by
  change icosianRootNormWord p.2.val ((Equiv.swap 2 p.1).symm j)=_
  rw [icosianRootCStandard_word]
  rcases p with ⟨i,r⟩
  fin_cases i <;> fin_cases j <;> simp [icosianRootCNorms,Equiv.swap_apply_def]

theorem icosianRootCParameter_injective : Function.Injective icosianRootCParameter := by
  rintro ⟨i,r⟩ ⟨j,s⟩ h
  have hij : i=j := by
    by_contra hn
    have he := congrArg (fun z => icosianRootNormWord z i) h
    simp [icosianRootCParameter_word,hn] at he
  subst j
  have he : r.val=s.val := (icosianRootPermute (Equiv.swap 2 i)).injective h
  exact congrArg (fun z => (i,z)) (Subtype.ext he)

abbrev IcosianRootCFamily := {r : IcosianRoot // r∈Set.range icosianRootCParameter}

def icosianRootCFamilyEquiv : (Fin 3 × IcosianRootCStandard) ≃ IcosianRootCFamily :=
  Equiv.ofInjective icosianRootCParameter icosianRootCParameter_injective

theorem icosianRootCFamily_card : Nat.card IcosianRootCFamily=23040 := by
  rw [← Nat.card_congr icosianRootCFamilyEquiv,Nat.card_prod,icosianRootCStandard_card]
  norm_num

theorem icosianRootC_recognition (r : IcosianRoot) (i : Fin 3)
    (h : ∀ j,icosianRootNormWord r j=if j=i then 2 else 1) :
    r∈Set.range icosianRootCParameter := by
  let rr := icosianRootPermute (Equiv.swap 2 i) r
  have hn (j : Fin 3) : icosianRootNormWord rr j=icosianRootCNorms j := by
    change icosianRootNormWord r ((Equiv.swap 2 i).symm j)=_
    rw [h]
    fin_cases i <;> fin_cases j <;> simp [icosianRootCNorms,Equiv.swap_apply_def]
  let s : IcosianRootCStandard := ⟨rr,fun j =>
    (icosianIntegralNorm_spec _).symm.trans (congrArg goldenIntegerToRational (hn j))⟩
  refine ⟨(i,s),?_⟩
  apply Subtype.ext
  funext j
  simp [icosianRootCParameter,s,rr,icosianRootPermute,icosianPermute]

def icosianRootDParameter (p : Equiv.Perm (Fin 3) × IcosianRootDStandard) : IcosianRoot :=
  icosianRootPermute p.1 p.2.val

theorem icosianRootDNorms_injective : Function.Injective icosianRootDNorms := by
  decide +kernel

theorem icosianRootDParameter_word (p : Equiv.Perm (Fin 3) × IcosianRootDStandard) (i : Fin 3) :
    icosianRootNormWord (icosianRootDParameter p) i=icosianRootDNorms (p.1.symm i) :=
  icosianRootDStandard_word p.2 _

theorem icosianRootDParameter_injective : Function.Injective icosianRootDParameter := by
  rintro ⟨p,r⟩ ⟨q,s⟩ h
  have hpq : p=q := by
    have hi : p.symm=q.symm := by
      apply Equiv.ext
      intro i
      apply icosianRootDNorms_injective
      have he := congrArg (fun z => icosianRootNormWord z i) h
      simpa only [icosianRootDParameter_word] using he
    exact congrArg Equiv.symm hi
  subst q
  have he : r.val=s.val := (icosianRootPermute p).injective h
  exact congrArg (fun z => (p,z)) (Subtype.ext he)

abbrev IcosianRootDFamily := {r : IcosianRoot // r∈Set.range icosianRootDParameter}

def icosianRootDFamilyEquiv : (Equiv.Perm (Fin 3) × IcosianRootDStandard) ≃ IcosianRootDFamily :=
  Equiv.ofInjective icosianRootDParameter icosianRootDParameter_injective

theorem icosianRootDFamily_card : Nat.card IcosianRootDFamily=11520 := by
  rw [← Nat.card_congr icosianRootDFamilyEquiv,Nat.card_prod,icosianRootDStandard_card]
  have h : Nat.card (Equiv.Perm (Fin 3))=6 := by
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  rw [h]

theorem icosianRootD_recognition (r : IcosianRoot) (p : Equiv.Perm (Fin 3))
    (h : ∀ j,icosianRootNormWord r j=icosianRootDNorms (p.symm j)) :
    r∈Set.range icosianRootDParameter := by
  let rr := icosianRootPermute p.symm r
  have hn (j : Fin 3) : icosianRootNormWord rr j=icosianRootDNorms j := by
    change icosianRootNormWord r (p j)=_
    rw [h,p.symm_apply_apply]
  let s : IcosianRootDStandard := ⟨rr,fun j =>
    (icosianIntegralNorm_spec _).symm.trans (congrArg goldenIntegerToRational (hn j))⟩
  refine ⟨(p,s),?_⟩
  apply Subtype.ext
  funext j
  simp [icosianRootDParameter,s,rr,icosianRootPermute,icosianPermute]

end Atlas.Lattices
