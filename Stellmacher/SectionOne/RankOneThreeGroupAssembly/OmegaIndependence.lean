module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaGeneration
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaActions

/-!
# Independence of omega factors and their action modules

A factor acts faithfully on its own four-point module while different factors fix it; this proves disjointness from the entire join of other factors, allowing correct multiple-factor cardinal counts.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- Coordinate uniqueness for the complete `oneOmega` decomposition.  If a
family of ambient `oneOmega` subgroups generates the odd core, then every
ambient `oneOmega` subgroup is already a member of that family.  The proof
uses action modules rather than the formally weaker pairwise-disjoint group
field: every other coordinate fixes `[V,F]`, while coprime idempotence says
that `F` cannot fix its own nontrivial action module. -/
public theorem oneOmega_eq_member_of_iSup_eq_oddCore
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    {I : Sort*} (K : I → Subgroup G)
    (hKomega : ∀ i, oneOmega (G := G) (V := V) (K i))
    (hgen : oddCore G = ⨆ i, K i)
    (F : Subgroup G) (hFomega : oneOmega (G := G) (V := V) F) :
    ∃ i, F = K i := by
  classical
  by_contra hnone
  push Not at hnone
  let U : Subgroup V := commutatorAction F V
  have hFmem : F ∈ oneOmegaFinset (G := G) (V := V) :=
    (mem_oneOmegaFinset_iff (G := G) (V := V) F).mpr hFomega
  have hKmem (i : I) : K i ∈ oneOmegaFinset (G := G) (V := V) :=
    (mem_oneOmegaFinset_iff (G := G) (V := V) (K i)).mpr (hKomega i)
  have hKfix (i : I) : K i ≤ fixingSubgroup G (U : Set V) := by
    exact distinct_oneOmega_factor_acts_trivially F (K i) hFmem (hKmem i)
      (hnone i) hdecomp
  have hWfix : oddCore G ≤ fixingSubgroup G (U : Set V) := by
    rw [hgen]
    exact iSup_le hKfix
  have hFfix : F ≤ fixingSubgroup G (U : Set V) := hFomega.1.trans hWfix
  let hUinv : IsInvariant F V U := commutatorAction_isInvariant
  let _ : IsInvariant F V U := hUinv
  have htriv : ActsTrivially (A := F) (G := U) := by
    intro f u
    apply Subtype.ext
    exact ((mem_fixingSubgroup_iff (M := G)
      (s := (U : Set V))).mp (hFfix f.property)) (u : V) u.property
  have hrestrictedBot : commutatorAction F U = ⊥ :=
    commutatorAction_eq_bot_of_actsTrivially htriv
  have hcop : Nat.Coprime (Nat.card F) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hFomega.2.1, hn]
    change Nat.Coprime (3 ^ 1) (2 ^ n)
    exact Nat.Coprime.pow 1 n (by decide)
  have hUeq : (commutatorAction F U).map U.subtype = U := by
    exact commutatorAction_restrict_eq_of_le_of_coprime U le_rfl hcop
  have hUbot : U = ⊥ := by
    rw [hrestrictedBot, Subgroup.map_bot] at hUeq
    exact hUeq.symm
  have hUcard : Nat.card U = 4 := hFomega.2.2
  rw [hUbot] at hUcard
  norm_num at hUcard

/-- An omega factor acts faithfully on its own order-four commutator module.
Equivalently, it meets the ambient pointwise stabilizer of that module
trivially.  This is the coordinate-independence input for support counting. -/
private theorem oneOmega_disjoint_fixingSubgroup_own_commutator
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (F : Subgroup G) (hF : oneOmega (G := G) (V := V) F) :
    Disjoint F (fixingSubgroup G (commutatorAction F V : Set V)) := by
  let U : Subgroup V := commutatorAction F V
  let K : Subgroup F :=
    (fixingSubgroup G (U : Set V)).comap F.subtype
  let hprime : Fact (Nat.card F).Prime := ⟨hF.2.1 ▸ Nat.prime_three⟩
  let _ : Fact (Nat.card F).Prime := hprime
  have hKbot : K = ⊥ := by
    rcases K.eq_bot_or_eq_top_of_prime_card with hbot | htop
    · exact hbot
    · exfalso
      have hFfix : F ≤ fixingSubgroup G (U : Set V) := by
        intro f hf
        have hfK : (⟨f, hf⟩ : F) ∈ K := by
          rw [htop]
          trivial
        exact hfK
      let hUinv : IsInvariant F V U := commutatorAction_isInvariant
      let _ : IsInvariant F V U := hUinv
      have htriv : ActsTrivially (A := F) (G := U) := by
        intro f x
        apply Subtype.ext
        exact ((mem_fixingSubgroup_iff (M := G)
          (s := (U : Set V))).mp (hFfix f.property)) (x : V) x.property
      have hrestrictedBot : commutatorAction F U = ⊥ :=
        commutatorAction_eq_bot_of_actsTrivially htriv
      have hcop : Nat.Coprime (Nat.card F) (Nat.card V) := by
        obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
        rw [hF.2.1, hn]
        change Nat.Coprime (3 ^ 1) (2 ^ n)
        exact Nat.Coprime.pow 1 n (by decide)
      have hUeq : (commutatorAction F U).map U.subtype = U :=
        commutatorAction_restrict_eq_of_le_of_coprime U le_rfl hcop
      have hUbot : U = ⊥ := by
        rw [hrestrictedBot, Subgroup.map_bot] at hUeq
        exact hUeq.symm
      have hUcard : Nat.card U = 4 := hF.2.2
      rw [hUbot] at hUcard
      norm_num at hUcard
  rw [Subgroup.disjoint_def]
  intro x hxF hxfix
  have hxK : (⟨x, hxF⟩ : F) ∈ K := hxfix
  rw [hKbot] at hxK
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hxK)

/-- A complete omega coordinate is disjoint from the join of any family of
different complete omega coordinates. -/
public theorem oneOmega_disjoint_iSup_of_distinct
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    (F : Subgroup G) (hF : oneOmega (G := G) (V := V) F)
    {I : Sort*} (K : I → Subgroup G)
    (hK : ∀ i, oneOmega (G := G) (V := V) (K i))
    (hne : ∀ i, K i ≠ F) :
    Disjoint F (⨆ i, K i) := by
  have hFmem : F ∈ oneOmegaFinset (G := G) (V := V) :=
    (mem_oneOmegaFinset_iff (G := G) (V := V) F).mpr hF
  have hjoinFix : (⨆ i, K i) ≤
      fixingSubgroup G (commutatorAction F V : Set V) := by
    refine iSup_le ?_
    intro i
    exact distinct_oneOmega_factor_acts_trivially F (K i) hFmem
      ((mem_oneOmegaFinset_iff (G := G) (V := V) (K i)).mpr (hK i))
      (Ne.symm (hne i)) hdecomp
  exact (oneOmega_disjoint_fixingSubgroup_own_commutator F hF).mono
    le_rfl hjoinFix

/-- The order-four action module of one complete omega factor is disjoint
from the join of the action modules of any family of distinct factors. -/
public theorem oneOmega_action_disjoint_iSup_of_distinct
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    (F : Subgroup G) (hF : oneOmega (G := G) (V := V) F)
    {I : Sort*} (K : I → Subgroup G)
    (hK : ∀ i, oneOmega (G := G) (V := V) (K i))
    (hne : ∀ i, K i ≠ F) :
    Disjoint (commutatorAction F V)
      (⨆ i, commutatorAction (K i) V) := by
  let U : Subgroup V := commutatorAction F V
  have hjoinFix : (⨆ i, commutatorAction (K i) V) ≤
      FixedPoints.subgroup F V := by
    refine iSup_le ?_
    intro i u hu
    rw [FixedPoints.mem_subgroup]
    intro f
    have hfix := distinct_oneOmega_factor_acts_trivially
      (K i) F
      ((mem_oneOmegaFinset_iff (G := G) (V := V) (K i)).mpr (hK i))
      ((mem_oneOmegaFinset_iff (G := G) (V := V) F).mpr hF)
      (hne i) hdecomp
    exact ((mem_fixingSubgroup_iff (M := G)
      (s := (commutatorAction (K i) V : Set V))).mp
        (hfix f.property)) u hu
  have hcop : Nat.Coprime (Nat.card F) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hF.2.1, hn]
    change Nat.Coprime (3 ^ 1) (2 ^ n)
    exact Nat.Coprime.pow 1 n (by decide)
  have hcompl : IsCompl (FixedPoints.subgroup F V) U :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := F)
      (Group.isSolvable_of_comm fun x y =>
        (IsMulCommutative.is_comm (M := V)).comm x y)
      hcop inferInstance
  exact hcompl.disjoint.symm.mono le_rfl hjoinFix

/-- The cardinality of a commuting product of disjoint finite subgroups is
the product of their cardinalities.  The normality needed for the usual
complement count is established only inside the generated subgroup. -/
public theorem natCard_sup_eq_mul_of_disjoint_of_le_centralizer
    {G : Type u} [Group G] [Finite G]
    (H K : Subgroup G) (hdisj : Disjoint H K)
    (hcomm : K ≤ Subgroup.centralizer (H : Set G)) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  let L : Subgroup G := H ⊔ K
  let HS : Subgroup L := H.subgroupOf L
  let KS : Subgroup L := K.subgroupOf L
  have hHnormalizer : L ≤ Subgroup.normalizer H := by
    exact sup_le Subgroup.le_normalizer
      (hcomm.trans (Subgroup.centralizer_le_normalizer (H : Set G)))
  let hHSnormal : HS.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      hHnormalizer
  let _ : HS.Normal := hHSnormal
  have hHSKSdisj : Disjoint HS KS := by
    rw [Subgroup.disjoint_def]
    intro x hxH hxK
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hdisj hxH hxK
  have hHSKS_top : HS ⊔ KS = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    ext x
    simp
  have hmul : (HS : Set L) * (KS : Set L) = Set.univ := by
    rw [← Subgroup.normal_mul HS KS, hHSKS_top]
    rfl
  have hcomp : HS.IsComplement' KS :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hHSKSdisj hmul
  have hcard := hcomp.card_mul_card
  rw [natCard_subgroupOf_eq H L le_sup_left,
    natCard_subgroupOf_eq K L le_sup_right] at hcard
  exact hcard.symm

/-- Fixed points split multiplicatively across two invariant, disjoint
subgroups of a finite commutative group.  The target is their join, so no
ambient generation hypothesis is needed. -/
public theorem natCard_inf_fixedPoints_sup_eq_mul
    {A V : Type u} [Group A] [Group V] [Finite V]
    [IsMulCommutative V] [MulDistribMulAction A V]
    (C U : Subgroup V) [IsInvariant A V C] [IsInvariant A V U]
    (hdisj : Disjoint C U) :
    Nat.card (↥((C ⊔ U) ⊓ FixedPoints.subgroup A V)) =
      Nat.card (↥(C ⊓ FixedPoints.subgroup A V)) *
        Nat.card (↥(U ⊓ FixedPoints.subgroup A V)) := by
  let L : Subgroup V := C ⊔ U
  let CL : Subgroup L := C.subgroupOf L
  let UL : Subgroup L := U.subgroupOf L
  let hLinv : IsInvariant A V L := isInvariant_sup C U
  let _ : IsInvariant A V L := hLinv
  let hCLinv : IsInvariant A L CL := isInvariant_subgroupOf C L
  let hULinv : IsInvariant A L UL := isInvariant_subgroupOf U L
  let _ : IsInvariant A L CL := hCLinv
  let _ : IsInvariant A L UL := hULinv
  have hCnormalizer : L ≤ Subgroup.normalizer C := by
    apply sup_le Subgroup.le_normalizer
    exact (Subgroup.le_centralizer_iff.mpr fun u hu c hc =>
      (IsMulCommutative.is_comm (M := V)).comm c u).trans
        (Subgroup.centralizer_le_normalizer (C : Set V))
  let hCLnormal : CL.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      hCnormalizer
  let _ : CL.Normal := hCLnormal
  have hdisjSub : Disjoint CL UL := by
    rw [Subgroup.disjoint_def]
    intro x hxC hxU
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hdisj hxC hxU
  have hsupTop : CL ⊔ UL = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    ext x
    simp
  have hmul : (CL : Set L) * (UL : Set L) = Set.univ := by
    rw [← Subgroup.normal_mul CL UL, hsupTop]
    rfl
  let hcomp : CL.IsComplement' UL :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjSub hmul
  let FC : Subgroup V := C ⊓ FixedPoints.subgroup A V
  let FU : Subgroup V := U ⊓ FixedPoints.subgroup A V
  let FL : Subgroup V := L ⊓ FixedPoints.subgroup A V
  let f : FC × FU → FL := fun z =>
    ⟨(z.1 : V) * (z.2 : V),
      ⟨L.mul_mem ((show C ≤ L from le_sup_left) z.1.property.1)
          ((show U ≤ L from le_sup_right) z.2.property.1),
        (FixedPoints.mem_subgroup (M := A)
          (a := (z.1 : V) * (z.2 : V))).mpr (fun a => by
            rw [smul_mul']
            have hc := (FixedPoints.mem_subgroup (M := A)
              (a := (z.1 : V))).mp z.1.property.2 a
            have hu := (FixedPoints.mem_subgroup (M := A)
              (a := (z.2 : V))).mp z.2.property.2 a
            rw [hc, hu])⟩⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    let xc : CL := ⟨⟨(x.1 : V),
      (show C ≤ L from le_sup_left) x.1.property.1⟩,
      x.1.property.1⟩
    let xu : UL := ⟨⟨(x.2 : V),
      (show U ≤ L from le_sup_right) x.2.property.1⟩,
      x.2.property.1⟩
    let yc : CL := ⟨⟨(y.1 : V),
      (show C ≤ L from le_sup_left) y.1.property.1⟩,
      y.1.property.1⟩
    let yu : UL := ⟨⟨(y.2 : V),
      (show U ≤ L from le_sup_right) y.2.property.1⟩,
      y.2.property.1⟩
    have hpair : (xc, xu) = (yc, yu) := by
      apply hcomp.1
      apply Subtype.ext
      exact congrArg (fun z : FL => (z : V)) hxy
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z : CL × UL => (((z.1 : CL) : L) : V)) hpair
    · apply Subtype.ext
      exact congrArg (fun z : CL × UL => (((z.2 : UL) : L) : V)) hpair
  have hfsurj : Function.Surjective f := by
    intro v
    let vL : L := ⟨(v : V), v.property.1⟩
    obtain ⟨z, hz⟩ := hcomp.2 vL
    let c : CL := z.1
    let u : UL := z.2
    have hfixed (a : A) : (a • c, a • u) = (c, u) := by
      apply hcomp.1
      apply Subtype.ext
      have hv := (FixedPoints.mem_subgroup (M := A) (a := (v : V))).mp
        v.property.2 a
      change a • ((c : L) : V) * a • ((u : L) : V) =
        ((c : L) : V) * ((u : L) : V)
      rw [← smul_mul']
      have hcu : ((c : L) : V) * ((u : L) : V) = (v : V) := by
        have hzL : (c : L) * (u : L) = vL := by
          simpa only [c, u] using hz
        exact congrArg (fun y : L => (y : V)) hzL
      rw [hcu, hv]
    let cf : FC := ⟨((c : L) : V), ⟨c.property, by
      apply (FixedPoints.mem_subgroup (M := A)
        (a := ((c : L) : V))).mpr
      intro a
      exact congrArg (fun z : CL × UL => (((z.1 : CL) : L) : V))
        (hfixed a)⟩⟩
    let uf : FU := ⟨((u : L) : V), ⟨u.property, by
      apply (FixedPoints.mem_subgroup (M := A)
        (a := ((u : L) : V))).mpr
      intro a
      exact congrArg (fun z : CL × UL => (((z.2 : UL) : L) : V))
        (hfixed a)⟩⟩
    refine ⟨(cf, uf), ?_⟩
    apply Subtype.ext
    exact congrArg (fun y : L => (y : V)) hz
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)).symm.trans
    (Nat.card_prod _ _)

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
