module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourModelExclusions
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.SolvableSylowThreeFree

/-!
# Excluding the Ree ordinary component of the extraspecial centralizer

The actual intersection H ∩ B is solvable and contains the restriction of
the original centralizer Sylow subgroup. The normal component contains L₁,
whose cubic two-core quotient makes this intersection's order divisible
by three. The genuine Ree Borel theorem says a solvable full-Sylow overgroup
has order prime to three, also through the literal central two-kernel.
Thus B/O₂(B) cannot be a Ree F₄ model.

The final application retains the original normal component and marked
inner involution, and removes the Ree alternative from the preceding full
1.1.5 reduction. Large linear, large unitary, triality and Tits quotients
remain; this does not assert centralizer containment or TI.

Source: Aschbacher–Smith, 14.7.26, printed p.1053, refs/quasithin.pdf.
The imported Ree calculation retains the root-defined Borel and its source
reference to F.1.12. No Data or final recognition premise is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Representation Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08 Chapter1.Section02.LocalModels
open Chapter15.Section03.Candidates.ComponentStructure
open scoped IsMulCommutative Pointwise commutatorElement MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem H_solvable
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    Group.IsSolvable F.H := by
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  have hdiv := odd_prime_dvd_twoCore_quotient_residual hp (hp.odd_of_ne_two hp2) hd
  obtain ⟨e⟩ := he
  rw [Nat.card_congr ((residualStarEquiv F).symm.trans e).toEquiv,
    HeisenbergPrime.card] at hdiv
  exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp
    (hp.dvd_of_dvd_pow hdiv)).resolve_left hp.ne_one)

/-- The literal intersection of the original H with B is solvable, contains a
full Sylow two-subgroup of B, and has order divisible by three. -/
theorem extraspecial_four_ordinary_intersection
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    : let J := F.H.comap ((centralizer ({x} : Set G)).subtype.comp B.subtype)
      Group.IsSolvable J ∧ (∃ P : Sylow 2 B, (P : Subgroup B) ≤ J) ∧
        3 ∣ Nat.card J := by
  let C := centralizer ({x} : Set G)
  let J := F.H.comap (C.subtype.comp B.subtype)
  let : Group.IsSolvable F.H := H_solvable he
  let j : J →* F.H := (C.subtype.comp (B.subtype.comp J.subtype)).codRestrict F.H
    (fun a => a.property)
  have hj : Function.Injective j := by
    intro a b hh
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : F.H => (a : G)) hh
  have hsol : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective hj
  obtain ⟨hn,hLB,_,_,_,_⟩ := extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  let := hn
  obtain ⟨_,_,_,_,_,P,hP,_⟩ := extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_normal B
  have hQJ : (Q : Subgroup B) ≤ J := by
    intro a ha
    rw [hQ] at ha
    have hh : ((a : C) : G) ∈ (T : Subgroup G) ⊓ C :=
      hP ▸ mem_map_of_mem C.subtype ha
    exact F.invariant 1 hh.1
  let eB := B.equivMapOfInjective C.subtype C.subtype_injective
  let k : F.Li L 1 →* B := eB.symm.toMonoidHom.comp (inclusion hLB)
  have hval (a : F.Li L 1) : ((k a : C) : G) = a :=
    congrArg Subtype.val (eB.apply_symm_apply ⟨a,hLB a.property⟩)
  let kJ : F.Li L 1 →* J := k.codRestrict J (fun a => by
    change ((k a : C) : G) ∈ F.H
    rw [hval]
    exact (F.Li_le L 1 a.property).2)
  have hkJ : Function.Injective kJ := by
    intro a b hh
    apply Subtype.ext
    exact (hval a).symm.trans ((congrArg (fun y : J => ((y.val : C) : G)) hh).trans (hval b))
  have h3 : 3 ∣ Nat.card (F.Li L 1) := by
    have hd := (pCore 2 (F.Li L 1)).card_quotient_dvd_card
    rw [pointResidual_core_quotient_card h structural] at hd
    exact hd
  exact ⟨hsol,⟨Q,hQJ⟩,h3.trans (card_dvd_of_injective kJ hkJ)⟩

/-- A Ree quotient is impossible for the actual ordinary component: the original
solvable full-Sylow intersection has a factor of three, whereas Ree Borels do not. -/
theorem extraspecial_four_ordinary_not_ree
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    {m : ℕ} (hm : 1 ≤ m) (hmodel : IsReeF4At (B ⧸ pCore 2 B) m) : False := by
  obtain ⟨r,⟨e⟩⟩ := hmodel
  let eR := e.trans r.modelEquiv
  let f := eR.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
  have hf : Function.Surjective f := eR.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ eR.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨hsol,⟨P,hPJ⟩,h3⟩ := extraspecial_four_ordinary_intersection
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  have hc := ReeF4.Parabolics.coprime_three_of_solvable_sylow_overgroup_of_two_kernel
    hm f hf hk P _ hsol hPJ
  exact Nat.prime_three.coprime_iff_not_dvd.mp hc h3

/-- The original escaping centralizer now leaves only large linear, large
unitary, triality and Tits quotients; the genuine Ree branch is discharged. -/
theorem extraspecial_four_ordinary_remaining_source
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    : ∃ (B : Subgroup (centralizer ({x} : Set G))) (z : G),
      IsComponent (centralizer ({x} : Set G)) B ∧ B.Normal ∧
      F.Li L 1 ≤ B.map (centralizer ({x} : Set G)).subtype ∧
      orderOf z = 2 ∧ zpowers z = F.Vi 1 ∧
      B.map (centralizer ({x} : Set G)).subtype =
        ⁅B.map (centralizer ({x} : Set G)).subtype,zpowers z⁆ ∧
      ¬ B.map (centralizer ({x} : Set G)).subtype ≤ F.H ∧
      ∃ α : MulAut B, (∀ y : B, ((α y : centralizer ({x} : Set G)) : G) = z * (y : G) * z⁻¹) ∧
        α ∈ (MulAut.conj (G := B)).range ∧
        ModelAction115 B α ∧
        ((∃ n, 4 ≤ n ∧ Even n ∧ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 (2^n)) ∨
        (∃ n, 7 ≤ n ∧ Odd n ∧ ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 (2^n)) ∨
        (∃ n, 1 ≤ n ∧ Triality.Standard.IsTrialityGroupAt (2^n) (B ⧸ pCore 2 B)) ∨
        Nonempty ((B ⧸ pCore 2 B) ≃* Tits.ParrottGroup)) := by
  obtain ⟨B,z,hB,hn,hLB,hz,hzp,hm,houtB,α,ha,hi,hmodel,hcases⟩ :=
    extraspecial_four_ordinary_reduced_source
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
  refine ⟨B,z,hB,hn,hLB,hz,hzp,hm,houtB,α,ha,hi,hmodel,?_⟩
  rcases hcases with hl | hu | ht | ⟨m,hm,hr⟩ | hT
  · exact Or.inl hl
  · exact Or.inr (Or.inl hu)
  · exact Or.inr (Or.inr (Or.inl ht))
  · exact (extraspecial_four_ordinary_not_ree
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB hm hr).elim
  · exact Or.inr (Or.inr (Or.inr hT))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
