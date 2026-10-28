module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourRee
public import Theory.SpecificGroups.Triality.LocalHeisenbergExclusion
public import Theory.SpecificGroups.Triality.StandardTwoRank.RankTable

/-!
# Excluding triality in the original extraspecial centralizer

The actual U embeds in B/O₂(B), so that quotient has two-rank at least
seven. The genuine triality rank table excludes the field-order-two
endpoint. For every larger field, the literal quotient action contains
the faithful Heisenberg subgroup inside a solvable subgroup of odd index,
contradicting the intrinsic triality Borel obstruction. The model's
simplicity and perfectness are transported from the original component.

The final source application retains B, L₁, the original marked inner
involution and its movement. Only large binary PSL₃, large binary PSU₃
and Tits quotients remain. Those last alternatives, centralizer containment
and TI remain to be proved; no recognition callback is introduced.

Source: Aschbacher–Smith, 14.7.26, printed p.1053, refs/quasithin.pdf;
GLS3 root geometry for the imported triality calculations.
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

private theorem transport_rankTwo_exclusion
    {Q W : Type*} [Group Q] [Finite Q] [Group W] [Finite W] (e : Q ≃* W)
    (exclude : ∀ (A : Subgroup (MulAut W)), MulAut.innerSubgroup W ≤ A →
      primeRank 3 A ≤ 2 → ∀ J : Subgroup A, Group.IsSolvable J → Odd J.index →
      ∀ f : HeisenbergPrime 3 →* A, Function.Injective f → (∀ y, f y ∈ J) → False)
    (A : Subgroup (MulAut Q)) (hA : MulAut.innerSubgroup Q ≤ A)
    (hr : primeRank 3 A ≤ 2) (J : Subgroup A) (hs : Group.IsSolvable J) (ho : Odd J.index)
    (f : HeisenbergPrime 3 →* A) (hf : Function.Injective f) (hJ : ∀ y, f y ∈ J) : False := by
  let ea := MulAut.congr e
  let A' := A.map ea.toMonoidHom
  let eA : A ≃* A' := ea.subgroupMap A
  let J' := J.map eA.toMonoidHom
  have hA' : MulAut.innerSubgroup W ≤ A' := by
    rw [←MulAut.map_innerSubgroup_congr e]
    exact map_mono hA
  have hr' : primeRank 3 A' ≤ 2 := (primeRank_equiv 3 eA).symm ▸ hr
  let := hs
  have hs' : Group.IsSolvable J' := Group.isSolvable_of_surjective
    (eA.toMonoidHom.subgroupMap_surjective J)
  have ho' : Odd J'.index := (index_map_of_bijective (f := eA.toMonoidHom) eA.bijective J).symm ▸ ho
  exact exclude A' hA' hr' J' hs' ho' (eA.toMonoidHom.comp f) (eA.injective.comp hf)
    (fun y => mem_map_of_mem _ (hJ y))


/-- The actual ordinary component has no triality quotient. Its original span
excludes the binary endpoint; the literal Heisenberg action excludes larger fields. -/
theorem extraspecial_four_ordinary_not_triality
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
    {n : ℕ} (hn : 1 ≤ n)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2^n) (B ⧸ pCore 2 B)) : False := by
  have hr2 := extraspecial_four_ordinary_twoRank
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  have heq := Triality.Standard.TwoRank.twoRank_eq_five_mul_of_model n (by omega) hmodel
  have hn2 : 1 < n := by omega
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n (by omega)).mp hmodel
  let : IsQuasisimple B := hB.2
  let : IsSimpleGroup (B ⧸ pCore 2 B) := (extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB).2.2.2.2.1
  let : IsSimpleGroup (Triality.Standard.BinaryCarrier n (by omega)) := e.symm.isSimpleGroup
  let : Group.IsPerfect (Triality.Standard.BinaryCarrier n (by omega)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨hnB,ha⟩ := extraspecial_four_ordinary_action
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  let := hnB
  obtain ⟨_,hi,hr,hs,ho,_,f,hf,hfJ⟩ := ha
  exact transport_rankTwo_exclusion e (fun A hA hr J hs ho f hf hJ => by
    let := hs
    exact Triality.Standard.LocalHeisenbergExclusion.no_action n hn2 A hA hr J ho f hf hJ)
    _ hi hr _ hs ho f hf hfJ

/-- The original source application now leaves only large linear, large unitary
and Tits quotients; all triality and Ree alternatives have been excluded. -/
theorem extraspecial_four_ordinary_three_family_source
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
        Nonempty ((B ⧸ pCore 2 B) ≃* Tits.ParrottGroup)) := by
  obtain ⟨B,z,hB,hn,hLB,hz,hzp,hm,houtB,α,ha,hi,hmodel,hcases⟩ :=
    extraspecial_four_ordinary_remaining_source
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
  refine ⟨B,z,hB,hn,hLB,hz,hzp,hm,houtB,α,ha,hi,hmodel,?_⟩
  rcases hcases with hl | hu | ⟨n,hn,ht⟩ | hT
  · exact Or.inl hl
  · exact Or.inr (Or.inl hu)
  · exact (extraspecial_four_ordinary_not_triality
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB hn ht).elim
  · exact Or.inr (Or.inr hT)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
