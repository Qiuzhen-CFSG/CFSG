module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.RankOne
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Relative embeddings in the two odd-extension carriers

A perfect binary PSL₂ section retains its simple two-core quotient under
solvable homomorphism kernels. Projecting either odd extension to its
SL₂ quotient and then to PSL₂ therefore preserves this smaller section.
A perfect subgroup of odd PSL₂ has trivial two-core, and the containing
group has dihedral Sylow two-subgroups. Its two-rank bound forces the
original nonbinary degree to be two.

Both original flag normalizers and arbitrary nontrivial U ≤ V₁ receive
actual 11.1.1 alternatives. The proofs retain O₂(Lᵢ), normal extension
kernels and the SL₂ covers, with no splitting assumption. The literal
smaller quotient markings belong to qt-d-1222-natural-flag-cartan and
are discharged by qt-d-1222-natural-local-geometry. The relative-components
owner retains the exhaustive catalogue and source-family assembly;
Refinement.RankOneAndExtensions applies these parameter restrictions.

Source: Aschbacher--Smith A.3.12--14 and 11.1.1, printed pp.47--49,761,
combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding

private theorem odd_rank_one_solvable_kernel_parameter
    {B F : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    [Field F] [Finite F] (ho : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (φ : B →* PSL(2,F)) [Group.IsSolvable φ.ker]
    {n : ℕ} (hn : 1 < n) (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) : n = 2 := by
  let : IsSimpleGroup (B ⧸ pCore 2 B) := by
    obtain ⟨E,_,_,hE,⟨e⟩⟩ := hm
    let : IsSimpleGroup PSL(2,E) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [hE]
      exact (show (4 : ℕ) = 2^2 from rfl).le.trans (Nat.pow_le_pow_right (by decide) hn))
    exact e.isSimpleGroup
  let C := φ.range
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  let : Group.IsSolvable φ.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  let a := PerfectCoreTwoExtension.solvableKernelQuotientEquiv φ.rangeRestrict φ.rangeRestrict_surjective
  have hodd : Odd (Nat.card F) := by
    obtain ⟨r,k,_,hr,_,he⟩ := ho
    rw [he]
    exact hr.pow
  have hz := Theory.PSL2.odd_perfect_subgroup_twoCore_eq_bot hodd C
  let b : (C ⧸ pCore 2 C) ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  have hlo : n ≤ primeRank 2 C := binary_rank_lower (hm.of_mulEquiv (a.trans b).symm)
  have hu : primeRank 2 PSL(2,F) ≤ 2 := by
    let P : Sylow 2 PSL(2,F) := Classical.choice inferInstance
    obtain ⟨k,_,⟨e⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F ho P
    rw [P.primeRank_eq,primeRank_equiv 2 e]
    exact dihedral_rank_le_two k
  have hb := hlo.trans ((primeRank_subgroup_le 2 C).trans hu)
  omega

private theorem extension_section_parameter
    {A : Type*} [Group A] [Finite A] (B : Subgroup A) [Group.IsPerfect B]
    {n r : ℕ} (hn : 1 < n) (hr : r.Prime) (ho : Odd r)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hext : Chapter1.Section02.LocalModels.HasExtension A
      (fun N _ => Group.IsSolvable N) (fun Q _ => Source.IsSL Q 2 r)) : n = 2 := by
  obtain ⟨N,hN,hsol,F,_,_,hF,⟨e⟩⟩ := hext
  let := hN
  let := hsol
  let q := QuotientGroup.mk' N
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  let k := e.toMonoidHom.comp q
  let : Group.IsSolvable k.ker := by
    change Group.IsSolvable (e.toMonoidHom.comp q).ker
    rw [MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective]
    infer_instance
  let π : A →* PSL(2,F) := (QuotientGroup.mk' (center SL(2,F))).comp k
  let : Group.IsSolvable π.ker := by
    change Group.IsSolvable ((QuotientGroup.mk' (center SL(2,F))).comp k).ker
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact isSolvable_comap_of_solvable_ker k (center SL(2,F))
  let φ := π.comp B.subtype
  let : Group.IsSolvable φ.ker := by
    let j : φ.ker →* π.ker :=
      (B.subtype.comp φ.ker.subtype).codRestrict π.ker (fun x => x.property)
    apply Group.isSolvable_of_isSolvable_injective (f := j)
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun z : π.ker => (z : A)) hab))
  exact odd_rank_one_solvable_kernel_parameter
    ⟨r,1,hr,ho,by omega,by simpa using hF⟩ φ hn hm

variable {G : Type*} [Group G] [Finite G]

/-- Solvable extensions of odd prime SL₂ carriers force field four for
the actual perfect smaller two-core section, including nonsplit extensions. -/
theorem solvable_extension_parameters {B K : Subgroup G} [Group.IsPerfect B]
    (hBK : B ≤ K) {n r : ℕ} (hn : 1 < n) (hr : r.Prime) (ho : Odd r)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hext : Chapter1.Section02.LocalModels.HasExtension (K ⧸ pCore 2 K)
      (fun N _ => Group.IsSolvable N) (fun Q _ => Source.IsSL Q 2 r)) : n = 2 := by
  let C := B.subgroupOf K
  let q := QuotientGroup.mk' (pCore 2 K)
  let a := subgroupOfEquivOfLe hBK
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := a.symm.toMonoidHom) a.symm.surjective
  let : Group.IsPerfect (C.map q) := Group.IsPerfect.ofSurjective
    (f := q.subgroupMap C) (q.subgroupMap_surjective C)
  have hk : IsPGroup 2 (q.subgroupMap C).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let b := (q.subgroupMap C).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective C) hk
  exact extension_section_parameter (C.map q) hn hr ho (hm.of_mulEquiv (b.symm.trans aq)) hext

open Chapter1.Section02.LocalModels

/-- The two odd-kernel rows retain their original normal kernels and covers. -/
@[expose] def OddExtensionCarrier (A : Type*) [Group A] : Prop :=
  HasExtension A (fun N _ => Group.IsNilpotent N ∧ Odd (Nat.card N))
    (fun Q _ => Source.IsSL Q 2 5) ∨
  ∃ r, Source.ExceptionalPrime r ∧ HasExtension A (ElementaryModel r 2)
    (fun Q _ => Source.IsSL Q 2 r)

/-- Both actual odd-extension carriers force the original field degree to two. -/
theorem odd_extension_parameters {B K : Subgroup G} [Group.IsPerfect B]
    (hBK : B ≤ K) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hext : OddExtensionCarrier (K ⧸ pCore 2 K)) : n = 2 := by
  rcases hext with ⟨N,hN,⟨hNil,_⟩,hQ⟩ | ⟨r,hr,N,hN,⟨eN⟩,hQ⟩
  · let := hNil
    exact solvable_extension_parameters hBK hn (by decide : Nat.Prime 5) (by decide)
      hm ⟨N,hN,inferInstance,hQ⟩
  · have hlarge : 11 ≤ r := by obtain ⟨_,hf,he⟩ := hr; omega
    have ho : Odd r := hr.1.odd_of_ne_two (by omega)
    let : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective
      (f := eN.toMonoidHom) eN.injective
    exact solvable_extension_parameters hBK hn hr.1 ho hm ⟨N,hN,inferInstance,hQ⟩

/-- The complete 11.1.1 alternatives for both nonsplit odd-extension rows. -/
theorem component_alternative_of_odd_extension {B K : Subgroup G} [Group.IsPerfect B]
    (hBK : B ≤ K) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hext : OddExtensionCarrier (K ⧸ pCore 2 K)) : ComponentAlternative B K n := by
  apply ComponentAlternative.four (odd_extension_parameters hBK hn hm hext)
  rcases hext with h | ⟨r,hr,h⟩
  · exact .nilpotentExtension h
  · exact .elementaryExtension r hr h

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Both flag normalizers retain the literal smaller section and odd extension. -/
theorem flag_component_alternative_of_odd_extension (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (_hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) (hmodel : OddExtensionCarrier (K ⧸ pCore 2 K)) :
    ComponentAlternative (f.Li i) K S.field.degree := by
  let : Group.IsPerfect (f.Li i) := localResidual_perfect _
  exact component_alternative_of_odd_extension hLK S.nonbinary hm hmodel

/-- The arbitrary-subspace application preserves the original N_T(U) Sylow
condition; field matching itself uses the stronger section argument. -/
theorem subspace_component_alternative_of_odd_extension
    (U : Subgroup G) (_hU : U ≠ ⊥) (_hUV : U ≤ f.Vi 0)
    (_hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (_hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) (hmodel : OddExtensionCarrier (K ⧸ pCore 2 K)) :
    ComponentAlternative (f.Li 0) K S.field.degree := by
  let : Group.IsPerfect (f.Li 0) := localResidual_perfect _
  exact component_alternative_of_odd_extension hLK S.nonbinary hm hmodel

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
