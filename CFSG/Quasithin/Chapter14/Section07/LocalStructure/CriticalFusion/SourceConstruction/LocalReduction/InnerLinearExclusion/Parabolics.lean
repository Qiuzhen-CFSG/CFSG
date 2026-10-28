module
public import Theory.SpecificGroups.BinaryLinear.CubicSylowGeneration
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Pairs
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The actual rank-two parabolics through a marked binary node

Index three recognizes the original point-parabolic image as one omitted
cut in the same Sylow flag. Every pair of omitted cuts through that node
contains the marked parabolic; elementary-root generation proves that their
join is the whole group. The diagonal block maps give PSL₃(2) for adjacent
nodes and S₃ × S₃ for nonadjacent nodes in dimensions four and five.
All pairs are included, in particular the middle adjacent pair in dimension
five. Their full preimages generate through the actual two-group kernel,
and their intrinsic two-core quotients are transported through that map.

This is the rank-two calculation in Aschbacher–Smith 14.7.51, printed
p.1065, refs/quasithin.pdf. The finite block checks only concern the three
or four nodes; no enumeration of a full linear group is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions

private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

/-- Index three identifies the marked parabolic with a single omitted cut
of the same Sylow flag. -/
theorem exists_marked_node {m : ℕ}
    (S : Sylow 2 (LinearGroup (m + 1)))
    (P : Subgroup (LinearGroup (m + 1))) (hSP : (S : Subgroup _) ≤ P)
    (hi : (S : Subgroup _).relIndex P = 3) :
    ∃ (b : Basis m) (i : Fin m),
      (S : Subgroup _) = cutStabilizer b Set.univ ∧ P = minimalParabolic b i := by
  obtain ⟨b,cuts,hb,hP⟩ := BinaryLinear.SylowFlagOvergroups.exists_flag_of_sylow_le S P hSP
  have hne : cuts ≠ Set.univ := by
    intro he
    rw [hP,he,←hb,relIndex_self] at hi
    norm_num at hi
  obtain ⟨i,hiC⟩ : ∃ i, i ∉ cuts := by
    by_contra! hall
    exact hne (Set.eq_univ_of_forall hall)
  have hmin : minimalParabolic b i ≤ P := by
    rw [hP]
    apply (cutStabilizer_le_iff b _ _).mpr
    intro j hj
    exact fun he => hiC (he ▸ hj)
  have hSmin : (S : Subgroup _) ≤ minimalParabolic b i := by
    rw [hb]
    exact (cutStabilizer_le_iff b _ _).mpr (Set.subset_univ _)
  have hm := relIndex_mul_relIndex S (minimalParabolic b i) P hSmin hmin
  rw [hi,hb,BinaryLinear.CubicSylowGeneration.minimalParabolic_index] at hm
  have hone : (minimalParabolic b i).relIndex P = 1 := by omega
  exact ⟨b,i,hb,le_antisymm (relIndex_eq_one.mp hone) hmin⟩

/-- The rank-two parabolics through any fixed node generate the whole
binary linear group; this is proved from ordered elementary-root generation. -/
theorem iSup_twoNodeParabolic_eq_top {m : ℕ} (hm : 2 ≤ m)
    (b : Basis m) (i : Fin m) :
    (⨆ j : {j : Fin m // j ≠ i}, cutStabilizer b ({i,j.val} : Set (Fin m))ᶜ) = ⊤ := by
  let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  obtain ⟨j,hji⟩ := exists_ne i
  apply top_unique
  rw [←iSup_minimalParabolic_eq_top (by omega : 1 ≤ m) b]
  apply iSup_le
  intro k
  by_cases hki : k = i
  · subst k
    apply le_trans ?_ (le_iSup (fun j : {j : Fin m // j ≠ i} =>
      cutStabilizer b ({i,j.val} : Set (Fin m))ᶜ) ⟨j,hji⟩)
    apply (cutStabilizer_le_iff b _ _).mpr
    intro x hx
    exact fun he => hx (Or.inl he)
  · apply le_trans ?_ (le_iSup (fun j : {j : Fin m // j ≠ i} =>
      cutStabilizer b ({i,j.val} : Set (Fin m))ᶜ) ⟨k,hki⟩)
    apply (cutStabilizer_le_iff b _ _).mpr
    intro x hx
    exact fun he => hx (Or.inr he)

/-- A full quotient with two-group kernel recognizes the actual S₃
point-parabolic image and constructs its generating rank-two preimages. -/
theorem exists_generating_twoNode_preimages
    {X : Type*} [Group X] [Finite X] {m : ℕ} (hm : 2 ≤ m)
    (q : X →* LinearGroup (m + 1)) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (S : Sylow 2 X) (B : Subgroup X)
    (hSB : (S : Subgroup X) ≤ B)
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) :
    ∃ (b : Basis m) (i : Fin m),
      (S : Subgroup X).map q = cutStabilizer b Set.univ ∧
      B.map q = minimalParabolic b i ∧
      (∀ j : {j : Fin m // j ≠ i},
        B ≤ (cutStabilizer b ({i,j.val} : Set (Fin m))ᶜ).comap q) ∧
      (⨆ j : {j : Fin m // j ≠ i},
        (cutStabilizer b ({i,j.val} : Set (Fin m))ᶜ).comap q) = ⊤ := by
  let S' := S.mapSurjective hq
  have hker : q.ker ≤ (S : Subgroup X) := hk.le_sylow_of_normal S
  have hi : (S' : Subgroup _).relIndex (B.map q) = 3 := by
    change ((S : Subgroup X).map q).relIndex (B.map q) = 3
    rw [relIndex_map_map, sup_eq_left.mpr hker, sup_eq_left.mpr (hker.trans hSB)]
    exact SymmetricThreeTwoCore.sylow_index_three eB (S.subtype hSB)
  obtain ⟨b,i,hb,hBi⟩ := exists_marked_node S' (B.map q) (map_mono hSB) hi
  have hBpre (j : {j : Fin m // j ≠ i}) :
      B ≤ (cutStabilizer b ({i,j.val} : Set (Fin m))ᶜ).comap q := by
    apply (map_le_iff_le_comap).mp
    rw [hBi]
    apply (cutStabilizer_le_iff b _ _).mpr
    intro x hx
    exact fun he => hx (Or.inl he)
  refine ⟨b,i,hb,hBi,hBpre,?_⟩
  let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  obtain ⟨j,hji⟩ := exists_ne i
  let J := ⨆ j : {j : Fin m // j ≠ i},
    (cutStabilizer b ({i,j.val} : Set (Fin m))ᶜ).comap q
  have hkJ : q.ker ≤ J := hker.trans (hSB.trans ((hBpre ⟨j,hji⟩).trans (le_iSup (fun j : {j : Fin m // j ≠ i} =>
      (cutStabilizer b ({i,j.val} : Set (Fin m))ᶜ).comap q) ⟨j,hji⟩)))
  apply map_injective_of_ker_le q hkJ le_top
  rw [map_top_of_surjective _ hq]
  change (⨆ j : {j : Fin m // j ≠ i},
    (cutStabilizer b ({i,j.val} : Set (Fin m))ᶜ).comap q).map q = ⊤
  rw [Subgroup.map_iSup]
  simp only [map_comap_eq_self_of_surjective hq]
  exact iSup_twoNodeParabolic_eq_top hm b i

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open BinaryLinear.SmallParabolicLevi BinaryLinear.SmallParabolicLevi.TwoNodes

/-- The two literal quotient models of a rank-two parabolic in the inner
binary-linear branch of 14.7.51. -/
@[expose] def RankTwoQuotient (X : Type*) [Group X] : Prop :=
  Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
  Nonempty ((X ⧸ pCore 2 X) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))

private def threeBlockEquiv (c : Fin 5 → Fin 5) (k : Fin 5)
    (hk : Fintype.card (Block c k) = 3)
    (ho : ∀ l, l ≠ k → Fintype.card (Block c l) ≤ 1) :
    (∀ l : Fin 5, BinaryLinear.GL (BlockSpace c l)) ≃* LinearGroup 3 := by
  classical
  let f := Pi.evalMonoidHom (fun l : Fin 5 => BinaryLinear.GL (BlockSpace c l)) k
  have hf : Function.Bijective f := by
    constructor
    · intro a b he
      funext l
      by_cases hl : l = k
      · subst l; exact he
      exact (linearBlock_eq_one_of_card_le_one c l (ho l hl) (a l)).trans
        (linearBlock_eq_one_of_card_le_one c l (ho l hl) (b l)).symm
    · intro a
      exact ⟨Function.update 1 k a, Function.update_self ..⟩
  let e : BlockSpace c k ≃ₗ[ZMod 2] Space 3 :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
      ((Fintype.equivFin (Block c k)).trans (finCongr hk)).symm
  exact (MulEquiv.ofBijective f hf).trans (linearGroupCongr e)

private def adjacentPairBlock (i j : Fin 4) : Fin 5 := (min i j).castSucc

private theorem adjacentPair_card (i j : Fin 4)
    (hij : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    Fintype.card (Block (pairLabel i j) (adjacentPairBlock i j)) = 3 ∧
      ∀ k : Fin 5, k ≠ adjacentPairBlock i j →
        Fintype.card (Block (pairLabel i j) k) ≤ 1 := by
  classical
  have h4 : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  have h5 : (Finset.univ : Finset (Fin 5)) = {0,1,2,3,4} := by decide
  have hlabel : pairLabel i j =
      if min i.val j.val = 0 then ![0,0,0,1,2]
      else if min i.val j.val = 1 then ![0,1,1,1,2] else ![0,1,2,2,2] := by
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> funext k <;> fin_cases k <;>
      simp [pairLabel,cutLabel,h4,Finset.filter_insert,Finset.filter_singleton]
  constructor
  · simp only [Block,Fintype.card_subtype]
    rw [hlabel]
    fin_cases i <;> fin_cases j <;> norm_num at hij <;>
      simp [adjacentPairBlock,h5,Finset.filter_insert,Finset.filter_singleton]
  · intro k hk
    simp only [Block,Fintype.card_subtype]
    rw [hlabel]
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> fin_cases k <;>
      simp_all [adjacentPairBlock,Finset.filter_insert,Finset.filter_singleton]

/-- Every adjacent or nonadjacent pair in the original five-space flag has
its stated intrinsic two-core quotient, including the middle adjacent pair. -/
theorem five_twoNode_quotient (b : Basis 4) (i j : Fin 4) (hij : i ≠ j) :
    RankTwoQuotient (cutStabilizer b ({i,j} : Set (Fin 4))ᶜ) := by
  by_cases ha : i.val + 1 = j.val ∨ j.val + 1 = i.val
  · have hc := adjacentPair_card i j ha
    exact Or.inl ⟨(flagDiagonalQuotientEquiv b _).trans
      ((threeBlockEquiv (pairLabel i j) (adjacentPairBlock i j) hc.1 hc.2).trans
        linearThreeEquivProjective)⟩
  · have hn : i.val + 1 < j.val ∨ j.val + 1 < i.val := by
      have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
      omega
    exact Or.inr ⟨(flagDiagonalQuotientEquiv b _).trans (pairFactorsEquiv i j hn)⟩

private theorem oneSpace_subsingleton : Subsingleton (LinearGroup 1) := by
  apply Finite.card_le_one_iff_subsingleton.mp
  have hc : Nat.card (LinearGroup 1) = 1 := by
    rw [←Nat.card_congr (matrixEquivLinear 1).toEquiv,Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  omega

private def dropFirstOne : LinearGroup 1 × LinearGroup 3 ≃* LinearGroup 3 := by
  let := oneSpace_subsingleton
  exact MulEquiv.ofBijective (MonoidHom.snd _ _)
    ⟨fun x y h => Prod.ext (Subsingleton.elim _ _) h,fun x => ⟨(1,x),rfl⟩⟩

private def dropLastOne : LinearGroup 3 × LinearGroup 1 ≃* LinearGroup 3 := by
  let := oneSpace_subsingleton
  exact MulEquiv.ofBijective (MonoidHom.fst _ _)
    ⟨fun x y h => Prod.ext h (Subsingleton.elim _ _),fun x => ⟨(x,1),rfl⟩⟩

private theorem four_cut_quotient (b : Basis 3) (k : Fin 3) :
    RankTwoQuotient (parabolic (cutSpace b k)) := by
  let W := cutSpace b k
  have hW : Module.finrank (ZMod 2) W = k.val + 1 := cutSpace_finrank b k
  have hQ : Module.finrank (ZMod 2) (Space 4 ⧸ W) = 3 - k.val := by
    have hh := W.finrank_quotient_add_finrank
    have hh' : Module.finrank (ZMod 2) (Space 4 ⧸ W) + (k.val + 1) = 4 := by
      simpa only [hW,Module.finrank_fin_fun] using hh
    omega
  let c : W ≃ₗ[ZMod 2] Space (k.val + 1) := LinearEquiv.ofFinrankEq _ _ (by simpa using hW)
  let q : (Space 4 ⧸ W) ≃ₗ[ZMod 2] Space (3 - k.val) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hQ)
  let e := quotientTwoCoreEquivOfCoordinates W c q
  fin_cases k
  · exact Or.inl ⟨e.trans (dropFirstOne.trans linearThreeEquivProjective)⟩
  · exact Or.inr ⟨e.trans (linearTwoEquivSymmetricThree.prodCongr linearTwoEquivSymmetricThree)⟩
  · exact Or.inl ⟨e.trans (dropLastOne.trans linearThreeEquivProjective)⟩

/-- Every two-node parabolic in the four-space flag has quotient PSL₃(2)
or S₃ × S₃. The middle plane gives the product row. -/
theorem four_twoNode_quotient (b : Basis 3) (i j : Fin 3) (hij : i ≠ j) :
    RankTwoQuotient (cutStabilizer b ({i,j} : Set (Fin 3))ᶜ) := by
  have hp : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3,
      ∀ x : Fin 3, (x ≠ i ∧ x ≠ j) ↔ x = k := by decide
  obtain ⟨k,hk'⟩ := hp i j hij
  have hk : ({i,j} : Set (Fin 3))ᶜ = {k} := by
    ext x
    simpa only [Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using hk' x
  have he : cutStabilizer b ({i,j} : Set (Fin 3))ᶜ = parabolic (cutSpace b k) := by
    rw [hk]
    ext g
    simp only [mem_cutStabilizer,Set.mem_singleton_iff,forall_eq]
    rfl
  rw [he]
  exact four_cut_quotient b k

/-- The rank-two rows in both source dimensions. -/
theorem twoNode_quotient {m : ℕ} (hm : m = 3 ∨ m = 4)
    (b : Basis m) (i j : Fin m) (hij : i ≠ j) :
    RankTwoQuotient (cutStabilizer b ({i,j} : Set (Fin m))ᶜ) := by
  rcases hm with rfl | rfl
  · exact four_twoNode_quotient b i j hij
  · exact five_twoNode_quotient b i j hij

/-- Pull the actual rank-two quotient through the given two-group kernel. -/
theorem rankTwoQuotient_comap {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (q : X →* Y) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (P : Subgroup Y) (hP : RankTwoQuotient P) : RankTwoQuotient (P.comap q) := by
  let f : P.comap q →* P := (q.comp (P.comap q).subtype).codRestrict P (fun x => x.property)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := hq y
    exact ⟨⟨x,show q x ∈ P from hx.symm ▸ y.property⟩,Subtype.ext hx⟩
  have hfk : IsPGroup 2 f.ker := by
    let g : f.ker →* q.ker :=
      ((P.comap q).subtype.comp f.ker.subtype).codRestrict q.ker (by
        intro x
        exact congrArg Subtype.val x.property)
    apply hk.of_injective g
    intro a b he
    have hv : (a.val.val : X) = b.val.val := congrArg (fun z : q.ker => (z : X)) he
    exact Subtype.ext (Subtype.ext hv)
  let e := f.pCoreQuotientEquiv hf hfk
  exact hP.imp (fun h => ⟨e.trans h.some⟩) (fun h => ⟨e.trans h.some⟩)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
open Subgroup

/-- The intrinsic core quotient of the actual ambient image. -/
theorem rankTwoQuotient_map {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Injective f)
    (P : Subgroup X) (hP : RankTwoQuotient P) : RankTwoQuotient (P.map f) := by
  let e := (P.equivMapOfInjective f hf).symm
  let c := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  exact hP.imp (fun h => ⟨c.trans h.some⟩) (fun h => ⟨c.trans h.some⟩)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
