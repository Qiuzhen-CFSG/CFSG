module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialChiefFactors

/-!
# The remaining point-central chief intervals in the extraspecial branch

If L₁ centralizes C_H(U)/U but K does not, normal two-perfect movement
constructs an actual H-chief interval inside that quotient. The small
involution calculation forces its order to be four or sixteen. Its
literal conjugation kernel contains O₂(H)L₁. Thus this branch cannot
be treated as the faithful order-64 interval already constructed when
L₁ moves the quotient.

The final application starts with the actual Heisenberg residual
isomorphism and exposes all cases: K centralizes the quotient, an
order-64 chief interval has exact kernel O₂(H) and localizes movement,
or the remaining point-central interval has order four or sixteen.
No chief section or action witness is assumed. Excluding the last case,
the rest of the extraspecial exclusion and the residual classification
through 14.7.52 remain obligations of the local reduction.

Source: Aschbacher–Smith, 14.7.20(2), printed p.1049. The smaller intervals
are an intermediate reduction, not an extra alternative in that theorem.
Numerators, denominators and all normalities use the original H.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

open NoncentralChiefRefinement in
/-- A K-moved interval in the point-central branch is small. Both normal
endpoints, the quotient order, and the original kernel containment are retained. -/
theorem extraspecial_exists_point_central_moved_chief
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    ∃ N B : NormalNode F.H, N ⋖ B ∧
      F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
      ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
      (Nat.card (Section N B) = 4 ∨ Nat.card (Section N B) = 16) ∧
      pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ≤ (sectionAction N B).ker := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  have hUH := sU.section_le
  have hCH : centralizer (F.U : Set G) ≤ F.H :=
    (centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) sU).trans
      (pCoreIn_le 2 F.H)
  have hUn := sU.normalized
  let Z : NormalNode F.H := ⟨F.U.subgroupOf F.H,
    (normal_subgroupOf_iff_le_normalizer hUH).mpr hUn⟩
  let Q : NormalNode F.H := ⟨(centralizer (F.U : Set G)).subgroupOf F.H,
    (normal_subgroupOf_iff_le_normalizer hCH).mpr
      (hUn.trans (normalizer_le_normalizer_centralizer _))⟩
  let R : NormalNode F.H := ⟨pResidual 2 F.H,(inferInstance : (pResidual 2 F.H).Normal)⟩
  have hRmap : R.val.map F.H.subtype = K F := rfl
  have hQ : IsPGroup 2 Q.val :=
    ((isPGroup_pCoreIn 2 F.H).to_le
      (centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) sU)).comap_subtype
  have hm' : ¬ ⁅Q.val,R.val⁆ ≤ Z.val := by
    intro hc
    apply hm
    have hh := map_mono (f := F.H.subtype) hc
    rw [map_commutator,hRmap] at hh
    change ⁅((centralizer (F.U : Set G)).subgroupOf F.H).map F.H.subtype,K F⁆ ≤
      (F.U.subgroupOf F.H).map F.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hCH,map_subgroupOf_eq_of_le hUH] at hh
  obtain ⟨N,B,hZN,hNB,hBQ,hmove⟩ := exists_moved_chief_of_normal_twoPerfect
    Z Q R (subgroupOf_mono F.H F.U.le_centralizer) hQ (isPPerfect_pResidual 2) hm'
  have hUN : F.U ≤ N.val.map F.H.subtype := by
    have hh := map_mono (f := F.H.subtype) hZN
    change (F.U.subgroupOf F.H).map F.H.subtype ≤ _ at hh
    rwa [map_subgroupOf_eq_of_le hUH] at hh
  have hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G) := by
    have hh := map_mono (f := F.H.subtype) hBQ
    change _ ≤ ((centralizer (F.U : Set G)).subgroupOf F.H).map F.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hCH] at hh
  let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB (hQ.to_le hBQ)
  let ρ := binarySectionRepresentation N B
  let : ρ.IsIrreducible := binarySection_irreducible N B hNB
  let s := ambientBinarySection F.H N B hNB.le
  have hKmove : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype := by
    intro hc
    apply hmove
    intro x hx
    have hh := mem_map_of_mem F.H.subtype hx
    rw [map_commutator,hRmap] at hh
    exact (mem_map_iff_mem F.H.subtype_injective).mp (hc hh)
  have hpoint : ⁅B.val.map F.H.subtype,F.Li L 1⁆ ≤ N.val.map F.H.subtype :=
    (commutator_mono hBC le_rfl).trans (hp.trans hUN)
  obtain ⟨σ,hσ,_,_,_,_,hd⟩ := extraspecial_point_central_chief_degree
    h hab structural previous hex hcard hexp hBC hUN s hpoint hKmove
  have hact : (sectionAction N B).ker = ρ.ker := by
    ext a
    change sectionAction N B a = 1 ↔ ρ a = 1
    constructor
    · intro ha
      ext w
      exact congrArg (fun f : MulAut (Section N B) => f w.toMul) ha
    · intro ha
      ext w
      exact congrArg Additive.toMul
        (congrArg (fun f : Module.End (ZMod 2) (Additive (Section N B)) => f (Additive.ofMul w)) ha)
  refine ⟨N,B,hNB,hUN,hBC,hKmove,?_,?_⟩
  · change Nat.card (Additive (Section N B)) = 4 ∨ Nat.card (Additive (Section N B)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    rcases hd with hd | hd
    · exact Or.inl (by rw [hd]; norm_num)
    · exact Or.inr (by rw [hd]; norm_num)
  · rw [hact]
    refine sup_le (normal_p_subgroup_le_ker ρ _ pCore_isPGroup) ?_
    intro a ha
    apply (s.action_mem_ker_iff a).mpr
    intro b hb
    exact commutator_le.mp (by rw [commutator_comm]; exact hpoint) (a : G) ha b hb


open NoncentralChiefRefinement in
/-- Original Heisenberg application with every remaining action branch exposed.
The small point-central interval is an unresolved exclusion, not the faithful
six-dimensional alternative of source 14.7.20(2). -/
theorem extraspecial_centralizer_chief_alternatives
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∨
      ∃ N B : NormalNode F.H, N ⋖ B ∧
        F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
        ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
        ((Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U) ∨
         (⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U ∧
          (Nat.card (Section N B) = 4 ∨ Nat.card (Section N B) = 16) ∧
          pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ≤ (sectionAction N B).ker)) := by
  classical
  by_cases hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U
  · exact Or.inl hc
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  apply Or.inr
  by_cases hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U
  · obtain ⟨N,B,hNB,hUN,hBC,hm,hd,hker⟩ := extraspecial_exists_point_central_moved_chief
      h hab structural previous hex hcard hexp hp hc
    exact ⟨N,B,hNB,hUN,hBC,hm,Or.inr ⟨hp,hd,hker⟩⟩
  · obtain ⟨N,B,hNB,hUN,hBC,hm,hd,hker,hu,hl⟩ := extraspecial_exists_point_moved_chief
      h hab structural previous hex hcard hexp hp
    refine ⟨N,B,hNB,hUN,hBC,?_,Or.inl ⟨hd,hker,hu,hl⟩⟩
    intro hh
    apply hm
    rw [commutator_comm]
    exact (commutator_mono le_rfl (pointResidual_le F)).trans hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
