module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Decomposition
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.SingleComponent.Terminal
public import Theory.Representation.PSL3Two.NaturalDualExtension
public import Theory.Representation.BinaryConjugationSection.SupportSpan
public import Theory.GroupTheory.SubgroupConjugation.PairPermutation

/-!
# The literal support-normalizer action from the original component sections

The index-two Sylow orbit and Mc=KT make Mc permute the two full supports.
The natural support's normalizer preserves both. Extend their original
coordinate maps to this normalizer; the paired L₃(2) extension theorem
forces the second action to be the dual of the first and proves fullness.
Gaschütz's component sum, lifted through the original central kernel, also
puts the whole commutator [U,Mc] in the same support join.

These conclusions discharge the action and whole-module premises of the
existing single-component crossing and residual-coordinate consumers.
SourceComplete applies this theorem to the supports constructed from the
original source hypotheses. Neither supports nor their action are replaced
by irreducible subquotients.

Source: Aschbacher--Smith, 14.6.22--24, printed pp.1038--1042.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hunique hmany hcard e hab in
/-- Construct the same full natural/dual action on Mc∩N(A), the pair permutation,
and the whole commutator bound from the original marked component supports. -/
theorem source_actions_of_component_sections
    (K : Subgroup G) (hKM : K ≤ Mc) (hnK : (K.subgroupOf Mc).Normal)
    (hgen : K ⊔ (T : Subgroup G) = Mc)
    (j : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (A B : Subgroup G)
    (d : BinaryConjugationSection K A (centralInvolutions T)
      (BinaryLinearThree.W.comp (j.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))))
    (d' : BinaryConjugationSection K B (centralInvolutions T)
      (BinaryLinearThree.W.dual.comp (j.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))))
    (hfull : ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = A ⊔ B)
    (hsep : A ⊓ B = centralInvolutions T)
    (s : T) (hsB : B = A.map (MulAut.conj (s:G)⁻¹).toMonoidHom)
    (hi : (normalizer (A : Set G)).relIndex (T : Subgroup G) = 2)
    (hN : Mc ≤ normalizer ((A ⊔ B : Subgroup G) : Set G)) :
    A ≤ conjugateSpanBy (localModule T M) Mc ∧
    B ≤ conjugateSpanBy (localModule T M) Mc ∧
    ⁅conjugateSpanBy (localModule T M) Mc,Mc⁆ ≤ A ⊔ B ∧
    (∀ x ∈ Mc, A.map (MulAut.conj x).toMonoidHom = A ∨
      A.map (MulAut.conj x).toMonoidHom = B) ∧
    ∃ f : (Mc ⊓ normalizer (A : Set G) : Subgroup G) →* BinaryLinear.GL (Fin 3 → ZMod 2),
      Function.Surjective f ∧
      Nonempty (BinaryConjugationSection (Mc ⊓ normalizer (A : Set G)) A (centralInvolutions T)
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f)) ∧
      Nonempty (BinaryConjugationSection (Mc ⊓ normalizer (A : Set G)) B (centralInvolutions T)
        (Representation.dual (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f))) := by
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let U := conjugateSpanBy (localModule T M) Mc
  let Z := centralInvolutions T
  let L := Mc ⊓ normalizer (A : Set G)
  have hMK : Mc ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKM).mp hnK
  have hprod : (Mc : Set G) = (K : Set G) * ((T : Subgroup G) : Set G) := by
    rw [←hgen]
    exact coe_mul_of_right_le_normalizer_left K (T : Subgroup G) (h.T_le_H.trans hMK)
  have hSU : A ⊔ B ≤ U := hfull.symm.le.trans
    (le_normalizer_iff_commutator_le_left.mp (hKM.trans (le_normalizer_conjugateSpanBy _ _)))
  have hAU := le_sup_left.trans hSU
  have hBU := le_sup_right.trans hSU
  have hne : A ≠ B := by
    intro he
    have hAZ : A ≤ Z := by
      change A ≤ centralInvolutions T
      rw [←hsep,he,inf_idem]
    obtain ⟨v,hv⟩ := exists_ne (0 : BinaryLinearThree.Vector)
    obtain ⟨a,ha⟩ := d.onto (Multiplicative.ofAdd v)
    have hz := (d.coordinates_eq_one_iff a).mpr (hAZ a.property)
    exact hv (congrArg Multiplicative.toAdd (ha.symm.trans hz))
  have hsN : (s:G)⁻¹ ∉ normalizer (A : Set G) := by
    intro hs
    exact hne ((mem_normalizer_iff_map_conj_eq.mp hs).symm.trans hsB.symm)
  have hpairT (x : G) (hx : x ∈ (T : Subgroup G)) :
      A.map (MulAut.conj x).toMonoidHom = A ∨ A.map (MulAut.conj x).toMonoidHom = B := by
    by_cases hxN : x ∈ normalizer (A : Set G)
    · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp hxN)
    · have hsx : (s:G)*x ∈ normalizer (A : Set G) := by
        apply (mul_mem_iff_of_index_two hi (a := s) (b := ⟨x,hx⟩)).mpr
        exact iff_of_false (fun hs => hsN ((normalizer (A : Set G)).inv_mem hs)) hxN
      apply Or.inr
      rw [hsB]
      calc
        A.map (MulAut.conj x).toMonoidHom =
            (A.map (MulAut.conj ((s:G)*x)).toMonoidHom).map (MulAut.conj (s:G)⁻¹).toMonoidHom := by
          rw [map_map]
          congr 1
          ext a
          simp [MulAut.conj_apply,mul_assoc]
        _ = _ := congrArg (Subgroup.map (MulAut.conj (s:G)⁻¹).toMonoidHom)
          (mem_normalizer_iff_map_conj_eq.mp hsx)
  have hpair (x : G) (hx : x ∈ Mc) :
      A.map (MulAut.conj x).toMonoidHom = A ∨ A.map (MulAut.conj x).toMonoidHom = B := by
    obtain ⟨k,hk,t,ht,rfl⟩ := (show x ∈ (K:Set G)*((T:Subgroup G):Set G) from hprod ▸ hx)
    have he : (MulAut.conj k).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
        (MulAut.conj (k*t)).toMonoidHom := by ext a; simp [MulAut.conj_apply,mul_assoc]
    rw [←he,←map_map]
    rcases hpairT t ht with ha | hb
    · rw [ha]; exact Or.inl (mem_normalizer_iff_map_conj_eq.mp (d.normalized hk))
    · rw [hb]; exact Or.inr (mem_normalizer_iff_map_conj_eq.mp (d'.normalized hk))
  have hperm := pair_permutation_of_conjugate_orbit Mc A B hpair (s:G)⁻¹
    (h.T_le_H ((T:Subgroup G).inv_mem s.property)) hsB.symm
  have hLB : L ≤ normalizer (B : Set G) := by
    intro x hx
    rcases hperm x hx.1 with hp | hp
    · exact mem_normalizer_iff_map_conj_eq.mpr hp.2
    · exact (hne ((mem_normalizer_iff_map_conj_eq.mp hx.2).symm.trans hp.1)).elim
  have hLZ : L ≤ normalizer (Z : Set G) :=
    inf_le_left.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  let : IsElementaryAbelian 2 U := h.UH_elementary_of_V_le_QH
    ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective (inclusion hAU) (inclusion_injective _)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective (inclusion hBU) (inclusion_injective _)
  obtain ⟨η,hη⟩ := d.exists_original_quotient_action (show L ≤ normalizer (A:Set G) from inf_le_right) hLZ
  obtain ⟨ν,hν⟩ := d'.exists_original_quotient_action hLB hLZ
  have hKL : K ≤ L := le_inf hKM d.normalized
  let : (K.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hKL).mpr (inf_le_left.trans hMK)
  let q := (j.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp
    (subgroupOfEquivOfLe hKL).toMonoidHom
  have hq : Function.Surjective q := j.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (subgroupOfEquivOfLe hKL).surjective)
  have hn (k : K.subgroupOf L) : η k = BinaryLinearThree.W (q k) := by
    apply LinearMap.ext
    intro v
    obtain ⟨a,ha⟩ := d.onto (Multiplicative.ofAdd v)
    rw [←show (d.coordinates a).toAdd = v from congrArg Multiplicative.toAdd ha,hη]
    exact d.equivariant ((subgroupOfEquivOfLe hKL) k) a
  have hd (k : K.subgroupOf L) : ν k = BinaryLinearThree.W.dual (q k) := by
    apply LinearMap.ext
    intro v
    obtain ⟨b,hb⟩ := d'.onto (Multiplicative.ofAdd v)
    rw [←show (d'.coordinates b).toAdd = v from congrArg Multiplicative.toAdd hb,hν]
    exact d'.equivariant ((subgroupOfEquivOfLe hKL) k) b
  obtain ⟨f,hf,hfη,hfν⟩ := BinaryLinearThree.NaturalDual.paired_extension η ν (K.subgroupOf L) q hq hn hd
  have hAL : A ≤ L := le_inf (hAU.trans h.UH_le_H) A.le_normalizer
  have hBL : B ≤ L := le_inf (hBU.trans h.UH_le_H)
    ((hBU.trans ((le_centralizer_iff_isMulCommutative.mpr hab).trans (centralizer_le hAU))).trans
      (Subgroup.centralizer_le_normalizer _))
  let c : BinaryConjugationSection L A Z η := {
    section_le := hAL, kernel_le := d.kernel_le, normalized := inf_le_right,
    coordinates := d.coordinates, onto := d.onto, kernel_eq := d.kernel_eq,
    equivariant := fun l a => (hη l a).symm }
  let c' : BinaryConjugationSection L B Z ν := {
    section_le := hBL, kernel_le := d'.kernel_le, normalized := hLB,
    coordinates := d'.coordinates, onto := d'.onto, kernel_eq := d'.kernel_eq,
    equivariant := fun l a => (hν l a).symm }
  have hcomm : ⁅U,Mc⁆ ≤ A ⊔ B := by
    obtain ⟨ρ,⟨cU⟩⟩ := BinaryConjugationSection.exists_conjugation_coordinates Mc U Z h.UH_le_H
      (le_normalizer_conjugateSpanBy _ _) (d.kernel_le.trans hAU)
      (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    have hspan := ComponentSupports.source_component_sum_sup_fixed
      hG T hempty hM hunique hmany hcard e hab ρ cU (fun (_ : Unit) => K) (fun _ => hKM) (by
        intro m
        obtain ⟨k,hk,t,ht,he⟩ := (show (m:G) ∈ (K:Set G)*((T:Subgroup G):Set G) from hprod ▸ m.property)
        exact ⟨⟨k,hKM hk⟩,by simpa only [iSup_const] using (show (⟨k,hKM hk⟩ : Mc) ∈ K.subgroupOf Mc from hk),⟨t,h.T_le_H ht⟩,ht,Subtype.ext he⟩)
    simp only [iSup_const] at hspan
    rw [hfull] at hspan
    have hUZ : U ≤ normalizer (Z:Set G) := h.UH_le_H.trans
      (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    have hcover := cU.le_sup_fixed_preimage_of_spanning_image (A ⊔ B)
      (d.kernel_le.trans le_sup_left) hUZ hspan
    apply (commutator_mono hcover le_rfl).trans
    exact commutator_sup_le_of_relative_normal U (A ⊔ B) (commutatorPreimage U Mc Z) Mc (A ⊔ B)
      ((le_centralizer_iff_isMulCommutative.mpr hab).trans (centralizer_le hSU) |>.trans
        (Subgroup.centralizer_le_normalizer _))
      hSU (commutatorPreimage_le _ _ _) (le_normalizer_iff_commutator_le_left.mp hN)
      ((commutator_commutatorPreimage_le _ _ _ hUZ).trans (d.kernel_le.trans le_sup_left))
  exact ⟨hAU,hBU,hcomm,hpair,f,hf,hfη ▸ ⟨c⟩,hfη ▸ hfν ▸ ⟨c'⟩⟩
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
