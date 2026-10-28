module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.NormalFour
public import Theory.Representation.BinaryPermutation.PointSupport
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LiftedSeeds
public import Theory.Representation.BinaryConjugationSection.CommutatorImage

/-!
# The original normal field-four permutation module and its full support

The original overlap fixes the nonzero image of the source plane in U_J/Z.
Its J-orbit spans that entire quotient, so the marked five-point action gives
a surjective permutation-module map. Faithfulness and the element of order
five force dimension at least four. Its kernel is therefore zero or the
constant line, yielding full or deleted permutation coordinates with every
original actor and the original seed preserved.

The original K is transitive through its prescribed A₅ quotient marking.
Consequently the augmentation submodule embeds as exactly the image of
[U_J,K], not merely as a selected irreducible section. This retains the
literal central quotient and identifies the full moved support as dimension
four. It does not exclude the original relatively normal PSL₂(4) component:
the remaining ambient field-four argument and terminal A₆ assembly belong
to qt-e-suitable-component-supports. Original 14.6.18 remains explicit, with
producer qt-e-14625-source.

Source: Aschbacher--Smith 14.3.6(1), 14.6.20 and the permutation construction
at the normal rank-one endpoint, refs/quasithin.pdf printed pp.991,1037.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Modules.Recognition
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hunique hmany hcard e hab

/-- The literal plane image is a line fixed by the overlap and spanning under H. -/
theorem source_overlap_spanning_vector
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)) :
    ∃ w : Additive ((conjugateSpanBy (localModule T M) H) ⧸
        (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H)),
      w ≠ 0 ∧ seedSpace a (localModule T M) = Submodule.span (ZMod 2) {w} ∧
      (∀ g : H, (g : G) ∈ M → a.representation (QuotientGroup.mk' (pCore 2 H) g) w = w) ∧
      Submodule.span (ZMod 2) (Set.range (fun g : H =>
        a.representation (QuotientGroup.mk' (pCore 2 H) g) w)) = ⊤ := by
  let U := conjugateSpanBy (localModule T M) H
  let V := localModule T M
  let Z := centralInvolutions T
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  let f := q.comp (inclusion (show V ≤ U from le_conjugateSpanBy _ _))
  have h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hk : f.ker = Z.subgroupOf V := by
    ext v
    exact QuotientGroup.eq_one_iff _
  have hkc : Nat.card f.ker = 2 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe h.point_lt.le).toEquiv]
    exact h.point_card
  have hfc : Nat.card f.range = 2 := by
    have hh := f.ker.card_mul_index
    rw [index_ker,hkc,hcard] at hh
    omega
  obtain ⟨w,hw,hu⟩ := (Nat.card_eq_two_iff' (1 : f.range)).mp hfc
  have hw' : (w : U ⧸ Z.subgroupOf U) ≠ 1 := fun he => hw (Subtype.ext he)
  have hs (v : V) : f v = 1 ∨ f v = w.val := by
    by_cases hv : f v = 1
    · exact Or.inl hv
    · exact Or.inr (congrArg Subtype.val (hu ⟨f v,⟨v,rfl⟩⟩
        (fun he => hv (congrArg Subtype.val he))))
  have hwseed : Additive.ofMul w.val ∈ seedSpace a V := by
    obtain ⟨v,hv⟩ := w.property
    exact Submodule.subset_span ⟨⟨v,le_conjugateSpanBy V H v.property⟩,v.property,
      congrArg Additive.ofMul hv⟩
  have he : seedSpace a V = Submodule.span (ZMod 2) {Additive.ofMul w.val} := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨u,hu,rfl⟩
      rcases hs ⟨u,hu⟩ with hh | hh
      · have he : Additive.ofMul (q u) = 0 := congrArg Additive.ofMul hh
        change Additive.ofMul (q u) ∈ _
        rw [he]
        exact Submodule.zero_mem _
      · have he : Additive.ofMul (q u) = Additive.ofMul w.val := congrArg Additive.ofMul hh
        exact he ▸ Submodule.subset_span (Set.mem_singleton _)
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hwseed)
  refine ⟨Additive.ofMul w.val,hw',he,?_,?_⟩
  · intro g hg
    exact source_overlap_seed_fixed hG T hempty hM hunique hmany hcard e hab H hH a
      hwseed ⟨QuotientGroup.mk' (pCore 2 H) g,⟨g,⟨hg,g.property⟩,rfl⟩⟩
  · apply top_unique
    rw [←seedSpace_iSup_maps_eq_top a]
    apply iSup_le
    intro g
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
    rw [he,Submodule.map_span,Set.image_singleton]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨g,rfl⟩)

variable (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hsolv

/-- The whole original quotient and the full K-support have compatible five-point markings. -/
theorem source_normal_four_module_marking
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    let J := K ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (localModule T M) J
    let Z := centralInvolutions T
    ∃ hU : IsElementaryAbelian 2 U, let _ := hU
    ∃ a : LocalQuotientAction J U Z,
    ∃ (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
      (f : J →* Equiv.Perm (Fin 5)) (i : Fin 5),
      f.ker = pCore 2 J ∧
      (f.range = alternatingGroup (Fin 5) ∨ f.range = ⊤) ∧
      (∀ k : K, f ⟨k,(show K ≤ J from le_sup_left) k.property⟩ =
        eK (QuotientGroup.mk' (pCore 2 K) k)) ∧
      M.subgroupOf J = (MulAction.stabilizer (Equiv.Perm (Fin 5)) i).comap f ∧
      ∃ w : Additive (U ⧸ Z.subgroupOf U), w ≠ 0 ∧
        seedSpace a (localModule T M) = Submodule.span (ZMod 2) {w} ∧
        (∃ F : IntertwiningMap ((BinaryPermutation.representation (Fin 5)).comp f)
            (a.representation.comp (QuotientGroup.mk' (pCore 2 J))),
          Function.Surjective F ∧ F (Pi.single i 1) = w ∧
          Function.Injective (F.toLinearMap.domRestrict (BinaryPermutation.core (Fin 5))) ∧
          (originalSection a).imageSpace ⁅U,K⁆ =
            (BinaryPermutation.core (Fin 5)).map F.toLinearMap ∧
          Module.finrank (ZMod 2) ((originalSection a).imageSpace ⁅U,K⁆) = 4) ∧
        ((∃ c : BinaryPermutation.Full (Fin 5) ≃ₗ[ZMod 2] Additive (U ⧸ Z.subgroupOf U),
          c (Pi.single i 1) = w ∧ ∀ g v,
            c (BinaryPermutation.representation (Fin 5) (f g) v) =
              a.representation (QuotientGroup.mk' (pCore 2 J) g) (c v)) ∨
        (∃ c : BinaryPermutation.Deleted (Fin 5) ≃ₗ[ZMod 2] Additive (U ⧸ Z.subgroupOf U),
          c ((BinaryPermutation.constants (Fin 5)).mkQ (Pi.single i 1)) = w ∧
          ∀ g v, c (BinaryPermutation.deletedRepresentation (Fin 5) (f g) v) =
            a.representation (QuotientGroup.mk' (pCore 2 J) g) (c v))) := by
  dsimp only
  let J := K ⊔ (T : Subgroup G)
  have hstar := source_normal_four_join_minimal
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn hm
  obtain ⟨hU,a,_⟩ := source_rankTwo_bounded_placed_action
    hG T hempty hM hunique hmany hcard e hab J hstar.1
  let := hU
  obtain ⟨eK,f,i,hker,hr,hf,hi,_⟩ := source_normal_four_point_overlap
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn hm
  have hA : alternatingGroup (Fin 5) ≤ f.range := by
    rcases hr with hr | hr
    · exact hr ▸ le_rfl
    · exact hr ▸ le_top
  have ht (j k : Fin 5) : ∃ g : J, f g j = k := by
    let : MulAction.IsPretransitive (alternatingGroup (Fin 5)) (Fin 5) :=
      alternatingGroup.isPretransitive_of_three_le_card (Fin 5) (by simp)
    obtain ⟨b,hb⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) j k
    obtain ⟨g,hg⟩ := hA b.property
    exact ⟨g,by rw [hg]; exact hb⟩
  obtain ⟨w,hw,hseed,hfix,hspan⟩ := source_overlap_spanning_vector
    hG T hempty hM hunique hmany hcard e hab J hstar.1 a
  have hpoint (g : J) (hg : f g i = i) :
      a.representation (QuotientGroup.mk' (pCore 2 J) g) w = w := by
    apply hfix
    change g ∈ M.subgroupOf J
    rw [hi]
    exact hg
  have hdiv : 5 ∣ Nat.card (J ⧸ pCore 2 J) := by
    have hmJ := source_normal_four_join_models hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hn hm
    dsimp only at hmJ
    rcases hmJ with hb | hb
    · obtain ⟨b⟩ := hb
      rw [Nat.card_congr b.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    · obtain ⟨b⟩ := hb
      rw [Nat.card_congr b.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
      norm_num [Nat.factorial]
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) J) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) J))) :=
    Module.Finite.of_finite
  have hd := BinaryPrimeDegree.orderOf_le_finrank a.representation a.faithful
    (by decide : Nat.Prime 5) (by decide : 5 ≠ 2) hdiv
  rw [BinaryPrimeDegree.orderOf_two_mod_five] at hd
  let ρ := a.representation.comp (QuotientGroup.mk' (pCore 2 J))
  obtain ⟨F,hF,hFw⟩ := BinaryPermutation.quotient_of_point_fixed ρ f ht i w hpoint hspan
  have hkF : F.toLinearMap.ker ≤ BinaryPermutation.constants (Fin 5) := by
    rcases BinaryPermutation.five_point_kernel ρ f ht F hF hd with hk | hk
    · rw [hk]; exact bot_le
    · exact hk.le
  have htrans (j k : Fin 5) : ∃ g : K.subgroupOf J, f g j = k := by
    let : MulAction.IsPretransitive (alternatingGroup (Fin 5)) (Fin 5) :=
      alternatingGroup.isPretransitive_of_three_le_card (Fin 5) (by simp)
    obtain ⟨b,hb⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) j k
    obtain ⟨k',hk'⟩ := eK.surjective b
    obtain ⟨k',rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) k'
    refine ⟨⟨⟨k',(show K ≤ J from le_sup_left) k'.property⟩,k'.property⟩,?_⟩
    rw [hf,hk']
    exact hb
  obtain ⟨hs,hdim,hinj⟩ := BinaryPermutation.five_point_support ρ f (K.subgroupOf J)
    htrans F hF hkF
  have himage : (originalSection a).imageSpace ⁅conjugateSpanBy (localModule T M) J,K⁆ =
      subspaceCommutator ρ ⊤ (K.subgroupOf J) := by
    rw [commutator_comm,(originalSection a).imageSpace_commutator K _ le_sup_left le_rfl,
      (originalSection a).imageSpace_self]
  exact ⟨hU,a,eK,f,i,hker,hr,hf,hi,w,hw,hseed,
    ⟨F,hF,hFw,hinj,himage.trans hs,himage ▸ hdim⟩,
    BinaryPermutation.five_point_marking
      (a.representation.comp (QuotientGroup.mk' (pCore 2 J))) f ht i w hpoint hspan hd⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
