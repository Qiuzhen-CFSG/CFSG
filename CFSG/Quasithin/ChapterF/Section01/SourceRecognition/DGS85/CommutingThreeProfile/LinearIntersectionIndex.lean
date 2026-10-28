module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.MovedNeighbor
public import Theory.SpecificGroups.SL2.SylowCharacteristicImage

/-!
# The linear index calculation in DGS 12.3(a)

A nontrivial subgroup of a binary SL₂ Sylow, normalized by a complement
whose image supplements that Sylow in its full normalizer, is the whole
Sylow. The Sylow itself centralizes the subgroup, so the supplement and
the Sylow together supply the normalizer invariance required by the
existing root-group calculation.

Apply this to the actual image of V_x intersect Q_y at a moved neighbor z.
The complement fixes x and y, hence normalizes the intersection. Its
nonzero quotient image has order |k|; the kernel is the literal Q_z, so
the resulting relative index is [V_x intersect Q_y : V_x intersect Q_y
intersect Q_z]. This proves the index calculation after the complement
and its full-normalizer marking have been constructed. Those markings
remain local Chapter 12 obligations, not a conclusion hidden in a TYPE.

Source: DGS85, Groups and Graphs, (12.3)(a), printed p.179. The source's
separate containment V_x intersect Q_z <= Q_y is not assumed or asserted.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

private theorem image_normalized_of_sylow_supplement
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    {D : Type*} [Group D] (q : D →* SL(2,k)) (T : Sylow 2 SL(2,k))
    (A K : Subgroup D) (hAT : A.map q ≤ T)
    (hKA : K ≤ normalizer (A : Set D))
    (hcover : (T : Subgroup SL(2,k)) ⊔ K.map q = normalizer (T : Set SL(2,k))) :
    normalizer (T : Set SL(2,k)) ≤ normalizer (A.map q : Set SL(2,k)) := by
  rw [← hcover]
  apply sup_le
  · let e := Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 T
    have hc : IsMulCommutative T := ⟨⟨fun a b => e.symm.injective (by simp only [map_mul, mul_comm])⟩⟩
    let := hc
    apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro a ha t ht
    exact congrArg Subtype.val (mul_comm (⟨t, ht⟩ : T) ⟨a, hAT ha⟩)
  · exact (map_mono hKA).trans (A.le_normalizer_map q)

private theorem sylow_image_coordinates
    {D k : Type*} [Group D] [Field k] [Finite k] [CharP k 2]
    (q : D →* SL(2,k)) (W : Subgroup D) (T : Sylow 2 SL(2,k))
    (him : W.map q = (T : Subgroup SL(2,k))) :
    ∃ f : W →* Multiplicative k, Function.Surjective f ∧
      f.ker = q.ker.subgroupOf W ∧
      ∀ w : W, ((Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 T) (f w) : SL(2,k)) = q w := by
  let t : W →* T := (q.comp W.subtype).codRestrict (T : Subgroup SL(2,k)) (fun w =>
    him ▸ mem_map_of_mem q w.property)
  have ht : Function.Surjective t := by
    intro a
    have ha : (a : SL(2,k)) ∈ W.map q := him.symm ▸ a.property
    obtain ⟨w, hw, hwa⟩ := ha
    exact ⟨⟨w, hw⟩, Subtype.ext hwa⟩
  let e := Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 T
  refine ⟨e.symm.toMonoidHom.comp t, e.symm.surjective.comp ht, ?_, ?_⟩
  · ext w
    change e.symm (t w) = 1 ↔ q (w : D) = 1
    rw [← e.symm.map_one, e.symm.injective.eq_iff]
    exact Subtype.ext_iff
  · intro w
    exact congrArg (fun a : T => (a : SL(2,k))) (e.apply_symm_apply (t w))


/-- The marked complement forces the full linear Sylow image and constructs its field coordinates. -/
theorem linear_core_intersection_index
    [∀ i, Finite (F i)] {k : Type*} [Field k] [Finite k] [CharP k 2]
    {x y z : Vertex F} (A : Subgroup G)
    (hcore : A.pCoreIn 2 = Q F z)
    (e : (A ⧸ pCore 2 A) ≃* SL(2,k))
    (hVA : V F x 1 ⊓ Q F y ≤ A)
    (he : ¬ V F x 1 ⊓ Q F y ≤ Q F z)
    (T : Sylow 2 SL(2,k)) (K : Subgroup A)
    (hT : ((V F x 1 ⊓ Q F y).subgroupOf A).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))) ≤ T)
    (hKx : K.map A.subtype ≤ stabilizer F x)
    (hKy : K.map A.subtype ≤ stabilizer F y)
    (hcover : (T : Subgroup SL(2,k)) ⊔ K.map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))) = normalizer (T : Set SL(2,k))) :
    ((V F x 1 ⊓ Q F y).subgroupOf A).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))) = (T : Subgroup SL(2,k)) ∧
      (Q F z).relIndex (V F x 1 ⊓ Q F y) = Nat.card k ∧
      ∃ f : (V F x 1 ⊓ Q F y : Subgroup G) →* Multiplicative k,
        Function.Surjective f ∧ f.ker = (Q F z).subgroupOf (V F x 1 ⊓ Q F y) ∧
        ∀ w, ((Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 T) (f w) : SL(2,k)) =
          e (QuotientGroup.mk' (pCore 2 A) ⟨w, hVA w.property⟩) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  let W := V F x 1 ⊓ Q F y
  have hk : q.ker = (Q F z).subgroupOf A := by
    have hq : q.ker = pCore 2 A := by
      ext a
      change e (QuotientGroup.mk' (pCore 2 A) a) = 1 ↔ a ∈ pCore 2 A
      rw [← e.map_one, e.injective.eq_iff]
      exact QuotientGroup.eq_one_iff a
    rw [hq, ← hcore]
    exact (comap_map_eq_self_of_injective A.subtype_injective (pCore 2 A)).symm
  have hn : K.map A.subtype ≤ normalizer (W : Set G) := by
    apply (le_inf (hKx.trans (stabilizer_normalizes_V F x 1)) ?_).trans
      inf_normalizer_le_normalizer_inf
    exact hKy.trans ((stabilizer F y).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F y))))
  have hn' : K ≤ normalizer (W.subgroupOf A : Set A) := by
    intro a ha
    exact le_normalizer_comap A.subtype (hn (mem_map_of_mem A.subtype ha))
  have hne : (W.subgroupOf A).map q ≠ ⊥ := by
    intro hz
    have hh := (map_eq_bot_iff (W.subgroupOf A)).mp hz
    rw [hk] at hh
    exact he (fun w hw => hh (show (⟨w, hVA hw⟩ : A) ∈ W.subgroupOf A from hw))
  have him := Matrix.SpecialLinearGroup.subgroup_eq_sylow_of_normalizer_invariant T
    ((W.subgroupOf A).map q) hT hne
    (image_normalized_of_sylow_supplement q T _ K hT hn' hcover)
  refine ⟨him, ?_, ?_⟩
  · rw [← relIndex_subgroupOf hVA, ← hk, relIndex_ker, him]
    exact Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 T).symm.toEquiv
  · obtain ⟨f, hf, hfker, hfact⟩ := sylow_image_coordinates q (W.subgroupOf A) T him
    let eW := subgroupOfEquivOfLe hVA
    refine ⟨f.comp eW.symm.toMonoidHom, hf.comp eW.symm.surjective, ?_, ?_⟩
    · ext w
      change f (eW.symm w) = 1 ↔ (w : G) ∈ Q F z
      change eW.symm w ∈ f.ker ↔ _
      rw [hfker]
      change (eW.symm w : A) ∈ q.ker ↔ _
      rw [hk]
      rfl
    · intro w
      exact hfact (eW.symm w)


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
