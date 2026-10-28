module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration.Transport
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.Reduction

/-!
# Generation through the actual local action

Restrict an H-action with kernel O₂(H) to LS. Its kernel is exactly O₂(LS),
since LS is normal in H. If two conjugates of the Baumann image generate
the action group, normality also makes the restricted action surjective.
The quotient transport then chooses a genuine conjugator in L and replaces
both Baumann subgroups by Uˣ modulo the actual two-core.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.6,
printed pp.156–157 (PDF pp.167–168).
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration
open Subgroup
universe u v
variable {G : Type u} [Group G] [Finite G]
variable {M : Type v} [Group M]
variable {K : GroupClass.{u}} {A H R L : Subgroup G}

omit [Finite G] in
/-- Restricting the acting homomorphism preserves the image of each subgroup. -/
theorem restrict_image {T B : Subgroup G} (hTH : T ≤ H) (hBT : B ≤ T)
    (f : H →* M) :
    (B.subgroupOf T).map (f.comp (inclusion hTH)) = (B.subgroupOf H).map f := by
  ext p
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨inclusion hTH b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hBT hb⟩, hb, rfl⟩

/-- The action on LS has kernel the actual local two-core. -/
theorem restriction_kernel
    (h : Configuration K A H R L) (f : H →* M) (hf : f.ker = pCore 2 H) :
    (f.comp (inclusion (Baumann.block_baumann_join_le_H h))).ker =
      (Q R L).subgroupOf (L ⊔ S R) := by
  ext t
  change f (inclusion (Baumann.block_baumann_join_le_H h) t) = 1 ↔ (t : G) ∈ Q R L
  rw [← MonoidHom.mem_ker, hf, Baumann.localCore_eq_inter h]
  change inclusion (Baumann.block_baumann_join_le_H h) t ∈ pCore 2 H ↔
    (t : G) ∈ L ⊔ S R ∧ (t : G) ∈ pCoreIn 2 H
  constructor
  · intro ht
    exact ⟨t.property, mem_map_of_mem H.subtype ht⟩
  · rintro ⟨_, a, ha, he⟩
    exact (show a = inclusion (Baumann.block_baumann_join_le_H h) t from Subtype.ext he) ▸ ha

/-- Generation in the actual H-action lifts to a conjugator in L, modulo O₂(LS). -/
theorem pair_of_action
    (h : Configuration K A H R L) (f : H →* M) (hf : Function.Surjective f)
    (hker : f.ker = pCore 2 H)
    (hpair : ∃ g, ((S R).subgroupOf H).map f ⊔
      (((S R).subgroupOf H).map f).map (MulAut.conj g).toMonoidHom = ⊤)
    {V : Subgroup G} (hspan : S R = V ⊔ Q R L) :
    ∃ y ∈ L, L ≤ (V ⊔ V.map (MulAut.conj y).toMonoidHom) ⊔ Q R L := by
  let T := L ⊔ S R
  let hTH : T ≤ H := Baumann.block_baumann_join_le_H h
  let fT := f.comp (inclusion hTH)
  have hr : fT.range = (T.subgroupOf H).map f := by
    rw [MonoidHom.range_comp, inclusion_range]
  let _ : (T.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hTH).mpr (Baumann.normalizes_block_baumann_join h)
  have hn : fT.range.Normal := hr ▸ Subgroup.Normal.map inferInstance f hf
  let _ := hn
  have hB : ((S R).subgroupOf H).map f ≤ fT.range := by
    rw [← restrict_image hTH le_sup_right]
    exact map_le_range _ _
  obtain ⟨g, hg⟩ := hpair
  have hsurj : Function.Surjective fT := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← hg]
    apply sup_le hB
    rintro z ⟨b, hb, rfl⟩
    exact hn.conj_mem b (hB hb) g
  obtain ⟨y, hy, hgen⟩ := choose_block_conjugator h fT hsurj (by
    rw [restrict_image hTH le_sup_right]
    exact ⟨g, hg⟩)
  exact ⟨y, hy, lift_quotient_pair hspan fT (restriction_kernel h f hker) hgen⟩

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration
end
