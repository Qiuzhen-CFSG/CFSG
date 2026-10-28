module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.Setup
public import Theory.GroupTheory.Commutator.PerfectQuotientPGroup
public import Theory.GroupTheory.Commutator.TwoCoverComparison
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Recognizing and marking the exceptional double cover

Given the actual quotient `M/O₂(M) ≃ PSL₃(2)` and a normal subgroup `R₀`
whose image of `O₂(M)` has order two, we identify `M/R₀` with `SL₂(7)`.
The order-two kernel is central. Its perfect quotient makes the
abelianization a two-group, and source 15.2(g), `O²(M) = M`, kills that
abelianization. Thus the kernel meets the derived subgroup nontrivially;
the proved comparison of central two-covers identifies the whole group.
This establishes the needed derived-kernel condition without assuming
nonsplitting or perfectness of the unknown cover.

Every nonidentity element of the kernel maps to `-I`, since the center of
`SL₂(7)` consists of the two scalar matrices. Both quotient maps are the
literal maps inside `M`. The third isomorphism theorem identifies
`(M/R₀)/(V/R₀)` with `M/V` before the actual order-168 model comparison is
applied. The ATLAS attribution and license reside in the imported comparison.

Source: GLS, Volume 4, Chapter 2, Lemma 15.7, `Chapter2.tex` line 2754.
The local construction of `R₀`, its order, and the action identifying
`M/V` remain separate source obligations.
-/

open Subgroup
open scoped MatrixGroups

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem perfect_image_of_twoResidual_of_two_kernel
    {X E B : Type*} [Group X] [Group E] [Group B] [Group.IsPerfect B]
    (s : X →* E) (hs : Function.Surjective s)
    (hres : External.hallPResidual 2 X = ⊤)
    (f : E →* B) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    Group.IsPerfect E := by
  have hp := CentralExtension.abelianization_isPGroup_of_perfect_quotient f hf hker
  have hk := External.hallPResidual_le_ker_of_isPGroup
    ((QuotientGroup.mk' (commutator E)).comp s) hp
  rw [hres] at hk
  refine ⟨top_unique ?_⟩
  intro x _
  obtain ⟨y, rfl⟩ := hs x
  exact (QuotientGroup.eq_one_iff (s y)).mp (hk (mem_top y))

private theorem sl2Seven_center_nonidentity_eq_neg_one
    {x : SL(2, ZMod 7)} (hx : x ∈ center SL(2, ZMod 7)) (hne : x ≠ 1) : x = -1 := by
  obtain ⟨a, ha, hax⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  have ha2 : a ^ 2 = 1 := by simpa using ha
  rcases sq_eq_one_iff.mp ha2 with h | h
  · subst a
    apply (hne _).elim
    apply Subtype.ext
    simpa using hax.symm
  · subst a
    apply Subtype.ext
    rw [← hax]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar, hij]

/-- The actual exceptional quotient, including the image of a specified
nonidentity kernel element. The double-cover and base-model premises are
explicit; this theorem does not construct the local subgroup or its action. -/
public theorem linear_marked_sl2Seven_of_two_cover
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (R₀ : Subgroup M) [R₀.Normal] (hR₀ : R₀ ≤ pCore 2 M)
    (hcard : Nat.card ((pCore 2 M).map (QuotientGroup.mk' R₀)) = 2)
    (eB : M ⧸ pCore 2 M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (u : M) (huV : u ∈ pCore 2 M) (huR : u ∉ R₀) :
    ∃ eQ : M ⧸ R₀ ≃* SL(2, ZMod 7), eQ (QuotientGroup.mk' R₀ u) = -1 := by
  let E := M ⧸ R₀
  let K : Subgroup E := (pCore 2 M).map (QuotientGroup.mk' R₀)
  let : K.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective R₀)
  let e : E ⧸ K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    (QuotientGroup.quotientQuotientEquivQuotient R₀ (pCore 2 M) hR₀).trans
      (eB.trans Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm)
  let f : E →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    e.toMonoidHom.comp (QuotientGroup.mk' K)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective K)
  have hfker : f.ker = K := by
    dsimp [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hKcard : Nat.card K = 2 := hcard
  have hK2 : IsPGroup 2 K := IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hKcard)
  have hKcentral : K ≤ center E := central_of_normal_card_two K hcard
  let g := GorensteinWalter.sl2ProjectiveProjection (ZMod 7)
  have hodd : Odd (Nat.card (ZMod 7)) := by norm_num
  have hseven : 3 < Nat.card (ZMod 7) := by norm_num
  obtain ⟨hg, hgc, hgcard, hg2, hperfect, hdih⟩ :=
    GorensteinWalter.sl2_projective_cover_model (ZMod 7) hodd hseven
  let : Group.IsPerfect SL(2, ZMod 7) := hperfect
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) :=
    Group.IsPerfect.ofSurjective (f := g) hg
  let : Group.IsPerfect E := perfect_image_of_twoResidual_of_two_kernel
    (QuotientGroup.mk' R₀) (QuotientGroup.mk'_surjective R₀)
    (r.linear_twoResidual_eq_top h) f hf (by rwa [hfker])
  have hcomm : commutator E = ⊤ := Group.IsPerfect.commutator_eq_top
  have hn : f.ker ⊓ commutator E ≠ ⊥ := by
    rw [hfker, hcomm, inf_top_eq]
    intro hbot
    have hc : Nat.card K = 1 := K.eq_bot_iff_card.mp hbot
    omega
  obtain ⟨eD⟩ := CentralExtension.commutator_mulEquiv_of_central_two_covers
    f g hf hg (by rwa [hfker]) hgc (by rwa [hfker]) hg2 hn hgcard hdih
  let eQ : E ≃* SL(2, ZMod 7) :=
    ((MulEquiv.subgroupCongr hcomm).trans Subgroup.topEquiv).symm.trans eD
  refine ⟨eQ, sl2Seven_center_nonidentity_eq_neg_one ?_ ?_⟩
  · have huK : QuotientGroup.mk' R₀ u ∈ K := mem_map_of_mem _ huV
    exact (Subgroup.centerCongr eQ ⟨_, hKcentral huK⟩).property
  · intro hu
    apply huR
    apply (QuotientGroup.eq_one_iff u).mp
    exact eQ.injective (hu.trans eQ.map_one.symm)

end BenderSuzuki.ZD
