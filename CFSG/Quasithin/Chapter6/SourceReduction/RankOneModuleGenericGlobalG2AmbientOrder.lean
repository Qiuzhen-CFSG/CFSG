module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2CompletionFusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalNormalizerAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialOddNonfusion
public import Theory.GroupTheory.TwoInvolutionClassOrder
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Ambient order comparison for the actual G₂ factor join

Write K = O²(H), J = L ∨ K and M₀ = N_G(L) ∨ N_G(K). The compatible
local maps already supply two marked classes covering the involutions in
S = O₂(N_G(L) ∩ H), separated by ambient nonfusion. Under S = T, Sylow
conjugacy extends this catalogue inside every overgroup of J and in G.
Nonfusion then gives full control of both classes in M₀.

The marked long root lies in Z(K), so its full centralizer is already in
N_G(K). If the designated short-root centralizer is in N_G(L), Thompson's
mixed-pair order formula proves |M₀| = |G|, hence M₀ = G. The source local
conditions make J normal in M₀, and simplicity and its marked involution
then give J = G. This uses the actual subgroups and the same compatible
maps throughout, without assuming a concrete completion isomorphism.

The odd-degree endpoint discharges S = T using the existing field-index
calculation. At even degrees the source transfer argument remains required.
The designated short-root centralizer bound is precisely the remaining
F.4.42 input to this ambient-equality step; it is not asserted here. The
concrete identification of J, exhaustive amalgam comparison and original
uniqueness remain separate duties of the generic-global source assembly.
The Chapter 12 companion applies both the catalogue and the order reduction.

Source: Aschbacher–Smith F.4.38, F.4.40–44, printed pp.294–296, and
5.3.3–4, printed pp.659–660 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem order_of_conj {X : Type*} [Group X] {x y : X}
    (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq x).symm

/-- Sylow conjugacy extends the local two-class catalogue inside every
intermediate group containing the original factor join. -/
private theorem classes_in_overgroup {T : Sylow 2 G} {J : Subgroup G}
    (hTJ : (T : Subgroup G) ≤ J) (z v : J)
    (hc : ∀ x : J, x.val ∈ (T : Subgroup G) → orderOf x = 2 →
      IsConj z x ∨ IsConj v x)
    (M : Subgroup G) (hJM : J ≤ M) (a : M) (ha : orderOf a = 2) :
    IsConj (inclusion hJM z) a ∨ IsConj (inclusion hJM v) a := by
  let U := T.subtype (hTJ.trans hJM)
  obtain ⟨b,hab⟩ := U.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using ha)
  let x : J := ⟨b.val.val,hTJ b.property⟩
  have hx2 : orderOf x = 2 := by
    have hb2 : orderOf (b.val : M) = 2 := (order_of_conj hab).symm.trans ha
    rw [←Subgroup.orderOf_coe] at hb2 ⊢
    exact hb2
  have he : inclusion hJM x = b.val := Subtype.ext rfl
  rcases hc x b.property hx2 with hx | hx
  · exact Or.inl (((inclusion hJM).map_isConj hx).trans (he ▸ hab.symm))
  · exact Or.inr (((inclusion hJM).map_isConj hx).trans (he ▸ hab.symm))

omit [Finite G] in
private theorem fusion_from_two_classes {M : Subgroup G} (z v : M)
    (hz : orderOf z = 2) (hn : ¬ IsConj z.val v.val)
    (hc : ∀ x : M, orderOf x = 2 → IsConj z x ∨ IsConj v x) :
    ∀ x : M, IsConj z x ↔ IsConj z.val x.val := by
  intro x
  refine ⟨M.subtype.map_isConj,?_⟩
  intro hh
  have hx : orderOf x = 2 := by
    rw [←Subgroup.orderOf_coe]
    exact (order_of_conj hh).symm.trans ((Subgroup.orderOf_coe z).trans hz)
  rcases hc x hx with he | he
  · exact he
  · exact (hn (hh.trans (M.subtype.map_isConj he).symm)).elim

/-- Once S is the ambient Sylow subgroup, the two marked G₂ classes cover
all involutions, both in G and inside every overgroup of the actual factor join.
The same compatible maps mark both representatives. -/
theorem Preparation.g2_ambient_involution_classes
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))
    (hST : sourceS L H = (T : Subgroup G)) :
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      ∃ z v : (L ⊔ residual H : Subgroup G),
        z.val = (e.right.symm (G2CompletionFusion.long (1:F))).val ∧
        v.val = (e.right.symm (G2CompletionFusion.short (1:F))).val ∧
        z.val ∈ (center (residual H)).map (residual H).subtype ∧
        orderOf z=2 ∧ orderOf v=2 ∧ ¬ IsConj z.val v.val ∧
        (∀ x : G, orderOf x=2 → IsConj z.val x ∨ IsConj v.val x) ∧
        ∀ M : Subgroup G, ∀ hJM : L ⊔ residual H ≤ M,
          ∀ x : M, orderOf x=2 →
            IsConj (inclusion hJM z) x ∨ IsConj (inclusion hJM v) x := by
  obtain ⟨e,z,v,hz,hv,hzK,hz2,hv2,hn,hclasses⟩ :=
    d.g2_completion_involution_classes h hH hp F he
  have hTJ : (T : Subgroup G) ≤ L ⊔ residual H := by
    rw [←hST]
    exact ((d.g2_local_structure h hH.1.1.2 hp F he).2.2.2.2 1).trans le_sup_right
  have hc : ∀ x : (L ⊔ residual H : Subgroup G),
      x.val ∈ (T : Subgroup G) → orderOf x=2 → IsConj z x ∨ IsConj v x := by
    simpa only [hST] using hclasses
  have hM := classes_in_overgroup hTJ z v hc
  refine ⟨e,z,v,hz,hv,hzK,hz2,hv2,hn,?_,hM⟩
  intro x hx
  let x' : (⊤ : Subgroup G) := ⟨x,mem_top x⟩
  have hx' : orderOf x'=2 := (Subgroup.orderOf_coe x').symm.trans hx
  rcases hM ⊤ le_top x' hx' with hh | hh
  · exact Or.inl ((⊤ : Subgroup G).subtype.map_isConj hh)
  · exact Or.inr ((⊤ : Subgroup G).subtype.map_isConj hh)

/-- Thompson's formula identifies the actual normalizer completion with G
once the designated short-root centralizer is controlled. Simplicity then
identifies the factor join itself with G. Neither equality is assumed. -/
theorem Preparation.g2_ambient_recognition_reduction
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))
    (hST : sourceS L H = (T : Subgroup G)) :
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      let v : G := (e.right.symm (G2CompletionFusion.short (1:F))).val
      orderOf v=2 ∧
      (centralizer ({v} : Set G) ≤ normalizer (L : Set G) →
        normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
        L ⊔ residual H = ⊤) := by
  obtain ⟨e,z,v,hz,hv,hzK,hz2,hv2,hn,hclasses,hMclasses⟩ :=
    d.g2_ambient_involution_classes h hH hp F he hST
  refine ⟨e,?_,?_⟩
  · exact hv ▸ ((Subgroup.orderOf_coe v).trans hv2)
  intro hCv
  rw [←hv] at hCv
  let J := L ⊔ residual H
  let M := normalizer (L : Set G) ⊔ normalizer (residual H : Set G)
  have hJM : J ≤ M := sup_le (L.le_normalizer.trans le_sup_left)
    ((residual H).le_normalizer.trans le_sup_right)
  let zM : M := inclusion hJM z
  let vM : M := inclusion hJM v
  have hzM : orderOf zM=2 := (orderOf_injective (inclusion hJM) (inclusion_injective _) z).trans hz2
  have hvM : orderOf vM=2 := (orderOf_injective (inclusion hJM) (inclusion_injective _) v).trans hv2
  have hMz : ∀ a : M, IsConj zM a ↔ IsConj z.val a.val :=
    fusion_from_two_classes zM vM hzM hn (hMclasses M hJM)
  have hMv : ∀ a : M, IsConj vM a ↔ IsConj v.val a.val :=
    fusion_from_two_classes vM zM hvM (fun hh => hn hh.symm)
      (fun a ha => (hMclasses M hJM a ha).symm)
  have hCz : centralizer ({z.val} : Set G) ≤ M :=
    ((d.g2_central_involution_centralizers h hH hp F he) 1 z.val hzK
      ((Subgroup.orderOf_coe z).trans hz2)).trans le_sup_right
  have hMG : M=⊤ := TwoInvolutionClassOrder.eq_top_of_centralizers_le M z.val v.val
    ((Subgroup.orderOf_coe z).trans hz2) ((Subgroup.orderOf_coe v).trans hv2)
    hn hclasses zM.property vM.property hCz (hCv.trans le_sup_left) hMz hMv
  have hcomp : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) := .g2 F he
  have hlocal := d.normalizer_local_conditions h hH (d.g2_right_maximal_all h hH hp F he) rfl
    (d.common_sylow_of_comparison h hH.1.1.2 hp hcomp)
    (d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp hcomp)
  have hN : J.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp (by
    have hh := normalizer_pair_normalizes hlocal
    change M ≤ normalizer (J : Set G) at hh
    rwa [hMG] at hh))
  let : IsSimpleGroup G := h.qtke.simple
  have hJG : J=⊤ := hN.eq_bot_or_eq_top.resolve_left (by
    intro hbot
    have hz1 : z.val=1 := mem_bot.mp (hbot ▸ z.property)
    have hh : orderOf z.val=2 := (Subgroup.orderOf_coe z).trans hz2
    simp [hz1] at hh)
  exact ⟨hMG,hJG⟩

/-- At odd original degrees the field-index calculation discharges S=T;
only the designated short-root centralizer bound remains for ambient equality. -/
theorem Preparation.g2_ambient_recognition_reduction_of_odd
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (hn : Odd n)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      let v : G := (e.right.symm (G2CompletionFusion.short (1:F))).val
      orderOf v=2 ∧
      (centralizer ({v} : Set G) ≤ normalizer (L : Set G) →
        normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
        L ⊔ residual H = ⊤) :=
  d.g2_ambient_recognition_reduction h hH hp F he
    (d.g2_short_root_not_fused_of_odd h hH hp hn F he).1

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
