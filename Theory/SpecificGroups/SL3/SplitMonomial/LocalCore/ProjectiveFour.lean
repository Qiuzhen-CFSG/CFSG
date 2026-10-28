module

public import Theory.SpecificGroups.SL3.SplitMonomial
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Transport of a normal four-subgroup to the projective monomial group

Restrict the actual SL₃-to-PSL₃ projection to the split monomial subgroup
and its published image. Its kernel embeds in the scalar center, so its
order divides three. The projection is therefore injective on a normal
subgroup of order four, and the relative centralizer of its image is the
image of its relative centralizer. Thus an abelian relative centralizer
remains abelian in the projective group.

This transfer retains the linear normal-four witness as an explicit input;
its construction is independent of the quotient argument.

Source: the monomial subgroup in GLS3, Theorem 6.5.3(b),
`refs/KGroup/GLS3/chapter6.tex`, used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, proof of Proposition 1.3.4,
printed p.511 (PDF p.528).
-/

public section

open Subgroup

namespace Matrix.SL3.SplitMonomial

variable (F : Type*) [Field F] [Finite F]

/-- A normal four-subgroup with abelian relative centralizer descends from
the linear monomial group to its actual projective image. -/
theorem projective_normal_four_of_linear
    (hlinear : ∃ V : Subgroup (linear F), V.Normal ∧ Nat.card V = 4 ∧
      IsMulCommutative (centralizer (V : Set (linear F)))) :
    ∃ W : Subgroup (projective F), W.Normal ∧ Nat.card W = 4 ∧
      IsMulCommutative (centralizer (W : Set (projective F))) := by
  obtain ⟨V, hVnormal, hVcard, hVcentralizer⟩ := hlinear
  let := hVnormal
  let := hVcentralizer
  let q : linear F →* projective F := (PSL3.projection F).subgroupMap (linear F)
  have hq : Function.Surjective q :=
    (PSL3.projection F).subgroupMap_surjective (linear F)
  have hkerdvd : Nat.card q.ker ∣ 3 := by
    change Nat.card ((PSL3.projection F).subgroupMap (linear F)).ker ∣ 3
    rw [ker_subgroupMap, PSL3.projection_ker]
    exact ((center (SpecialLinearGroup (Fin 3) F)).card_comap_dvd_of_injective
      (linear F).subtype (linear F).subtype_injective).trans (card_center_dvd_three F)
  have hker : Nat.Coprime 2 (Nat.card q.ker) :=
    Nat.Coprime.of_dvd_right hkerdvd (by decide : Nat.Coprime 2 3)
  have hVtwo : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by simpa using hVcard)
  have hinj : Function.Injective (q.comp V.subtype) :=
    injective_comp_subtype_of_coprime_ker q hker V hVtwo
  let e : V ≃* V.map q := MulEquiv.ofBijective (q.subgroupMap V)
    ⟨fun x y h => hinj (congrArg Subtype.val h), q.subgroupMap_surjective V⟩
  refine ⟨V.map q, hVnormal.map q hq, ?_, ?_⟩
  · exact (Nat.card_congr e.toEquiv).symm.trans hVcard
  · rw [← map_centralizer_eq_of_surjective_coprime q hq hker V hVtwo]
    infer_instance

end Matrix.SL3.SplitMonomial
