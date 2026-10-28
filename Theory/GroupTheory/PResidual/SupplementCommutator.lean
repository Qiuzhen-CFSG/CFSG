module

public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.Commutator.NormalizesSupplement

/-!
# The residual of a prime-group supplement

If G=RB, R is a p-group and B is p-perfect, then Oᵖ(G)=B[R,B]. The displayed
subgroup is normal with p-group quotient, while B and its commutators lie in
the residual. An embedded version retains the original ambient subgroups.

Source application: the equality O²(N_H(Q₀Q₅))=B₅Q₅ in Aschbacher–Smith
J.4.4(3), printed p.441.
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem pResidual_eq_sup_commutator_of_supplement (R B : Subgroup G)
    (hR : IsPGroup p R) (hB : IsPPerfect p B) (hgen:R⊔B=⊤) :
    pResidual p G=B⊔⁅R,B⁆ := by
  let C := ⁅R,B⁆
  let : C.Normal := normalizer_eq_top_iff.mp (top_unique (hgen ▸
    sup_le (normalizer_commutator_ge_left R B) (normalizer_commutator_ge_right R B)))
  let E := B⊔C
  have hRE : R≤normalizer (E:Set G) :=
    le_normalizer_sup_of_commutator_le B R B C le_rfl (by rw [commutator_comm])
  let : E.Normal := normalizer_eq_top_iff.mp (top_unique (hgen ▸
    sup_le hRE ((show B≤E from le_sup_left).trans E.le_normalizer)))
  have heR : E⊔R=⊤ := by
    apply top_unique
    rw [←hgen]
    exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
  have hBR : B≤pResidual p G := le_pResidual_of_isPPerfect B hB
  apply le_antisymm
  · exact (pResidual_le_iff_isPGroup_quotient p E).mpr
      (isPGroup_quotient_of_sup_eq_top E R hR heR)
  · exact sup_le hBR ((commutator_mono le_rfl hBR).trans (commutator_le_right _ _))

theorem embedded_pResidual_sup_eq_sup_commutator (R B : Subgroup G)
    (hR : IsPGroup p R) (hB : IsPPerfect p B) :
    (pResidual p (R⊔B:Subgroup G)).map (R⊔B).subtype=B⊔⁅R,B⁆ := by
  let J := R⊔B
  have hgen : R.subgroupOf J⊔B.subgroupOf J=⊤ := by
    rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hB' : IsPPerfect p (B.subgroupOf J) :=
    hB.of_surjective (subgroupOfEquivOfLe (show B≤J from le_sup_right)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show B≤J from le_sup_right)).symm.surjective
  have he := congrArg (Subgroup.map J.subtype)
    (pResidual_eq_sup_commutator_of_supplement (R.subgroupOf J) (B.subgroupOf J)
      hR.comap_subtype hB' hgen)
  rw [Subgroup.map_sup,Subgroup.map_commutator,
    map_subgroupOf_eq_of_le (show R≤J from le_sup_left),
    map_subgroupOf_eq_of_le (show B≤J from le_sup_right)] at he
  exact he

end Subgroup
