module
public import Stellmacher.SectionEight.EightSixFullResidual
public import Stellmacher.SectionEight.EightSixInitialThreeSupplement
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexFixedCore
public import Stellmacher.SectionEight.GeneratedEightSixInitialCenterResidual
public import Theory.GroupTheory.CoprimeFullQuotientFixed

/-!
# The initial three-fixed subgroup splits the common intersection

For the equation-one configuration of Stellmacher (8.6), retain the actual
initial three-Sylow subgroup, the initial quotient of type S3, the central
next line, the initial center of order four, and elementary common
intersection D. Then D is the internal direct product of the three-fixed
subgroup of Q and the initial center. No numerical cost hypothesis is used.

The full residual identity Q = [Q,Ea]D and Ea ≤ QT force the three-fixed
subgroup of Q into D. A nontrivial fixed element in the initial center would
trivialize its cubic action, contrary to [Za,Ea] = Za. Coprime decomposition
of elementary D then gives the two complementary factors. This is the
fixed-core step used in the cases of Stellmacher (8.6), printed pp.43–44.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped IsMulCommutative
universe u

public theorem eight_six_fixed_core_splitting
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (D L Q : Subgroup G)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (T : Subgroup G) (hT : IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a)) :
    IsInternalDirectProductTwo D (Q ⊓ Subgroup.centralizer (T : Set G))
      (ZAt ctx.Γ ctx.criticalPath.a) := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let F := EAt Γ cp.a
  let Z := ZAt Γ cp.a
  let C := Q ⊓ Subgroup.centralizer (T : Set G)
  have hcores := eight_six_rigidity_core_containments ctx.sectionSeven Γ cp previous D L Q hD data
  have hDQ : D ≤ Q := hcores.1
  have hZD : Z ≤ D := hcores.2.2.1
  have hZCQ : Z ≤ Subgroup.centralizer (Q : Set G) := hcores.2.2.2
  have hQL : Q ≤ L := hQ ▸ twoCoreIn_le L
  have hQP : Q ≤ P := hQL.trans data.closure_le
  have hDP : D ≤ P := hDQ.trans hQP
  have hZP : Z ≤ P := hZD.trans hDP
  have hFdef : F = twoResidualIn P := Γ.twoResidualAt_def _
  have hFP : F ≤ P := hFdef ▸ twoResidualIn_le P
  obtain ⟨sylow,hsylow⟩ := hT
  have hTP : T ≤ P := hsylow ▸ Subgroup.map_subtype_le _
  have hTthree : IsPGroup 3 T := hsylow ▸ sylow.isPGroup'.map _
  have hTF : T ≤ F := hFdef ▸ eight_six_three_subgroup_le_residual T P hTP hTthree
  have hLN : P ≤ Subgroup.normalizer (L : Set G) := by
    rw [hL]
    exact eight_six_conjugate_closure_normalizer _ _
  have hQn : (Q.subgroupOf P).Normal := by
    rw [hQ]
    exact twoCoreIn_normal_of_normal L P data.closure_le
      (Subgroup.normal_subgroupOf_of_le_normalizer hLN)
  let _ := hQn
  have hDn : (D.subgroupOf P).Normal := data.intersection_normal.2
  let _ := hDn
  have hQtwo : IsPGroup 2 Q := hQ ▸ eight_six_two_core_is_two_group L
  let _ : Fact (IsPGroup 2 Q) := ⟨hQtwo⟩
  have hcommQ : ⁅Q,Q⁆ ≤ D := by
    have hm : (_root_.commutator Q).map Q.subtype = ⁅Q,Q⁆ := by
      rw [_root_.commutator_def,Subgroup.map_commutator,
        ←MonoidHom.range_eq_map,Subgroup.range_subtype]
    rw [←hm]
    exact (Subgroup.map_mono (commutator_le_frattini_of_isPGroup (p := 2))).trans data.core_frattini_le
  have hfull : Q = ⁅Q,F⁆ ⊔ D := eight_six_full_residual ctx previous hprev D L Q hL hQ data
  have hcover : F ≤ Q ⊔ T := eight_six_initial_residual_le_core_sup_three ctx hquot
    previous D L Q T hL hQ ⟨sylow,hsylow⟩ data
  have hfulli : Q.subgroupOf P = ⁅Q.subgroupOf P,F.subgroupOf P⁆ ⊔ D.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hQP,Subgroup.map_subgroupOf_eq_of_le hFP,
      Subgroup.map_subgroupOf_eq_of_le hDP]
    exact hfull
  have hcommi : ⁅Q.subgroupOf P,Q.subgroupOf P⁆ ≤ D.subgroupOf P := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hQP,
      Subgroup.map_subgroupOf_eq_of_le hDP]
    exact hcommQ
  have hcoveri : F.subgroupOf P ≤ Q.subgroupOf P ⊔ T.subgroupOf P := by
    rw [←Subgroup.subgroupOf_sup hQP hTP]
    exact Subgroup.subgroupOf_mono P hcover
  have hfixedi := Subgroup.centralizer_le_layer_of_full_coprime_quotient
    (Q.subgroupOf P) (D.subgroupOf P) (F.subgroupOf P) (T.subgroupOf P)
    (hQtwo.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm)
    (hTthree.of_equiv (Subgroup.subgroupOfEquivOfLe hTP).symm)
    hcommi hfulli hcoveri
  have hCD : C ≤ D := by
    intro c hc
    obtain ⟨hcQ,hcT⟩ := hc
    let cP : P := ⟨c,hQP hcQ⟩
    have hcf : cP ∈ Subgroup.centralizer (T.subgroupOf P : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hcT (t:G) ht
    exact hfixedi ⟨hcQ,hcf⟩
  have hPNZ : P ≤ Subgroup.normalizer (Z : Set G) := stabilizer_le_normalizer_z Γ cp.a
  have hTZ : T ≤ Subgroup.normalizer (Z : Set G) := hTP.trans hPNZ
  let action : T →* MulAut Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hTZ)
  have hZfixed : Z ⊓ Subgroup.centralizer (T : Set G) = ⊥ := by
    apply bot_unique
    intro z hz
    by_contra hzne
    have hzNe : (⟨z,hz.1⟩:Z) ≠ 1 := fun h => hzne (congrArg Subtype.val h)
    have htrivial := three_group_action_four_fixed_imp_trivial hTthree hcard action
      (⟨z,hz.1⟩:Z) hzNe (by
        intro t
        apply Subtype.ext
        change (t:G)*z*(t:G)⁻¹=z
        exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp hz.2 t t.property))
    have hTC : T ≤ Subgroup.centralizer (Z : Set G) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hh := congrArg (fun a : MulAut Z => (a ⟨z,hz⟩ : G)) (htrivial ⟨t,ht⟩)
      change t*z*t⁻¹=z at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hFC : F ≤ Subgroup.centralizer (Z : Set G) := hcover.trans
      (sup_le (Subgroup.le_centralizer_iff.mp hZCQ) hTC)
    have hZcomm : ⁅Z,F⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp hFC)
    rw [eight_six_initial_center_residual_local ctx hcenter hcard] at hZcomm
    have hc : Nat.card Z = 4 := hcard
    change Z = ⊥ at hZcomm
    rw [hZcomm,Subgroup.card_bot] at hc
    omega
  let _ : IsElementaryAbelian 2 D := helementary
  have hDtwo : IsPGroup 2 D := IsElementaryAbelian.isPGroup 2 D
  have hTD : T ≤ Subgroup.normalizer (D : Set G) := hTP.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hDP).mp hDn)
  have hDcomm : ⁅D,T⁆ ≤ Z := by
    have hFres : twoResidualIn L = F :=
      eight_six_equation_one_residual_eq_initial ctx.sectionSeven Γ cp previous D L Q hL data
    have hh : ⁅D,F⁆ = Z := hFres ▸ data.residual_commutator
    exact (Subgroup.commutator_mono le_rfl hTF).trans hh.le
  have hdecomp := Subgroup.eq_commutator_sup_centralizer_of_solvable_coprime D T hTD
    (Group.isSolvable_of_comm fun a b => mul_comm a b)
    (IsPGroup.coprime_card_of_ne 3 2 (by decide) T D hTthree hDtwo)
  have hDCeq : D ⊓ Subgroup.centralizer (T : Set G) = C :=
    le_antisymm (inf_le_inf_right _ hDQ) (le_inf hCD inf_le_right)
  have hsplit : D = C ⊔ Z := by
    apply le_antisymm
    · rw [hdecomp,hDCeq]
      exact sup_le (hDcomm.trans le_sup_right) le_sup_left
    · exact sup_le hCD hZD
  refine ⟨hsplit,?_,?_⟩
  · apply Subgroup.disjoint_def.mpr
    intro x hxC hxZ
    have hx : x ∈ Z ⊓ Subgroup.centralizer (T : Set G) := ⟨hxZ,hxC.2⟩
    simpa only [hZfixed,Subgroup.mem_bot] using hx
  · intro c hc z hz
    exact congrArg (fun d : D => (d:G)) (mul_comm (⟨c,hCD hc⟩:D) ⟨z,hZD hz⟩)
end Stellmacher.SectionEight
