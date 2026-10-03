module
public import Theory.GroupTheory.Commutator.ConjugateGeneratorProduct
public import Stellmacher.SectionEight.EightFourPredecessorStarCore
public import Stellmacher.SectionEight.EightFourStarPredecessorModuleCentralization

/-!
# Source (7): centralization of the original fixed-center closure

Retain the actual local Section Eight context, faithful quotient witness, and
nontrivial fixed-closure branch. Let C be the actual equivariant star family,
with its original first-step closure and its bounds in the neighbor modules.
In the first extracted configuration, a subgroup D of the transported star
whose commutator with A lies in the endpoint center centralizes the original
first-step star. The source subgroup D inside the transported edge-fixed
family is a special case of this result.

The predecessor star lies in the initial core, so it centralizes A. Its
conjugate therefore centralizes A^x. Quotient the terminal stabilizer by its
normal center module: the image of D commutes with both generators of L0,
hence with x. The conjugate-generator product theorem puts D in the
predecessor star joined with the endpoint center. Both lie in the
predecessor's neighbor module, which the initial star centralizes by the
proved local critical-pair geometry. The canonical public statement remains
an exact wrapper on the same graph. No new quotient witness, selected-factor
identification, or second-configuration alternative is needed.

The private subtype transfer applies the intrinsic product theorem inside the
literal terminal stabilizer, without requiring D to lie in L0. Source:
Stellmacher (8.4)(7), Journal of Algebra190 (1997), printed p39, the sentence
following the definition of D in `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem conjugate_subgroupOf_map
    {G : Type*} [Group G] (P A : Subgroup G) (hAP : A ≤ P) (x : P) :
    ((A.subgroupOf P).conjBy x).map P.subtype = A.conjBy (x : G) := by
  change ((A.subgroupOf P).map (MulAut.conj x).toMonoidHom).map P.subtype = _
  rw [Subgroup.map_map]
  have heq : P.subtype.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj (x : G)).toMonoidHom.comp P.subtype := by ext t; rfl
  rw [heq, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hAP]
  rfl

private theorem relative_conjugate_generator_product
    {G : Type*} [Group G] (P D Y A Z : Subgroup G)
    (hDP : D ≤ P) (hYP : Y ≤ P) (hAP : A ≤ P) (hZP : Z ≤ P)
    (hZn : (Z.subgroupOf P).Normal)
    (x : G) (hxP : x ∈ P) (hDY : D ≤ Y) (hDA : ⁅D,A⁆ ≤ Z)
    (hDAx : ⁅D,A.conjBy x⁆ = ⊥) (hx : x ∈ A ⊔ A.conjBy x) :
    D ≤ Y.conjBy x⁻¹ ⊔ Z := by
  let xP : P := ⟨x,hxP⟩
  let _ : (Z.subgroupOf P).Normal := hZn
  have hDAp : ⁅D.subgroupOf P,A.subgroupOf P⁆ ≤ Z.subgroupOf P := by
    intro t ht
    have hm := Subgroup.mem_map_of_mem P.subtype ht
    rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hDP,
      Subgroup.map_subgroupOf_eq_of_le hAP] at hm
    exact hDA hm
  have hDAxp : ⁅D.subgroupOf P,(A.subgroupOf P).conjBy xP⁆ = ⊥ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hDP,
      conjugate_subgroupOf_map P A hAP xP,Subgroup.map_bot]
    exact hDAx
  have hxp : xP ∈ A.subgroupOf P ⊔ (A.subgroupOf P).conjBy xP := by
    apply (Subgroup.mem_map_iff_mem P.subtype_injective).mp
    rw [Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le hAP,
      conjugate_subgroupOf_map P A hAP xP]
    exact hx
  have hprod := Subgroup.le_conjBy_inv_sup_of_commutator_conjugate_generators
    (D.subgroupOf P) (Y.subgroupOf P) (A.subgroupOf P) (Z.subgroupOf P) xP
    (fun _ hd => hDY hd) hDAp hDAxp hxp
  have hm := Subgroup.map_mono hprod (f := P.subtype)
  rw [Subgroup.map_subgroupOf_eq_of_le hDP,Subgroup.map_sup,
    conjugate_subgroupOf_map P Y hYP xP⁻¹,
    Subgroup.map_subgroupOf_eq_of_le hZP] at hm
  exact hm



/-- Source (7): the selected subgroup centralizes the original first-step star. -/
public theorem eight_four_star_fixed_centralization_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (C : ctx.Γ.Vertex → Subgroup H)
    (hC : ∀ g d, C (ctx.Γ.act g d) = (C d).conjBy g⁻¹)
    (hbase : C ctx.criticalPath.firstStep = (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype)
    (hCV : ∀ d, C d ≤ VAt ctx.Γ d)
    (A L0 D : Subgroup H) (x : H)
    (hA : A ≤ ZAt ctx.Γ ctx.criticalPath.a)
    (hL0 : L0 ≤ GAt ctx.Γ ctx.criticalPath.a')
    (hgen : L0 = A ⊔ A.conjBy x) (hx : x ∈ L0)
    (hD : D ≤ C (ctx.Γ.act x⁻¹
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-1,by omega⟩)))
    (hDA : ⁅D,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a') :
    ⁅D,C ctx.criticalPath.firstStep⁆ = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let prev := cp.path ⟨cp.length-1,by omega⟩
  let next := Γ.act x⁻¹ prev
  let P := GAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  have hpos := cp.length_pos
  have hprevadj : Γ.adjacent cp.a' prev := by
    have he := cp.path_adj ⟨cp.length-1,by omega⟩
    have hi : (⟨cp.length-1,by omega⟩ : Fin cp.length).succ =
        ⟨cp.length,Nat.lt_succ_self _⟩ := by apply Fin.ext; dsimp; omega
    rw [hi,cp.path_end] at he
    exact Γ.adjacent_symm he
  have hprev := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hprevadj
  have hfirst := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hxP : x ∈ P := hL0 hx
  have hfix : Γ.act x⁻¹ cp.a' = cp.a' := by
    have hh := P.inv_mem hxP
    change x⁻¹ ∈ (Γ.vertexStabilizer cp.a' : Set H) at hh
    rw [Γ.stabilizer_def] at hh
    exact hh
  have hnextadj : Γ.adjacent cp.a' next := by
    have hh := adjacent_act Γ x⁻¹ hprevadj
    rwa [hfix] at hh
  have hnext := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hnextadj)
  have hYp : C next ≤ P :=
    (hCV next).trans ((SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp
      (eight_four_centered_length_gt_one_local ctx hcenter) next).trans
        ((lemma_seven_three h Γ).sylow_and_core next cp.a' hnext default).2.2)
  have hQp : QAt Γ cp.a' ≤ P := by
    rw [show QAt Γ cp.a' = twoCoreIn P from Γ.twoCoreAt_def cp.a']
    exact Subgroup.map_subtype_le _
  have hZP : Z ≤ P := ((lemma_seven_three h Γ).center_core cp.a' prev hprev).trans
    ((Subgroup.map_subtype_le _).trans hQp)
  have hZn : (Z.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZP).mpr (stabilizer_le_normalizer_z Γ cp.a')
  have hAP : A ≤ P := (show A ≤ L0 by rw [hgen]; exact le_sup_left).trans hL0
  have hprevCore : C prev ≤ QAt Γ cp.a :=
    eight_four_predecessor_star_le_initial_core_local ctx hcenter w hbranch C hC hbase
  have hQaA : QAt Γ cp.a ≤ Subgroup.centralizer (A : Set H) := by
    apply Subgroup.le_centralizer_iff.mpr
    exact hA.trans (((lemma_seven_three h Γ).center_core cp.a cp.firstStep hfirst).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (SevenSix.centerAmbient_le_centralizer _)))
  have hprevA : ⁅C prev,A⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hprevCore.trans hQaA)
  have hnextEq : C next = (C prev).conjBy x := by
    simpa only [next,inv_inv] using hC x⁻¹ prev
  have hnextAx : ⁅C next,A.conjBy x⁆ = ⊥ := by
    have hm := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hprevA
    rw [Subgroup.map_commutator,Subgroup.map_bot] at hm
    rw [hnextEq]
    exact hm
  have hDAx : ⁅D,A.conjBy x⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono hD le_rfl).trans_eq hnextAx)
  have hprod := relative_conjugate_generator_product P D (C next) A Z
    (hD.trans hYp) hYp hAP hZP hZn x hxP hD hDA hDAx (by rwa [← hgen])
  rw [hnextEq,Subgroup.conjBy_inv] at hprod
  have hZV : Z ≤ VAt Γ prev := by
    change Z ≤ v Γ prev
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨cp.a',(SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm hprevadj),rfl⟩
  have hDV : D ≤ VAt Γ prev := hprod.trans (sup_le (hCV prev) hZV)
  have hstar := eight_four_star_centralizes_predecessor_module_local
    ctx hcenter w hbranch C hC hbase (hCV cp.firstStep)
  rw [Subgroup.commutator_comm]
  exact le_bot_iff.mp ((Subgroup.commutator_mono le_rfl hDV).trans_eq hstar)


/-- Canonical-context wrapper with the original witness, subgroup and conjugator. -/
public theorem eight_four_star_fixed_centralization
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (C : ctx.Γ.Vertex → Subgroup H)
    (hC : ∀ g d, C (ctx.Γ.act g d) = (C d).conjBy g⁻¹)
    (hbase : C ctx.criticalPath.firstStep = (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype)
    (hCV : ∀ d, C d ≤ VAt ctx.Γ d)
    (A L0 D : Subgroup H) (x : H)
    (hA : A ≤ ZAt ctx.Γ ctx.criticalPath.a)
    (hL0 : L0 ≤ GAt ctx.Γ ctx.criticalPath.a')
    (hgen : L0 = A ⊔ A.conjBy x) (hx : x ∈ L0)
    (hD : D ≤ C (ctx.Γ.act x⁻¹
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-1,by omega⟩)))
    (hDA : ⁅D,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a') :
    ⁅D,C ctx.criticalPath.firstStep⁆ = ⊥ := by
  exact eight_four_star_fixed_centralization_local
    ctx.toLocalContext hcenter w hbranch C hC hbase hCV A L0 D x hA hL0 hgen hx hD hDA

end Stellmacher.SectionEight
