module
public import Theory.GroupTheory.PResidual.CyclicImageCentralKernel
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaResidualStar
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaResidualImage

/-!
# The cyclic Omega residual has its original two-core kernel

In the order-three branch, the actual Y is the two-residual of the
M-normal closure of Rc. On M/O₂(M), Rc centralizes the action kernel by
15.2.3(5). The cyclic-image transfer lemma therefore makes the literal
starred residual act faithfully on V. Source normality identifies its
intrinsic two-core and gives C_Y(V)=O₂(Y), together with |Y*|=3.

No isomorphism or centralizer/core equality is a premise. The full
Sylow-three product description in 15.2.3(1)(iii) is a separate source
conclusion.

Source: Aschbacher--Smith, 15.2.3(1), printed p.1105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem residual_notation {D : Type*} [Group D] [Finite D] (H : Subgroup D) :
    twoResidualAmbient H = (pResidual 2 H).map H.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN,n,hn⟩
    exact ⟨hN,IsPGroup.of_card hn⟩
  · rintro ⟨hN,hp⟩
    exact ⟨hN,IsPGroup.iff_card.mp hp⟩

omit [Finite G] in
private theorem omega_core_le_kernel {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn)) :
    pCore 2 M ≤ (actionHom M V hn).ker := by
  let f := (actionHom M V hn).rangeRestrict
  have hcore : pCore 2 M ≤ f.ker := by
    let e := ho.2.2.2.1.some
    have hn : ((pCore 2 M).map (e.toMonoidHom.comp f)).Normal :=
      Normal.map inferInstance _ (e.surjective.comp (actionHom M V hn).rangeRestrict_surjective)
    have hp : (pCore 2 M).map (e.toMonoidHom.comp f) ≤
        pCore 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
      le_sSup ⟨hn,pCore_isPGroup.map _⟩
    rw [SymmetricThreeProduct.twoCore_eq_bot] at hp
    intro x hx
    exact e.injective ((Subgroup.mem_bot.mp (hp (mem_map_of_mem _ hx))).trans e.map_one.symm)
  simpa only [f,MonoidHom.ker_rangeRestrict] using hcore

/-- In the cubic-image branch, the original residual action kernel lies in O₂(M). -/
theorem source_omega_cyclic_kernel_le_core (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 3) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    Y.subgroupOf M ⊓ (actionHom M V hV.normalized).ker ≤ pCore 2 M := by
  let f := (actionHom M V hV.normalized).rangeRestrict
  let q := QuotientGroup.mk' (pCore 2 M)
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let R := ((M ⊓ Mc).pCoreIn 2).subgroupOf M
  have hcore : pCore 2 M ≤ f.ker := by
    simpa only [f,MonoidHom.ker_rangeRestrict] using omega_core_le_kernel hV.normalized ho
  let g := QuotientGroup.lift (pCore 2 M) f hcore
  have hcomp : g.comp q = f := rfl
  have hker : g.ker = f.ker.map q := QuotientGroup.ker_lift _ _ _
  have hCeq : (M ⊓ centralizer (V : Set G)).subgroupOf M = f.ker := by
    rw [show f = (actionHom M V hV.normalized).rangeRestrict from rfl,
      MonoidHom.ker_rangeRestrict,actionHom_ker]
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
  have hcentral : R.map q ≤ centralizer (g.ker : Set (M ⧸ pCore 2 M)) := by
    rw [hker,← hCeq]
    exact le_sup_left.trans (source_omega_lemma_15_2_3_5 T hTM hu hV ho)
  have hY : (Y.subgroupOf M).map q =
      (pResidual 2 (normalClosure (R.map q : Set (M ⧸ pCore 2 M)))).map
        (normalClosure (R.map q : Set (M ⧸ pCore 2 M))).subtype := by
    rw [source_omega_caseIIResidual_image T hTM hV.normalized ho q
      (QuotientGroup.mk'_surjective _),residual_notation]
  have hR : IsPGroup 2 (R.map q) := (isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype.map q
  have hcyclic : IsCyclic (((Y.subgroupOf M).map q).map g) := by
    rw [map_map,hcomp]
    exact isCyclic_of_prime_card hcard
  have hfaithful : Disjoint ((Y.subgroupOf M).map q) g.ker := by
    rw [hY] at hcyclic ⊢
    let := hcyclic
    exact disjoint_twoResidual_normalClosure_ker_of_cyclic_image g (R.map q) hR hcentral
  change Y.subgroupOf M ⊓ (actionHom M V hV.normalized).ker ≤ pCore 2 M
  intro x hx
  have hz : q x = 1 := disjoint_def.mp hfaithful (mem_map_of_mem q hx.1)
    (show q x ∈ g.ker from (show f x = 1 from Subtype.ext hx.2))
  exact (QuotientGroup.eq_one_iff x).mp hz
/-- The literal source residual satisfies C_Y(V)=O₂(Y) in the cubic-image branch. -/
theorem source_omega_cyclic_kernel_eq_core (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 3) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    Y ⊓ centralizer (V : Set G) = Y.pCoreIn 2 := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let A := Y.subgroupOf M
  have hYM : Y ≤ M := by
    dsimp only [Y]
    rw [source_omega_caseIIResidual_eq T hTM hV.normalized ho]
    exact (map_subtype_le _).trans
      (conjugateSpanBy_le_self ((pCoreIn_le 2 _).trans inf_le_left))
  let : A.Normal := source_omega_lemma_15_2_3_2 T hTM hV.normalized ho
  have hAcore := pCore_subnormal_eq_comap 2 (inferInstance : A.Normal).isSubnormal
  have hbound := source_omega_cyclic_kernel_le_core T hTM hu hV ho hcard
  have hEq : A ⊓ (actionHom M V hV.normalized).ker = A.pCoreIn 2 := by
    apply le_antisymm
    · intro x hx
      refine ⟨⟨x,hx.1⟩,?_,rfl⟩
      rw [hAcore]
      exact hbound hx
    · exact le_inf (pCoreIn_le 2 A)
        ((pCoreIn_le_of_subnormal 2 (inferInstance : A.Normal).isSubnormal).trans
          (omega_core_le_kernel hV.normalized ho))
  have hh := congrArg (Subgroup.map M.subtype) hEq
  rw [map_inf _ _ _ M.subtype_injective,
    map_pCoreIn_of_injective 2 A M.subtype M.subtype_injective,
    show A.map M.subtype = Y from map_subgroupOf_eq_of_le hYM,
    actionHom_ker,subgroupOf_map_subtype] at hh
  change Y ⊓ centralizer (V : Set G) = Y.pCoreIn 2
  simpa only [← inf_assoc,inf_eq_left.mpr ((inf_le_left : Y ⊓ centralizer (V : Set G) ≤ Y).trans hYM)] using hh

/-- The literal residual image in M/O₂(M) has order three. -/
theorem source_omega_cyclic_star_card (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 3) :
    Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (QuotientGroup.mk' (pCore 2 M))) = 3 := by
  let A := (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M
  let f := (actionHom M V hV.normalized).rangeRestrict
  let q := QuotientGroup.mk' (pCore 2 M)
  have hbound := source_omega_cyclic_kernel_le_core T hTM hu hV ho hcard
  have hcore := omega_core_le_kernel hV.normalized ho
  have he : A ⊓ f.ker = A ⊓ pCore 2 M := by
    rw [show f = (actionHom M V hV.normalized).rangeRestrict from rfl,
      MonoidHom.ker_rangeRestrict]
    exact le_antisymm (le_inf inf_le_left hbound) (inf_le_inf_left A hcore)
  have hc : Nat.card (A.map q) = Nat.card (A.map f) := by
    rw [← relIndex_ker,← relIndex_ker]
    rw [show q.ker = pCore 2 M from QuotientGroup.ker_mk' _]
    rw [← inf_relIndex_left A (pCore 2 M),← inf_relIndex_left A f.ker,he]
  exact hc.trans hcard

end CFSG.Quasithin.Chapter15.Section02
