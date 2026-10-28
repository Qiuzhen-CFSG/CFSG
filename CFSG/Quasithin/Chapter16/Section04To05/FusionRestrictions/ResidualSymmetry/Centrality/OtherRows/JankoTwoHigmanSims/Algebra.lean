module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.Marking
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Inner
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.HigmanSims.CoreNormalOrders
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.HigmanSims.ProductNormalOrders
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.HigmanSims.ElementaryResidual
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Residual sizes and perfectness for the J₂ and HS rows

A two-perfect extension of a perfect group by a two-group is perfect:
its abelianization is a two-group and hence trivial. This proves perfectness
for the table residuals and for their full central covers.

The actual central HS residual has order at least 3840 by the existing
normal-subgroup calculation. For J₂ a residual of order at most 120 would
be a perfect central extension of A₅ with kernel of order at most two,
hence a component. The checked self-centralizing normal two-kernel excludes
this. The noncentral product residuals have orders 60 and 360, respectively;
the elementary outer HS residual has order dividing 960.

These are intrinsic inputs to Aschbacher–Smith 16.5.6(4), printed p.1197,
using the literal rows 16.1.5(8),(10), p.1172. Perfectness and the J₂ order
gap are deductions, not additional table conclusions. No central kernel
or extension action is discarded.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.JankoTwoHigmanSims
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open SylowSymmetry.ReverseDelta.Comparison
open SylowSymmetry.ReverseDelta.Comparison.OtherFamilies

private theorem perfect_of_twoPerfect {C D : Type*} [Group C] [Group D] [Group.IsPerfect D]
    (f : C →* D) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hC : IsPPerfect 2 C) : Group.IsPerfect C := by
  have hm : (commutator C).map f = ⊤ := by
    rw [commutator_def, map_commutator, map_top_of_surjective _ hf]
    exact Group.IsPerfect.commutator_eq_top
  have hs : commutator C ⊔ f.ker = ⊤ := by
    rw [← comap_map_eq, hm, comap_top]
  exact ⟨hC (commutator C) inferInstance
    (isPGroup_quotient_of_sup_eq_top _ _ hk hs)⟩

private theorem residual_perfect_of_two_kernel {C D : Type*} [Group C] [Finite C]
    [Group D] [Group.IsPerfect (pResidual 2 D)]
    (f : C →* D) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    Group.IsPerfect (pResidual 2 C) := by
  let R := pResidual 2 C
  have hm : R.map f = pResidual 2 D := map_pResidual_of_surjective 2 f hf
  let : Group.IsPerfect (R.map f) := by rw [hm]; infer_instance
  have he : (f.subgroupMap R).ker = f.ker.subgroupOf R := by
    ext x
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    rfl
  apply perfect_of_twoPerfect (f.subgroupMap R) (f.subgroupMap_surjective R)
    ?_ (isPPerfect_pResidual 2)
  rw [he]
  exact hk.comap_subtype

/-- A perfect model residual lifts to the full residual through its own central two-kernel. -/
theorem full_residual_perfect {G S : Type*} [Group G] [Finite G] [Group S]
    {L : Subgroup G} [IsQuasisimple L] (hodd : pPrimeCore 2 L = ⊥)
    (e : (L ⧸ center L) ≃* S) (u : normalizer (L : Set G))
    [Group.IsPerfect (pResidual 2 (MulAut.centralQuotientAction e
      (L.normalizerMonoidHom u)).fixedSubgroup)] :
    Group.IsPerfect (involutionTwoResidual L u.val) := by
  let hXL := (SylowSymmetry.ReverseDelta.residual_le L u.val).trans inf_le_left
  let f := centralImageMap hXL
  let em := centralImageModelEquiv hodd e u.property
  let : Group.IsPerfect (SylowSymmetry.ReverseDelta.centralImage L (SylowSymmetry.ReverseDelta.residual L u.val)) :=
    Group.IsPerfect.ofSurjective (f := em.symm.toMonoidHom) em.symm.surjective
  change Group.IsPerfect (SylowSymmetry.ReverseDelta.residual L u.val)
  exact perfect_of_twoPerfect (D := SylowSymmetry.ReverseDelta.centralImage L (SylowSymmetry.ReverseDelta.residual L u.val)) f (centralImageMap_surjective hXL)
    (centralImageMap_two_kernel hodd hXL) (isPPerfect_embedded_pResidual 2 _)

/-- The two-residual of the literal HS core extension is perfect; this is deduced from the extension. -/
theorem hs_core_residual_perfect {C : Type*} [Group C] [Finite C]
    (h : IsHSCoreExtension C) : Group.IsPerfect (pResidual 2 C) := by
  obtain ⟨Q, hQ, hs, ⟨e⟩⟩ := h
  let := hQ
  let f : C →* S5 := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hk : f.ker = Q := by
    ext x
    change e (QuotientGroup.mk' Q x) = 1 ↔ x ∈ Q
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let : Group.IsPerfect A5 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (pResidual 2 S5) := by
    rw [Equiv.Perm.twoResidual_eq_alternating]
    infer_instance
  apply residual_perfect_of_two_kernel f hf
  rw [hk]
  apply IsPGroup.of_card (n := 6)
  exact HSInner.shape_card hs

/-- The actual central HS row has two-residual order at least 3840. -/
theorem hs_core_residual_large [IsSimpleGroup Sporadic.LeechRelated.HS.Carrier]
    [Group.IsPerfect Sporadic.LeechRelated.HS.Carrier]
    (a : MulAut Sporadic.LeechRelated.HS.Carrier) (ha : orderOf a = 2)
    (hi : ∃ x, a = MulAut.conj x) (hc : IsHSCoreExtension a.fixedSubgroup) :
    3840 ≤ Nat.card (pResidual 2 a.fixedSubgroup) := by
  have hns : ¬ Group.IsSolvable (pResidual 2 a.fixedSubgroup) := by
    obtain ⟨Q, hQ, _, ⟨e⟩⟩ := hc
    let := hQ
    let f := e.toMonoidHom.comp (QuotientGroup.mk' Q)
    have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective Q)
    have hm : (pResidual 2 a.fixedSubgroup).map f = alternatingGroup (Fin 5) := by
      rw [map_pResidual_of_surjective 2 f hf, Equiv.Perm.twoResidual_eq_alternating]
    intro hs
    let := hs
    have hsA := Group.isSolvable_of_surjective (f.subgroupMap_surjective (pResidual 2 a.fixedSubgroup))
    rw [hm] at hsA
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable _ hsA
  have hd := hs_core_residual_normal_card_dvd a ha hi hc ⊤ inferInstance (by
    intro hs
    let := hs
    exact hns (Group.isSolvable_of_surjective
      (f := (topEquiv : (⊤ : Subgroup (pResidual 2 a.fixedSubgroup)) ≃* _).toMonoidHom)
      topEquiv.surjective))
  rw [card_top] at hd
  exact Nat.le_of_dvd Nat.card_pos hd


private theorem quaternion_dihedral_card {Q : Type*} [Group Q] [Finite Q]
    (h : IsQuaternionDihedralProduct Q) : Nat.card Q = 32 := by
  obtain ⟨B, D, ⟨eB⟩, ⟨eD⟩, hi, hc, hs⟩ := h
  have hB : Nat.card B = 8 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hD : Nat.card D = 8 := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
  have hn : D ≤ normalizer (B : Set Q) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro d hd b hb
    exact hc b hb d hd
  have he := card_mul_eq_card_inf_mul_card_sup_of_normalizes B D hn
  rw [hB, hD, hi, hs, card_top] at he
  omega

/-- The embedded quaternion-dihedral kernel and A₅ quotient give the full centralizer order 1920. -/
theorem j2_core_card {C : Type*} [Group C] [Finite C]
    (h : IsJ2CoreExtension C) : Nat.card C = 1920 := by
  obtain ⟨Q, hQ, hs, ⟨e⟩⟩ := h
  let := hQ
  rw [card_eq_card_quotient_mul_card_subgroup Q, Nat.card_congr e.toEquiv,
    quaternion_dihedral_card hs]
  change Nat.card (alternatingGroup (Fin 5)) * 32 = 1920
  rw [nat_card_alternatingGroup]
  norm_num

private theorem perfect_twoPerfect {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] : IsPPerfect 2 H := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (H ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (H ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)

/-- The two-residual of the literal J₂ core extension is perfect. -/
theorem j2_core_residual_perfect {C : Type*} [Group C] [Finite C]
    (h : IsJ2CoreExtension C) : Group.IsPerfect (pResidual 2 C) := by
  obtain ⟨Q, hQ, hs, ⟨e⟩⟩ := h
  let := hQ
  let f : C →* A5 := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hk : f.ker = Q := by
    ext x
    change e (QuotientGroup.mk' Q x) = 1 ↔ x ∈ Q
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let : Group.IsPerfect A5 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (pResidual 2 A5) := by
    rw [(pResidual_eq_top_iff 2 A5).mpr perfect_twoPerfect]
    infer_instance
  apply residual_perfect_of_two_kernel f hf
  rw [hk]
  apply IsPGroup.of_card (n := 5)
  exact quaternion_dihedral_card hs


private noncomputable def botProdEquiv {H K : Type*} [Group H] [Group K]
    (N : Subgroup K) : (⊥ : Subgroup H).prod N ≃* N where
  toFun x := ⟨x.val.2, x.property.2⟩
  invFun x := ⟨(1, x), ⟨rfl, x.property⟩⟩
  left_inv x := Subtype.ext (Prod.ext (mem_bot.mp x.property.1).symm rfl)
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The noncentral inner J₂ fixed group has order 240. -/
theorem j2_product_card : Nat.card (E4 × A5) = 240 := by
  change Nat.card ((Fin 2 → Multiplicative (ZMod 2)) × alternatingGroup (Fin 5)) = 240
  rw [Nat.card_prod, nat_card_alternatingGroup]
  norm_num

/-- The two-residual of E₄ × A₅ is the actual A₅ factor. -/
noncomputable def j2ProductResidualEquiv : pResidual 2 (E4 × A5) ≃* A5 := by
  let N := (⊥ : Subgroup E4).prod (⊤ : Subgroup A5)
  let e : N ≃* A5 := (botProdEquiv (⊤ : Subgroup A5)).trans topEquiv
  let : Group.IsPerfect A5 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect N := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hp : IsPGroup 2 ((E4 × A5) ⧸ N) := by
    apply IsPGroup.of_card (n := 2)
    have hA : Nat.card A5 = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have hn : Nat.card N = 60 := (Nat.card_congr e.toEquiv).trans hA
    have hi := N.card_mul_index
    rw [hn, j2_product_card] at hi
    rw [← index_eq_card]
    omega
  exact (MulEquiv.subgroupCongr
    (pResidual_eq_of_isPPerfect N perfect_twoPerfect hp)).trans e

/-- An actual noncentral J₂ row equivalence gives residual order 60. -/
theorem j2_product_residual_card {C : Type*} [Group C]
    (e : C ≃* E4 × A5) : Nat.card (pResidual 2 C) = 60 := by
  let er := (e.subgroupMap (pResidual 2 C)).trans
    ((MulEquiv.subgroupCongr (map_pResidual 2 e)).trans j2ProductResidualEquiv)
  rw [Nat.card_congr er.toEquiv]
  change Nat.card (alternatingGroup (Fin 5)) = 60
  rw [nat_card_alternatingGroup]
  norm_num

/-- A self-centralizing normal two-kernel excludes residual orders at most 120: such a residual would be a component. -/
theorem j2_core_residual_large {C : Type*} [Group C] [Finite C]
    (hc : IsJ2CoreExtension C) (hself : HasSelfCentralizingNormalTwoSubgroup C) :
    120 < Nat.card (pResidual 2 C) := by
  let R := pResidual 2 C
  let : Group.IsPerfect R := j2_core_residual_perfect hc
  obtain ⟨Q, hQ, _, ⟨e⟩⟩ := hc
  let := hQ
  let f : C →* A5 := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective Q)
  let : Group.IsPerfect A5 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hm : R.map f = ⊤ := by
    rw [map_pResidual_of_surjective 2 f hf, (pResidual_eq_top_iff 2 A5).mpr perfect_twoPerfect]
  let g : R →* A5 := f.comp R.subtype
  have hg : Function.Surjective g := by
    apply MonoidHom.range_eq_top.mp
    simpa only [g, MonoidHom.range_comp, range_subtype] using hm
  by_contra! hsmall
  have hkcard : Nat.card g.ker ≤ 2 := by
    have he : Nat.card g.ker * 60 = Nat.card R := by
      have hq : g.ker.index = 60 := by
        rw [index_eq_card,
          Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv]
        change Nat.card (alternatingGroup (Fin 5)) = 60
        rw [nat_card_alternatingGroup]
        norm_num
      simpa only [hq] using g.ker.card_mul_index
    have hsmall' : Nat.card R ≤ 120 := hsmall
    rw [← he] at hsmall'
    omega
  have hkcentral : g.ker ≤ center R := by
    rcases (show Nat.card g.ker = 1 ∨ Nat.card g.ker = 2 from by
      have hp := Nat.card_pos (α := g.ker)
      omega) with hk | hk
    · rw [card_eq_one.mp hk]
      exact bot_le
    · exact central_of_normal_card_two g.ker hk
  have hker : g.ker = center R := by
    apply le_antisymm hkcentral
    intro x hx
    have hz : g x ∈ center A5 := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := hg y
      simpa only [map_mul] using congrArg g (mem_center_iff.mp hx y)
    rw [alternatingGroup.center_eq_bot (by simp)] at hz
    exact hz
  let : IsQuasisimple R := {
    toIsPerfect := inferInstance
    simple := by
      let : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective g hg)).isSimpleGroup }
  exact hself.not_isComponent R
    ⟨(inferInstance : R.Normal).isSubnormal, inferInstance⟩

/-- The proved kernel action in the actual central J₂ class supplies the strict order bound. -/
theorem j2_inner_core_residual_large
    (a : MulAut Sporadic.LeechRelated.J2.Carrier) (ha : orderOf a = 2)
    (hi : ∃ x, a = MulAut.conj x) (hc : IsJ2CoreExtension a.fixedSubgroup) :
    120 < Nat.card (pResidual 2 a.fixedSubgroup) := by
  rcases J2Inner.inner_structure a ha hi with hs | hp
  · exact j2_core_residual_large hc hs.2
  · obtain ⟨ep⟩ := hp
    have hh := j2_core_card hc
    rw [Nat.card_congr ep.toEquiv, j2_product_card] at hh
    norm_num at hh

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.JankoTwoHigmanSims
