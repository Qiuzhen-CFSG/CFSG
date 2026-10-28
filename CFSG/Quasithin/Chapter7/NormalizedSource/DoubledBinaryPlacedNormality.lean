module
public import CFSG.Quasithin.Chapter4.Section04.OddActorResidual
public import Theory.GroupTheory.CentralCoverTwoLocalPlacement
public import Theory.GroupTheory.ResidualCentralQuotientImage
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddPlacement
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# The actual maximal two-local in a placed binary-three component

Let R be the original odd fixed residual inside K, with R contained in a
unique maximal two-local M = N_G(L). A two-local of K/Z(K) containing the
image of R lifts into M by lifting its nontrivial two-subgroup through the
full central kernel. Since K is contained in N_G(A), that preimage normalizes
R. Thus the residual image is normal in every such two-local.

The nontrivial moved module makes the image's two-core nontrivial. Its
normalizer is consequently the unique maximal two-local over the image,
and its full preimage is precisely K intersect M. Every original module
normalized by M is normal in that same local. Finally, for the SL3(2)
quotient, an odd component center makes the whole residual map injective:
its central kernel lies in the residual two-core and has odd order.

These are placement and transport results, without a full-Sylow or
component-simplicity assertion. The Chapter12 companion applies them to
the whole marked natural-dual orbit. Source: Aschbacher--Smith 4.4.6--7
and the concluding inspection in 4.4.3, printed pp.620--623,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedNormality
open Chapter4 Chapter4.Section04
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

/-- The full preimage of an actual quotient two-local lies in N_G(L),
and the literal residual image is normal relative to that local. -/
theorem local_preimage_and_normality
    {L A K : Subgroup G} (hKN : K ≤ normalizer (A : Set G))
    (hRK : oddActorResidual L A ≤ K)
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (q : K →* Q) (hq : Function.Surjective q) (hc : q.ker ≤ center K)
    (B : Subgroup Q) (hB : IsTwoLocal B)
    (hRB : (q.comp (inclusion hRK)).range ≤ B) :
    (B.comap q).map K.subtype ≤ normalizer (L : Set G) ∧
      (((q.comp (inclusion hRK)).range).subgroupOf B).Normal := by
  obtain ⟨P,hPne,hP,rfl⟩ := hB
  have hPM := central_preimage_le_of_unique_maximalTwoLocal hRK hu.2.2
    q hq hc (normalizer (P : Set Q)) P hP hPne le_rfl hRB
  exact ⟨hPM,image_normal_in_of_preimage_normalizes hRK q hq _ hRB
    ((le_inf hPM ((map_subtype_le _).trans hKN)).trans (normalizes_oddActorResidual L A))⟩

/-- The moved module makes the residual image local. Its normalizer is
the unique maximal two-local containing that image. -/
theorem residual_image_unique_local
    {L A K W : Subgroup G} (hKN : K ≤ normalizer (A : Set G))
    (hRK : oddActorResidual L A ≤ K)
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hWR : W ≤ (oddActorResidual L A).pCoreIn 2) (hne : W ≠ ⊥)
    (hm : W = ⁅W,oddActorResidual L A⁆) (e : (K ⧸ center K) ≃* Q) :
    let r := residualQuotientMap hRK e
    UniqueMaximalOvergroup r.range (normalizer (r.range : Set Q)) := by
  let r := residualQuotientMap hRK e
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let : Finite Q := Finite.of_surjective q hq
  have hc : q.ker ≤ center K := by
    intro x hx
    exact (QuotientGroup.eq_one_iff x).mp (e.injective (hx.trans e.map_one.symm))
  obtain ⟨hp,hpne,hn⟩ := residualQuotientMap_two_local hRK hWR hne hm e
  have hpX : (pCore 2 (oddActorResidual L A)).map r ≤ r.range := map_le_range _ _
  have hpCore : (pCore 2 (oddActorResidual L A)).map r ≤ r.range.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hp hpX hn
  have hcore : pCore 2 r.range ≠ ⊥ := by
    intro he
    apply hpne
    apply bot_unique
    simpa only [pCoreIn,he,Subgroup.map_bot] using hpCore
  have hlocal := exists_twoLocal_overgroup_normalizer r.range (pCore 2 r.range)
    hcore pCore_isPGroup
  have hnormal (B : Subgroup Q) (hB : IsMaximalTwoLocal B) (hRB : r.range ≤ B) :
      (r.range.subgroupOf B).Normal :=
    (local_preimage_and_normality hKN hRK hu q hq hc B hB.1 hRB).2
  have hmax := (unique_maximalTwoLocal_overgroup_of_normal r.range ⊥ bot_le hlocal
    (fun B hB hRB => hnormal B hB (by simpa only [sup_bot_eq] using hRB))).1
  refine ⟨hmax,r.range.le_normalizer,?_⟩
  intro B hB hRB
  exact hB.eq_of_le hmax.1 ((normal_subgroupOf_iff_le_normalizer hRB).mp (hnormal B hB hRB))

/-- The full inverse image of the selected quotient normalizer is the
literal intersection of the original component with N_G(L). -/
theorem residual_normalizer_preimage
    {L A K W : Subgroup G} (hKN : K ≤ normalizer (A : Set G))
    (hRK : oddActorResidual L A ≤ K)
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hWR : W ≤ (oddActorResidual L A).pCoreIn 2) (hne : W ≠ ⊥)
    (hm : W = ⁅W,oddActorResidual L A⁆) (e : (K ⧸ center K) ≃* Q) :
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let r := residualQuotientMap hRK e
    (normalizer (r.range : Set Q)).comap q = (normalizer (L : Set G)).subgroupOf K := by
  intro q r
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hc : q.ker ≤ center K := by
    intro x hx
    exact (QuotientGroup.eq_one_iff x).mp (e.injective (hx.trans e.map_one.symm))
  have huQ := residual_image_unique_local hKN hRK hu hWR hne hm e
  have hp := (local_preimage_and_normality hKN hRK hu q hq hc
    (normalizer (r.range : Set Q)) huQ.1.1 r.range.le_normalizer).1
  apply le_antisymm
  · intro x hx
    exact hp (mem_map_of_mem K.subtype hx)
  · intro x hx
    have hn : (x : G) ∈ normalizer (oddActorResidual L A : Set G) :=
      normalizes_oddActorResidual L A ⟨hx,hKN x.property⟩
    apply mem_normalizer_iff.mpr
    intro y
    constructor
    · rintro ⟨z,rfl⟩
      have hz := (mem_normalizer_iff.mp hn _).mp z.property
      refine ⟨⟨(x : G) * z * (x : G)⁻¹,hz⟩,?_⟩
      change q (x * inclusion hRK z * x⁻¹) = q x * q (inclusion hRK z) * (q x)⁻¹
      simp only [map_mul,map_inv]
    · intro hy
      obtain ⟨z,hz⟩ := hy
      have hxinv : ((x : G)⁻¹) ∈ normalizer (oddActorResidual L A : Set G) :=
        (normalizer (oddActorResidual L A : Set G)).inv_mem hn
      have hmem := (mem_normalizer_iff.mp hxinv _).mp z.property
      refine ⟨⟨(x : G)⁻¹ * z * ((x : G)⁻¹)⁻¹,hmem⟩,?_⟩
      change q (x⁻¹ * inclusion hRK z * (x⁻¹)⁻¹) = y
      simp only [map_mul,map_inv]
      change (q x)⁻¹ * r z * ((q x)⁻¹)⁻¹ = y
      rw [hz]
      group

/-- The whole original module, mapped by the same quotient, is normal
in every two-local containing the residual image. -/
theorem whole_module_normal_in_local
    {L A K W : Subgroup G} (hKN : K ≤ normalizer (A : Set G))
    (hRK : oddActorResidual L A ≤ K)
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hWR : W ≤ oddActorResidual L A)
    (hMW : normalizer (L : Set G) ≤ normalizer (W : Set G))
    (q : K →* Q) (hq : Function.Surjective q) (hc : q.ker ≤ center K)
    (B : Subgroup Q) (hB : IsTwoLocal B)
    (hRB : (q.comp (inclusion hRK)).range ≤ B) :
    let w := q.comp (inclusion (hWR.trans hRK))
    w.range ≤ B ∧ (w.range.subgroupOf B).Normal := by
  intro w
  have hWB : w.range ≤ B := by
    rintro _ ⟨x,rfl⟩
    exact hRB ⟨inclusion hWR x,rfl⟩
  have hp := (local_preimage_and_normality hKN hRK hu q hq hc B hB hRB).1
  exact ⟨hWB,image_normal_in_of_preimage_normalizes (hWR.trans hRK) q hq B hWB
    (hp.trans hMW)⟩

/-- An odd full center kills no part of an embedded binary-three
covering residual. The containing component need not be centerless. -/
theorem central_quotient_injective
    {R C : Type*} [Group R] [Finite R] [Group C] [Finite C]
    (e : (R ⧸ pCore 2 R) ≃* BinaryLinearThree.Group)
    (i : R →* C) (hi : Function.Injective i) (ho : Odd (Nat.card (center C))) :
    Function.Injective ((QuotientGroup.mk' (center C)).comp i) := by
  let π := QuotientGroup.mk' (center C)
  have hk := DoubledBinaryOddPlacement.central_kernel_le_twoCore e i hi
  have hodd : Nat.Coprime 2 (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    exact ho.coprime_two_left
  let P := (pCore 2 R).map i
  have hp := injective_comp_subtype_of_coprime_ker π hodd P (pCore_isPGroup.map i)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hxP : i x ∈ P := mem_map_of_mem i (hk hx)
  have he : (⟨i x,hxP⟩ : P) = 1 := hp (by
    change π (i x) = π 1
    exact hx.trans π.map_one.symm)
  exact hi ((congrArg Subtype.val he).trans i.map_one.symm)

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedNormality
