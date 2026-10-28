module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldFixedBlockSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldFixedCardSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldFixedFusionSource
public import Theory.SpecificGroups.SL2.SylowKernelCardinality
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.RootQuotientCoordinatesSource
/-!
# The original fixed Thompson subgroup is Sylow in the fixed block

The fixed counts on R and O₂(H), together with |R/O₂(H)|=2^n, give
|C_R(s)|=2^(n/2)|C_O₂(H)(s)|. The literal fixed-block quotient is
PSL₂(2^(n/2)); its defining-characteristic Sylow has exactly the first
factor's order. Thus a Sylow containing C_R(s) has the same order.
The theorem retains the original ambient embedding in both center branches.
Source: Aschbacher–Smith, 2.4.12(2), 2.4.23(3), printed pp.532,537.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_field_fixed_thompson_sylow
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (s : G) (hs : s ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G))
    (hs2 : orderOf s = 2) :
    let L := d.block.map d.H.subtype
    let Ls := L ⊓ centralizer ({s}:Set G)
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    ∃ P : Sylow 2 Ls, (P:Subgroup Ls).map Ls.subtype=R⊓centralizer ({s}:Set G) := by
  let L := d.block.map d.H.subtype
  let Ls := L ⊓ centralizer ({s}:Set G)
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let Q := twoCore d.H
  let Rs := R⊓centralizer ({s}:Set G)
  let Qs := Q⊓centralizer ({s}:Set G)
  let N := Q.subgroupOf R
  let : N.Normal := source_field_core_normal d
  have hQR : Q≤R := le_sSup (d.core_source hG T hST).2.2
  have hRL : R≤L := (source_core_absorption d hG T hST hsingle hL hM hTM hu).1
  have hRsLs : Rs≤Ls := inf_le_inf hRL le_rfl
  have hQsLs : Qs≤Ls := inf_le_inf (hQR.trans hRL) le_rfl
  obtain ⟨m,hm,hn,hcore,⟨e⟩⟩ := source_field_fixed_block_quotient
    d hG T hST hsingle hL hM hTM hu c s hs hs2
  let F := GaloisField 2 m
  let ef := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let f := ef.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Ls))
  have hf : Function.Surjective f := ef.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker=pCore 2 Ls := by
    ext a
    change ef (QuotientGroup.mk' (pCore 2 Ls) a)=1 ↔ _
    rw [ef.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff a
  have hQs : pCore 2 Ls=Qs.subgroupOf Ls := by
    rw [hcore]
    ext a
    change a.val∈Q ↔ a.val∈Q∧a.val∈centralizer ({s}:Set G)
    exact ⟨fun h=>⟨h,a.property.2⟩,And.left⟩
  have hQc : Nat.card f.ker=Nat.card Qs := by
    rw [hk,hQs]
    exact Nat.card_congr (subgroupOfEquivOfLe hQsLs).toEquiv
  have hRc : Nat.card R=2^n*Nat.card Q := by
    rw [card_eq_card_quotient_mul_card_subgroup N,
      source_root_quotient_card d hG T hST hsingle hL hM hTM hu,
      Nat.card_congr (subgroupOfEquivOfLe hQR).toEquiv]
  have hcR := source_field_thompson_centralizer_card_square d hG T hST hsingle hL hM hTM hu c s hs hs2
  have hcQ := source_field_core_centralizer_card_square d hG T hST hsingle hL hM hTM hu c s hs hs2
  have hcRs : Nat.card Rs=2^m*Nat.card Qs := by
    apply (Nat.pow_left_inj (by decide : 2≠0)).mp
    calc
      Nat.card Rs^2 = Nat.card R := hcR
      _ = 2^n*Nat.card Q := hRc
      _ = (2^m*Nat.card Qs)^2 := by rw [hn, Nat.mul_comm 2 m,pow_mul,mul_pow,hcQ]
  have hRsT : Rs≤(T:Subgroup G) :=
    inf_le_left.trans ((show R≤(d.S:Subgroup d.H).map d.H.subtype from sSup_le fun _ h=>h.1).trans hST.le)
  have hA' : IsPGroup 2 (Rs.subgroupOf Ls) := (T.isPGroup'.to_le hRsT).comap_subtype
  have hcA : Nat.card (Rs.subgroupOf Ls)=Nat.card F*Nat.card f.ker := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRsLs).toEquiv,
      GaloisField.card 2 m hm.ne',hQc]
    exact hcRs
  obtain ⟨P,hP⟩ := Matrix.SpecialLinearGroup.exists_sylow_of_kernel_field_card
    f hf (hk ▸ pCore_isPGroup) (Rs.subgroupOf Ls) hA' hcA
  refine ⟨P,?_⟩
  rw [hP,subgroupOf_map_subtype,inf_eq_left.mpr hRsLs]
end CFSG.Quasithin.Chapter2.LinearShadows.Single
