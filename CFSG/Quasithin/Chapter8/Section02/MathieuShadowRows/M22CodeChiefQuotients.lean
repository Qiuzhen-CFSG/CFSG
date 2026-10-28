module
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.WreathTwoSylowMaximal
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreQuotient
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.MaximalSylow
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Solvable
public import Theory.GroupTheory.SylowCoprimeEquivalence

/-!
# Normal-core and Sylow quotients from a wreath image

A surjection from a minimal parabolic onto the binary-plane wreath group
has exactly the original maximal-overgroup normal core as its kernel.
Indeed the image Sylow is maximal, so its maximal-overgroup core is the
trivial two-core.  The Sylow intersection with the original core is
O₂(H); restricting the same map therefore identifies the literal Sylow
quotient with the dihedral group of order eight.

The M22-code application uses a constructed chief image.  This identifies
the normal-core quotient, without replacing that core by O₂(H). In the
solvable branch, B.6.8 makes the two-residual modulo O₂(H) an odd prime
core. Its image is the wreath group’s elementary subgroup of order nine,
so that prime is three; the subsequent quotient is the same D₈.
Source: Aschbacher–Smith, B.6.8 and the argument in 8.2.2(1), printed
pp.113–114 and 715, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open ChapterB

theorem wreath_parabolic_kernel
    {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (hp : IsMinimalParabolicOver S ⊤)
    (f : H →* WreathTwoResidual.Actor) (hf : Function.Surjective f) :
    f.ker = minimalParabolicCore S hp := by
  let : Nontrivial WreathTwoResidual.Actor := wreathTwoDihedralHom_injective.nontrivial
  have hn : f.ker ≠ ⊤ := by
    intro ht
    have hh := congrArg (Subgroup.map f) ht
    rw [map_ker_self,map_top_of_surjective f hf] at hh
    exact bot_ne_top hh
  obtain ⟨hk,hp'⟩ := minimalParabolic_reduced_image S hp f hf WreathTwoResidual.twoCore_eq_bot hn
  have hc := minimalParabolicCore_map_core S hp f hf hk
  rw [minimalParabolicCore_eq_twoCore_of_sylow_isCoatom (S.mapSurjective hf)
    (minimalParabolic_surjective_core S hp f hf hk)
    (wreath_two_sylow_isCoatom (S.mapSurjective hf)),WreathTwoResidual.twoCore_eq_bot] at hc
  exact le_antisymm hk ((Subgroup.map_eq_bot_iff _).mp hc)

theorem wreath_parabolic_quotients
    {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (hp : IsMinimalParabolicOver S ⊤)
    (f : H →* WreathTwoResidual.Actor) (hf : Function.Surjective f) :
    Nonempty ((H ⧸ minimalParabolicCore S hp) ≃* WreathTwoResidual.Actor) ∧
      Nonempty ((S ⧸ (pCore 2 H).subgroupOf (S : Subgroup H)) ≃* DihedralGroup 4) := by
  have hk := wreath_parabolic_kernel S hp f hf
  have hs : (f.subgroupMap (S : Subgroup H)).ker = (pCore 2 H).subgroupOf (S : Subgroup H) := by
    rw [ker_subgroupMap,hk,←inf_subgroupOf_left (minimalParabolicCore S hp) (S : Subgroup H),
      minimalParabolic_sylow_inf_core S hp]
  obtain ⟨a⟩ := wreath_two_sylow_mulEquiv_dihedral_four (S.mapSurjective hf)
  exact ⟨⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩,
    ⟨((QuotientGroup.quotientMulEquivOfEq hs.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (f.subgroupMap (S : Subgroup H))
      (f.subgroupMap_surjective _))).trans a⟩⟩

/-- The solvable branch retains the full three-core after quotienting by
O₂(H), and its subsequent quotient is the original Sylow quotient D₈. -/
theorem solvable_wreath_parabolic_residual
    {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (hp : IsMinimalParabolicOver S ⊤) (hs : Group.IsSolvable H)
    (f : H →* WreathTwoResidual.Actor) (hf : Function.Surjective f) :
    pResidual 2 (H ⧸ pCore 2 H) = pCore 3 (H ⧸ pCore 2 H) ∧
      Nonempty (((H ⧸ pCore 2 H) ⧸ pCore 3 (H ⧸ pCore 2 H)) ≃* DihedralGroup 4) := by
  let Q := H ⧸ pCore 2 H
  let q := QuotientGroup.mk' (pCore 2 H)
  have hq := QuotientGroup.mk'_surjective (pCore 2 H)
  have hker : pCore 2 H ≤ f.ker := by
    rw [wreath_parabolic_kernel S hp f hf]
    exact minimalParabolicTwoCore_le_core S hp
  let g : Q →* WreathTwoResidual.Actor := QuotientGroup.lift (pCore 2 H) f hker
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨q x,rfl⟩
  obtain ⟨p,hp',ho,hR,hQ,_⟩ := minimalParabolic_solvable_structure S hp hs
  let : Fact p.Prime := ⟨hp'⟩
  have hRP : IsPGroup p (pResidual 2 WreathTwoResidual.Actor) := by
    rw [←map_pResidual_of_surjective 2 g hg,hR]
    exact pCore_isPGroup.map g
  obtain ⟨e₉⟩ := WreathTwoResidual.residual_equiv_elementaryNine
  have hc : Nat.card (pResidual 2 WreathTwoResidual.Actor) = 9 := by
    rw [Nat.card_congr e₉.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have he : p = 3 := by
    rcases hRP.card_eq_or_dvd with h1 | hd
    · omega
    have hd3 : p ∣ 3 := hp'.dvd_of_dvd_pow
      (show p ∣ 3^2 from hd.trans (by rw [hc]; norm_num))
    rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with he | he
    · exact (hp'.ne_one he).elim
    · exact he
  subst p
  refine ⟨hR,?_⟩
  let R := S.mapSurjective hq
  have hsq : (q.subgroupMap (S : Subgroup H)).ker = (pCore 2 H).subgroupOf (S : Subgroup H) := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
  let eS : (S ⧸ (pCore 2 H).subgroupOf (S : Subgroup H)) ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq hsq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap (S : Subgroup H))
        (q.subgroupMap_surjective _))
  obtain ⟨eD⟩ := (wreath_parabolic_quotients S hp f hf).2
  let q₃ := QuotientGroup.mk' (pCore 3 Q)
  have hq₃ := QuotientGroup.mk'_surjective (pCore 3 Q)
  have hc₃ : Nat.Coprime 2 (Nat.card q₃.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup : IsPGroup 3 (pCore 3 Q)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  let R₃ := R.mapSurjective hq₃
  have htop : (R₃ : Subgroup (Q ⧸ pCore 3 Q)) = ⊤ :=
    (R₃.is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  let eR : R ≃* (Q ⧸ pCore 3 Q) :=
    (Sylow.equivOfSurjectiveCoprime q₃ hq₃ hc₃ R R₃).trans
      ((MulEquiv.subgroupCongr htop).trans topEquiv)
  exact ⟨eR.symm.trans (eS.symm.trans eD)⟩


end CFSG.Quasithin.Chapter8.MathieuShadowRows
