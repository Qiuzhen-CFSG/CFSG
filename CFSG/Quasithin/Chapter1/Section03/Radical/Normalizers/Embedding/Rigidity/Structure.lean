module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Rigidity.Lifting
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.SolvableRadical.Transport

/-!
# Images inside the solvable radical of an A.3.6 component

The common clauses of A.3.6 put a two-perfect subgroup of the solvable
radical inside the Fitting subgroup: the quotient has order at most two.
The Fitting subgroup has odd order. For a map with two-group kernel,
this identifies the kernel with the intrinsic two-core and gives the actual
quotient-image equivalence. An odd p-group image then lies in O_p by
nilpotence of the Fitting subgroup.

These reductions use the complete A.3.6 common conclusions, without the
additional center–Frattini assertion printed in 1.2.1(4d).
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.6, printed pp.43–45, and proof of 1.3.8, printed p.513.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Rigidity
open Section02
variable {G : Type*} [Group G] [Finite G]


theorem twoPerfect_le_fitting {A : Type*} [Group A] [Finite A]
    (hc : A36Common A) {B : Subgroup A} (hB : IsPPerfect 2 B)
    (hBR : B ≤ solvableRadical A) : B ≤ fittingSubgroup A := by
  rcases hc.2.2.1 with ⟨_, _, hi⟩ | ⟨_, he, _⟩
  · let F := (fittingSubgroup A).subgroupOf (solvableRadical A)
    have hq : IsPGroup 2 (solvableRadical A ⧸ F) := by
      apply IsPGroup.of_card (n := 1)
      exact hi.trans (pow_one 2).symm
    let f : B →* solvableRadical A ⧸ F :=
      (QuotientGroup.mk' F).comp (inclusion hBR)
    have hf := hB.hom_eq_one_of_isPGroup hq f
    intro b hb
    have he : f ⟨b, hb⟩ = 1 := DFunLike.congr_fun hf ⟨b, hb⟩
    exact (QuotientGroup.eq_one_iff (inclusion hBR ⟨b, hb⟩)).mp he
  · exact hBR.trans he.ge

theorem twoCore_eq_bot_of_le_fitting {A : Type*} [Group A] [Finite A]
    (hc : A36Common A) {B : Subgroup A} (hBF : B ≤ fittingSubgroup A) :
    pCore 2 B = ⊥ := by
  have hcard : Nat.Coprime 2 (Nat.card B) := by
    have hf : Nat.Coprime 2 (Nat.card (fittingSubgroup A)) := by
      rw [hc.1]
      exact pPrimeCore_coprime_card
    exact hf.of_dvd_right (card_dvd_of_le hBF)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := B))
  apply disjoint_top.mp
  apply disjoint_of_coprime_natCard
  simpa only [hn, card_top] using hcard.pow_left n

noncomputable def quotientImageEquiv {A : Type*} [Group A] [Finite A]
    (f : G →* A) (hk : IsPGroup 2 f.ker) (himage : pCore 2 f.range = ⊥) :
    (G ⧸ pCore 2 G) ≃* f.range := by
  have he := f.rangeRestrict.comap_pCore_of_ker_isPGroup
    f.rangeRestrict_surjective
    (hk.of_equiv (MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict f)).symm)
  rw [himage, MonoidHom.comap_bot, MonoidHom.ker_rangeRestrict] at he
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivRange f)

theorem quotientImageEquiv_apply_mk {A : Type*} [Group A] [Finite A]
    (f : G →* A) (hk : IsPGroup 2 f.ker) (himage : pCore 2 f.range = ⊥)
    (x : G) : (quotientImageEquiv f hk himage (QuotientGroup.mk' (pCore 2 G) x) : A) =
      f x := by rfl

theorem pSubgroup_le_core {A : Type*} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] {B : Subgroup A}
    (hB : IsPGroup p B) (hBF : B ≤ fittingSubgroup A) : B ≤ pCore p A := by
  have hbf : IsPGroup p (B.subgroupOf (fittingSubgroup A)) := hB.comap_subtype
  obtain ⟨S, hS⟩ := hbf.exists_le_sylow
  have hm : B ≤ (S : Subgroup (fittingSubgroup A)).map (fittingSubgroup A).subtype := by
    simpa only [map_subgroupOf_eq_of_le hBF] using
      map_mono (f := (fittingSubgroup A).subtype) hS
  exact hm.trans (Sylow.map_le_pCore inferInstance inferInstance p S)

theorem radical_image_le_core {A : Type*} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (hc : A36Common A)
    (hG : IsPPerfect 2 G) (hq : XiOddQuotient p (G ⧸ pCore 2 G))
    (f : G →* A) (hk : IsPGroup 2 f.ker) (hR : f.range ≤ solvableRadical A) :
    f.range ≤ pCore p A := by
  have hF := twoPerfect_le_fitting hc
    (hG.of_surjective f.rangeRestrict f.rangeRestrict_surjective) hR
  have hshape := hq.of_mulEquiv (quotientImageEquiv f hk (twoCore_eq_bot_of_le_fitting hc hF))
  exact pSubgroup_le_core hshape.isPGroup hF

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Rigidity
