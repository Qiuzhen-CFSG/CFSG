module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.PerfectActions
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.CComponent.Radical
public import Theory.SpecificGroups.SL2.ResidualTwoExtension

/-!
# Prime-field cover rigidity for the noncentral Fitting branch

For a perfect group surjecting onto prime-field SL₂(r), cover rigidity
forces the kernel K to equal [K,L]. Consequently every solvable kernel
of such a map is contained in the kernel of any quasisimple image. This
compares the source's different Frattini-action kernels without assuming
that their model primes agree. The same argument proves K = Z(L)N implies
K = N for the literal quotient L/N.

`frattiniCentralizers_eq` applies this comparison to the actual kernels
in A.1.29, with all four combinations of its model alternatives. Proper
normal kernels in a C-component are proved solvable using A.3.3(1).
Only the existing exact `PrimeSL2CoverRigidity` input is explicit; its
unconditional Chapter I discharge belongs to the enclosing source assembly.
These lemmas do not identify the common kernel with the Fitting subgroup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.6, printed pp.43–44, especially the common-kernel argument and (*).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.RankActions
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
universe u

variable {A : Type u} [Group A] [Finite A] [Group.IsPerfect A]

theorem kernel_eq_of_commutator_le
    (hrigid : PrimeSL2CoverRigidity.{u})
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (f : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hf : Function.Surjective f) (N : Subgroup A) [N.Normal]
    (hN : N ≤ f.ker) (hc : ⁅f.ker, (⊤ : Subgroup A)⁆ ≤ N) : f.ker = N := by
  let q := QuotientGroup.mk' N
  let g := QuotientGroup.lift N f hN
  have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective N f hf hN
  have hz : g.ker ≤ center (A ⧸ N) := by
    rw [commutator_top_right_eq_bot_iff_le_center.symm]
    change ⁅(QuotientGroup.lift N f hN).ker, (⊤ : Subgroup (A ⧸ N))⁆ = ⊥
    rw [QuotientGroup.ker_lift, ← map_top_of_surjective q (QuotientGroup.mk'_surjective N),
      ← map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q, QuotientGroup.ker_mk'] using hc)
  exact ((QuotientGroup.injective_lift_iff N f hN).mp
    (hrigid p hp (A ⧸ N) g hg hz)).symm

theorem kernel_eq_commutator
    (hrigid : PrimeSL2CoverRigidity.{u})
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (f : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hf : Function.Surjective f) : f.ker = ⁅f.ker, (⊤ : Subgroup A)⁆ := by
  exact kernel_eq_of_commutator_le hrigid hp f hf _ (commutator_le_left _ _) le_rfl

theorem kernel_eq_of_central_supplement
    (hrigid : PrimeSL2CoverRigidity.{u})
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (f : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hf : Function.Surjective f) (N : Subgroup A) [N.Normal]
    (heq : f.ker = center A ⊔ N) : f.ker = N := by
  apply kernel_eq_of_commutator_le hrigid hp f hf N
  · rw [heq]; exact le_sup_right
  · let q := QuotientGroup.mk' N
    rw [← QuotientGroup.ker_mk' N]
    apply (Subgroup.map_eq_bot_iff _).mp
    rw [map_commutator, map_top_of_surjective q (QuotientGroup.mk'_surjective N)]
    apply commutator_top_right_eq_bot_iff_le_center.mpr
    rw [heq, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
    rintro _ ⟨z, hz, rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact congrArg q (mem_center_iff.mp hz x)

theorem kernel_le_of_solvable_kernel
    (hrigid : PrimeSL2CoverRigidity.{u})
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (f : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    {D : Type*} [Group D] [Finite D] [IsQuasisimple D]
    (g : A →* D) (hg : Function.Surjective g) : f.ker ≤ g.ker := by
  have hcentral : f.ker.map g ≤ center D :=
    (le_solvableRadical _ (Normal.map inferInstance g hg)
      (Group.isSolvable_of_surjective (g.subgroupMap_surjective f.ker))).trans
        IsQuasisimple.solvableRadical_le_center
  have hc : ⁅f.ker, (⊤ : Subgroup A)⁆ ≤ g.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    rw [map_commutator, map_top_of_surjective g hg]
    exact commutator_top_right_eq_bot_iff_le_center.mpr hcentral
  exact (kernel_eq_commutator hrigid hp f hf).le.trans hc

theorem kernels_eq_of_solvable
    (hrigid : PrimeSL2CoverRigidity.{u})
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hp : 3 < p) (hr : 3 < r)
    (f : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (g : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r))
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    [Group.IsSolvable f.ker] [Group.IsSolvable g.ker] : f.ker = g.ker := by
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by simpa only [Nat.card_zmod] using hp) (MulEquiv.refl _)
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by simpa only [Nat.card_zmod] using hr) (MulEquiv.refl _)
  exact le_antisymm (kernel_le_of_solvable_kernel hrigid hp f hf g hg)
    (kernel_le_of_solvable_kernel hrigid hr g hg f hf)

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting

namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
universe u
variable {G : Type u} [Group G] [Finite G] {L : Subgroup G}

theorem solvable_kernel_of_cComponent (hL : L.IsCComponent)
    {D : Type*} [Group D] [Nontrivial D]
    (f : L →* D) (hf : Function.Surjective f) : Group.IsSolvable f.ker := by
  apply hL.isSolvable_of_subnormal_lt_top (inferInstance : f.ker.Normal).isSubnormal
  intro htop
  obtain ⟨x, hx⟩ := exists_ne (1 : D)
  obtain ⟨a, rfl⟩ := hf x
  exact hx (show a ∈ f.ker from htop ▸ mem_top a)

theorem cComponent_SL2_kernels_eq (hrigid : PrimeSL2CoverRigidity.{u})
    (hL : L.IsCComponent)
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hp : 3 < p) (hr : 3 < r)
    (f : L →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (g : L →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r))
    (hf : Function.Surjective f) (hg : Function.Surjective g) : f.ker = g.ker := by
  let : Group.IsPerfect L := hL.perfect
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by simpa only [Nat.card_zmod] using hp) (MulEquiv.refl _)
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by simpa only [Nat.card_zmod] using hr) (MulEquiv.refl _)
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p) ⧸ center _) :=
    IsQuasisimple.simple
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod r) ⧸ center _) :=
    IsQuasisimple.simple
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    (QuotientGroup.mk'_surjective (center _)).nontrivial
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :=
    (QuotientGroup.mk'_surjective (center _)).nontrivial
  let : Group.IsSolvable f.ker := solvable_kernel_of_cComponent hL f hf
  let : Group.IsSolvable g.ker := solvable_kernel_of_cComponent hL g hg
  exact kernels_eq_of_solvable hrigid hp hr f g hf hg

theorem frattiniCentralizers_eq (hrigid : PrimeSL2CoverRigidity.{u})
    (hL : L.IsCComponent) (P Q : Subgroup G) [P.Normal] [Q.Normal]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : Odd p) (hq : Odd q) (hP : IsPGroup p P) (hQ : IsPGroup q Q)
    (hPo : omega₁ P (p := p) = ⊤) (hQo : omega₁ Q (p := q) = ⊤)
    (hPc : _root_.commutator P ≤ center P) (hQc : _root_.commutator Q ≤ center Q)
    (hPr : primeRank p P = 2) (hQr : primeRank q Q = 2)
    (hPL : ⁅P,L⁆ ≠ ⊥) (hQL : ⁅Q,L⁆ ≠ ⊥) :
    frattiniCentralizer P L = frattiniCentralizer Q L := by
  let : Group.IsPerfect L := hL.perfect
  have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨k,hk⟩ := hp; omega
  have hq2 : q ≠ 2 := by rintro rfl; obtain ⟨k,hk⟩ := hq; omega
  have hp3 := three_lt_of_perfect_action P L hp2 hP hPo hPc hPr hPL
  have hq3 := three_lt_of_perfect_action Q L hq2 hQ hQo hQc hQr hQL
  have step {r s : ℕ} [Fact r.Prime] [Fact s.Prime] (hr : 3 < r) (hs : 3 < s)
      (e : (L ⧸ frattiniCentralizer P L) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod r))
      (j : (L ⧸ frattiniCentralizer Q L) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod s)) :
      frattiniCentralizer P L = frattiniCentralizer Q L := by
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (frattiniCentralizer P L))
    let g := j.toMonoidHom.comp (QuotientGroup.mk' (frattiniCentralizer Q L))
    have he := cComponent_SL2_kernels_eq hrigid hL hr hs f g
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
      (j.surjective.comp (QuotientGroup.mk'_surjective _))
    simpa only [f, g, MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,
      MonoidHom.ker_comp_of_injective _ j.toMonoidHom j.injective, QuotientGroup.ker_mk'] using he
  have hPm := CFSG.Quasithin.ChapterA.lemma_A_1_29_1 P L hp hP hPo hPc hPr hPL
  have hQm := CFSG.Quasithin.ChapterA.lemma_A_1_29_1 Q L hq hQ hQo hQc hQr hQL
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rcases hPm with he | ⟨_, he⟩ <;> rcases hQm with hj | ⟨_, hj⟩
  · exact step hp3 hq3 he.some hj.some
  · exact step hp3 (by decide) he.some hj.some
  · exact step (by decide) hq3 he.some hj.some
  · exact step (by decide) (by decide) he.some hj.some

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
