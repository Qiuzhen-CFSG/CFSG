module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Family

/-!
# Changing the selected quotient from its normal core to its two-core

Source: Aschbacher–Smith, Proposition 8.2.2(5), printed pp.714–715.
E.2.11(5) identifies the two kernels. The canonical quotient equivalence
commutes with projection, so it transports the same marked Borel. After
the independent E.2.13(6) exclusion, the source family supplies the three
remaining actual models, positivity of k, and divisibility by n(H).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
open Subgroup ChapterE
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G]

/-- The image in the quotient by the intrinsic two-core. -/
def coreImage (I U : Subgroup G) : Subgroup (I ⧸ pCore 2 I) :=
  (U.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))

/-- The canonical equivalence supplied by the E.2.11(5) kernel equality. -/
def coreQuotientEquiv (M I : Subgroup G) (hc : localCore M I = pCore 2 I) :
    Star M I ≃* I ⧸ pCore 2 I := QuotientGroup.quotientMulEquivOfEq hc

theorem coreQuotientEquiv_projection (M I : Subgroup G)
    (hc : localCore M I = pCore 2 I) (i : I) :
    coreQuotientEquiv M I hc (QuotientGroup.mk' (localCore M I) i) =
      QuotientGroup.mk' (pCore 2 I) i :=
  QuotientGroup.quotientMulEquivOfEq_mk hc i

/-- Every specified subgroup image uses the same commuting quotient map. -/
theorem starImage_map_coreQuotientEquiv (M I U : Subgroup G)
    (hc : localCore M I = pCore 2 I) :
    (starImage M I U).map (coreQuotientEquiv M I hc).toMonoidHom = coreImage I U := by
  have he : (coreQuotientEquiv M I hc).toMonoidHom.comp
      (QuotientGroup.mk' (localCore M I)) = QuotientGroup.mk' (pCore 2 I) := by
    ext i
    exact coreQuotientEquiv_projection M I hc i
  rw [starImage, map_map, he, coreImage]

/-- Marked rank-one alternatives transport along an actual equivalence. -/
theorem RankOneAlternative.map {X Y : Type*} [Group X] [Group Y]
    {N : Subgroup X} {k : ℕ} (h : RankOneAlternative X N k) (e : X ≃* Y) :
    RankOneAlternative Y (N.map e.toMonoidHom) k := by
  have cancel {Z : Type} [Group Z] (f : X ≃* Z) :
      (N.map e.toMonoidHom).map (e.symm.trans f).toMonoidHom = N.map f.toMonoidHom := by
    rw [map_map]
    congr 1
    ext x
    simp
  rcases h with ⟨hk, f, hf⟩ | ⟨m, hm, hk, f, hf⟩ | ⟨hk, p, a, hp, ho, ha, ⟨f⟩⟩
  · exact Or.inl ⟨hk, e.symm.trans f, (cancel f).trans hf⟩
  · exact Or.inr (Or.inl ⟨m, hm, hk, e.symm.trans f, (cancel f).trans hf⟩)
  · exact Or.inr (Or.inr ⟨hk, p, a, hp, ho, ha, ⟨e.symm.trans f⟩⟩)

/-- The weaker dihedral formulation used in 8.2.2: its rotation order is
positive and odd. The actual multiplicative equivalences are retained. -/
theorem RankOneAlternative.models {X : Type*} [Group X] {N : Subgroup X} {k : ℕ}
    (h : RankOneAlternative X N k) :
    0 < k ∧
      ((∃ m : ℕ, 0 < m ∧ Odd m ∧ k = 1 ∧ Nonempty (X ≃* DihedralGroup m)) ∨
       (1 < k ∧ Nonempty (X ≃* PSL2 (BinaryGaloisField k))) ∨
       (∃ m : ℕ, 0 < m ∧ k = 2 * m + 1 ∧ Nonempty (X ≃* SuzukiMatrixGroup m))) := by
  rcases h with ⟨hk, e, _⟩ | ⟨m, hm, hk, e, _⟩ | ⟨hk, p, a, hp, ho, _, he⟩
  · exact ⟨by omega, Or.inr (Or.inl ⟨hk, ⟨e⟩⟩)⟩
  · exact ⟨by omega, Or.inr (Or.inr ⟨m, hm, hk, ⟨e⟩⟩)⟩
  · exact ⟨by omega, Or.inl ⟨p ^ a, pow_pos hp.pos a, ho.pow, hk, he⟩⟩

/-- Apply E.2.11(5)'s kernel equality and E.2.13(6)'s exclusion to the
source family. This discharges the quotient-change step of 8.2.2(5),
including its Borel marking; the two earlier source premises remain explicit. -/
theorem selected_quotient [Finite G] {H T M V I : Subgroup G} {k : ℕ}
    (h : Family H T M V I k) (hc : localCore M I = pCore 2 I)
    (hsp : ¬ SymplecticAlternative (Star M H) (Star M I)
      (starImage M I M) (starImage M I T) (starImage M I V) k) :
    0 < k ∧ k ∣ generationParameter H ∧
      RankOneAlternative (I ⧸ pCore 2 I) (coreImage I M) k := by
  have hr := (h.classified.resolve_right hsp).map (coreQuotientEquiv M I hc)
  rw [starImage_map_coreQuotientEquiv] at hr
  exact ⟨hr.models.1, h.parameter_dvd, hr⟩

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
