module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The full solvable branch of B.6.8

Apply the solvable primitive-group theorem to `H/O₂(H)`. Subgroup
correspondence preserves the unique maximal overgroup of the image of `T`
and identifies its normal core with the literal image of `J`.
The resulting odd-prime two-residual is exactly the prime core. Its
Frattini subgroup is `J̄`. Transporting the residual through
`H/O₂(H) → H/J` identifies the prime core of the star quotient and retains
the actual irreducible conjugation action of the mapped Sylow subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.6.8(2), printed pp.113–114. The two-group quotient by the prime core
states `H = O₂,p,₂(H)` using the literal successive quotients.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterB
open Subgroup
variable {H : Type*} [Group H] [Finite H]

private theorem stellmacher_residual_eq (G : Type*) [Group G] [Finite G] :
    Stellmacher.twoResidualAmbient (⊤ : Subgroup G) = pResidual 2 G := by
  rw [Stellmacher.SectionThree.twoResidualAmbient_top_eq_hktPResidual]
  apply le_antisymm
  · exact BenderSuzuki.External.hktPResidual_le _ inferInstance
      (Subgroup.isPGroup_quotient_pResidual 2)
  · exact sInf_le ⟨BenderSuzuki.External.hktPResidual_normal,
      BenderSuzuki.External.hktPResidual_quotient_isPGroup⟩

private theorem residual_eq_pCore {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : IsPGroup p (pResidual 2 G)) : pResidual 2 G = pCore p G := by
  refine le_antisymm ?_ ?_
  · exact le_sSup ⟨inferInstance, hp⟩
  intro x hx
  apply mem_pResidual_of_orderOf_coprime
  have hc := (pCore_isPGroup (G := G) (p := p)).orderOf_coprime
    (Nat.coprime_two_right.mpr ho) (⟨x, hx⟩ : pCore p G)
  rw [← Subgroup.orderOf_coe] at hc
  exact hc.symm

omit [Finite H] in
/-- The unique maximal overgroup and its normal core after factoring out `O₂(H)`. -/
theorem minimalParabolic_quotient_maximal_geometry (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) :
    let q := QuotientGroup.mk' (pCore 2 H)
    let B := (minimalParabolicMax T hP).map q
    IsCoatom B ∧ (T : Subgroup H).map q ≤ B ∧
      (∀ L : Subgroup (H ⧸ pCore 2 H), IsCoatom L → (T : Subgroup H).map q ≤ L → L = B) ∧
      B.normalCore = minimalParabolicCoreImage T hP := by
  let M := minimalParabolicMax T hP
  let J := minimalParabolicCore T hP
  let Q := pCore 2 H
  let q := QuotientGroup.mk' Q
  let B := M.map q
  have hq := QuotientGroup.mk'_surjective Q
  have hQM : Q ≤ M := (minimalParabolicTwoCore_le_core T hP).trans (normalCore_le _)
  have hBpre : B.comap q = M := by
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hQM]
  have hB : IsCoatom B := by
    refine ⟨?_, ?_⟩
    · intro htop
      apply (minimalParabolicMax_spec T hP).1.ne_top
      change M = ⊤
      rw [← hBpre, htop, comap_top]
    · intro L hBL
      have hML : M < L.comap q := by
        rw [← hBpre]
        exact lt_of_le_of_ne (comap_mono hBL.le)
          (fun he => hBL.ne (comap_injective hq he))
      have htop := (minimalParabolicMax_spec T hP).1.2 _ hML
      apply comap_injective hq
      simpa using htop
  have huniq : ∀ L : Subgroup (H ⧸ Q), IsCoatom L → (T : Subgroup H).map q ≤ L → L = B := by
    intro L hL hTL
    apply comap_injective hq
    rw [hBpre]
    exact minimalParabolicMax_unique T hP (isCoatom_comap_of_surjective hq hL)
      (map_le_iff_le_comap.mp hTL)
  refine ⟨hB, map_mono (minimalParabolicMax_spec T hP).2, huniq, ?_⟩
  let : (J.map q).Normal := (inferInstance : J.Normal).map q hq
  apply le_antisymm
  · have hpre : B.normalCore.comap q ≤ J := by
      apply normal_le_normalCore.mpr
      change B.normalCore.comap q ≤ M
      rw [← hBpre]
      exact comap_mono (normalCore_le B)
    rw [← map_comap_eq_self_of_surjective hq B.normalCore]
    exact map_mono hpre
  · exact normal_le_normalCore.mpr (map_mono (normalCore_le M))

private theorem solvable_quotient_data (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p (pResidual 2 (H ⧸ pCore 2 H)) ∧
      minimalParabolicCoreImage T hP =
        Stellmacher.frattiniAmbient (pResidual 2 (H ⧸ pCore 2 H)) := by
  let Q := pCore 2 H
  let q := QuotientGroup.mk' Q
  have hq := QuotientGroup.mk'_surjective Q
  obtain ⟨hB, hTB, hu, hJ⟩ := minimalParabolic_quotient_maximal_geometry T hP
  have hcore : pCore 2 (H ⧸ Q) = ⊥ := by
    rw [← pCore_map_mk'_eq_of_normal_isPGroup (p := 2) Q (pCore_isPGroup (G := H) (p := 2))]
    exact (map_eq_bot_iff (f := q) (H := Q)).mpr (by simp [q])
  obtain ⟨p, hp, ho, hr, hPhi, _⟩ :=
    Stellmacher.SectionThree.solvable_primitive_two_local ((T : Subgroup H).map q)
      ((minimalParabolicMax T hP).map q) (T.mapSurjective hq) rfl hB hTB hu hcore
      (inferInstance : Group.IsSolvable (H ⧸ Q))
  rw [stellmacher_residual_eq] at hr hPhi
  exact ⟨p, hp, ho, hr, hJ ▸ hPhi⟩

/-- All assertions of B.6.8(2), with residual/prime-core identifications in
both source quotients and the mapped Sylow action in `H/J`. -/
theorem minimalParabolic_solvable_structure (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      pResidual 2 (H ⧸ pCore 2 H) = pCore p (H ⧸ pCore 2 H) ∧
      IsPGroup 2 ((H ⧸ pCore 2 H) ⧸ pCore p (H ⧸ pCore 2 H)) ∧
      minimalParabolicCoreImage T hP = Stellmacher.frattiniAmbient (pCore p (H ⧸ pCore 2 H)) ∧
      pResidual 2 (minimalParabolicStarQuotient T hP) =
        pCore p (minimalParabolicStarQuotient T hP) ∧
      Stellmacher.IsIrreducibleSection (minimalParabolicStarSylow T hP) ⊥
        (pCore p (minimalParabolicStarQuotient T hP)) := by
  obtain ⟨p, hp, ho, hr, hPhi⟩ := solvable_quotient_data T hP hs
  let : Fact p.Prime := ⟨hp⟩
  have hR := residual_eq_pCore ho hr
  let J := minimalParabolicCore T hP
  let Q := pCore 2 H
  let q := QuotientGroup.mk' Q
  let qJ := QuotientGroup.mk' J
  have hQker : Q ≤ qJ.ker := by
    rw [QuotientGroup.ker_mk']
    exact minimalParabolicTwoCore_le_core T hP
  let f : (H ⧸ Q) →* (H ⧸ J) := QuotientGroup.lift Q qJ hQker
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective J y
    exact ⟨q x, rfl⟩
  have hrstar : IsPGroup p (pResidual 2 (H ⧸ J)) := by
    rw [← map_pResidual_of_surjective 2 f hf]
    exact hr.map f
  have hRstar : pResidual 2 (minimalParabolicStarQuotient T hP) =
      pCore p (minimalParabolicStarQuotient T hP) := residual_eq_pCore ho hrstar
  obtain ⟨_, _, _, _, hir, _⟩ := minimalParabolic_solvable_star_structure T hP hs
  refine ⟨p, hp, ho, hR, ?_, ?_, hRstar, ?_⟩
  · exact (pResidual_le_iff_isPGroup_quotient 2 _).mp hR.le
  · simpa only [hR] using hPhi
  · simpa only [hRstar] using hir

end CFSG.Quasithin.ChapterB
end
end
