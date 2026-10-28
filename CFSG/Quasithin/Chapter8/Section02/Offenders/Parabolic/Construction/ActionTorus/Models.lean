module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.ActionTorus.Source

/-!
# The precise model centralizers used by the torus lift

Source: Aschbacher–Smith, E.2.11(2–3), E.2.14(2,9), printed pp.224–227,
and Proposition 8.2.2(6,8), printed pp.714–715.

The remaining matrix-model inputs concern only the centralizer of a Sylow
center inside the named PSL₂ or Suzuki Borel. They imply that the kernel
of the original V-action is a two-group, via the marked quotient. The
transport keeps the actual equivalence, mapped Sylow subgroup and center.
The final adapter takes the already constructed markings in I/O₂(I) and
moves them back to I* using the canonical quotient equivalence.

`RankOneBorelCenterModels` is an explicit pair of model propositions, not
a theorem or a classification tag. The source assembly must supply them;
no orders, simplicity or representation theory of unrelated models is needed.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Subgroup
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
open ChapterE BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups

/-- Only the two Borel centralizer facts used to control the action kernel. -/
def RankOneBorelCenterModels : Prop :=
  (∀ (k : ℕ), 1 < k → ∀ (S : Sylow 2 (PSL2 (BinaryGaloisField k))),
    (S : Subgroup (PSL2 (BinaryGaloisField k))) ≤ PBorel (BinaryGaloisField k) →
    IsPGroup 2 ↥(PBorel (BinaryGaloisField k) ⊓ centralizer (embeddedCenter (S : Subgroup (PSL2 (BinaryGaloisField k))) : Set (PSL2 (BinaryGaloisField k))))) ∧
  (∀ (m : ℕ), 0 < m → ∀ (S : Sylow 2 (SuzukiMatrixGroup m)),
    (S : Subgroup (SuzukiMatrixGroup m)) ≤ SuzukiBorelSubgroup m →
    IsPGroup 2 ↥(SuzukiBorelSubgroup m ⊓ centralizer (embeddedCenter (S : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m))))

private theorem embeddedCenter_map {X Y : Type*} [Group X] [Group Y]
    (S : Subgroup X) (e : X ≃* Y) :
    (embeddedCenter S).map e.toMonoidHom = embeddedCenter (S.map e.toMonoidHom) := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨⟨e z, mem_map_of_mem _ z.property⟩, mem_center_iff.mpr ?_, rfl⟩
    rintro ⟨_, s, hs, rfl⟩
    apply Subtype.ext
    exact (map_mul e _ _).symm.trans
      ((congrArg e (congrArg Subtype.val (mem_center_iff.mp hz ⟨s, hs⟩))).trans (map_mul e _ _))
  · rintro _ ⟨⟨_, z, hz, rfl⟩, hc, rfl⟩
    refine ⟨z, ⟨⟨z, hz⟩, mem_center_iff.mpr ?_, rfl⟩, rfl⟩
    intro s
    apply Subtype.ext
    apply e.injective
    change e (s.val * z) = e (z * s.val)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val
      (mem_center_iff.mp hc ⟨e s, mem_map_of_mem _ s.property⟩)

private theorem borel_center_two_transport {X Y : Type*} [Group X] [Group Y]
    (N : Subgroup X) (S : Sylow 2 X) (e : X ≃* Y) (B : Subgroup Y)
    (hB : N.map e.toMonoidHom = B)
    (hC : IsPGroup 2 ↥(B ⊓ centralizer (embeddedCenter
      ((S : Subgroup X).map e.toMonoidHom) : Set Y))) :
    IsPGroup 2 ↥(N ⊓ centralizer (embeddedCenter (S : Subgroup X) : Set X)) := by
  apply (hC.comap_of_injective e.toMonoidHom e.injective).to_le
  intro x hx
  refine ⟨hB ▸ mem_map_of_mem e.toMonoidHom hx.1, ?_⟩
  rw [← embeddedCenter_map]
  rintro _ ⟨z, hz, rfl⟩
  change e z * e x = e x * e z
  rw [← map_mul, ← map_mul]
  exact congrArg e (hx.2 z hz)

theorem selected_borel_center_two {G : Type*} [Group G] [Finite G]
    (models : RankOneBorelCenterModels) (M I V : Subgroup G) (k : ℕ) (hk : 1 < k)
    (hr : RankOneAlternative (Star M I) (starImage M I M) k)
    (S : Sylow 2 (Star M I)) (hSM : (S : Subgroup _) ≤ starImage M I M)
    (hV : starImage M I V = embeddedCenter (S : Subgroup _)) :
    IsPGroup 2 ↥(starImage M I M ⊓ centralizer (starImage M I V : Set (Star M I))) := by
  rw [hV]
  rcases hr with ⟨hpos, e, hB⟩ | ⟨m, hm, hk', e, hB⟩ | ⟨hk1, _⟩
  · apply borel_center_two_transport _ S e _ hB
    have hm := models.1 k hpos (S.mapSurjective (f := e.toMonoidHom) e.surjective) (by
      rw [Sylow.coe_mapSurjective]
      exact hB ▸ map_mono hSM)
    simpa only [Sylow.coe_mapSurjective] using hm
  · apply borel_center_two_transport _ S e _ hB
    have hm' := models.2 m hm (S.mapSurjective (f := e.toMonoidHom) e.surjective) (by
      rw [Sylow.coe_mapSurjective]
      exact hB ▸ map_mono hSM)
    simpa only [Sylow.coe_mapSurjective] using hm'
  · omega

/-- Recover the required star-quotient centralizer bound from the exact
Sylow and center marking already supplied in I/O₂(I). -/
theorem selected_borel_center_two_of_core_markings {G : Type*} [Group G] [Finite G]
    (models : RankOneBorelCenterModels) (M I V T : Subgroup G) (k : ℕ) (hk : 1 < k)
    (hc : localCore M I = pCore 2 I)
    (hr : RankOneAlternative (Star M I) (starImage M I M) k)
    (S : Sylow 2 I) (hS : (S : Subgroup I) = T.subgroupOf I)
    (hSM : (S : Subgroup I) ≤ M.subgroupOf I)
    (hV : coreImage I V = embeddedCenter (coreImage I T)) :
    IsPGroup 2 ↥(starImage M I M ⊓ centralizer (starImage M I V : Set (Star M I))) := by
  let Sstar := S.mapSurjective (QuotientGroup.mk'_surjective (localCore M I))
  have hSS : (Sstar : Subgroup (Star M I)) = starImage M I T := by
    rw [Sylow.coe_mapSurjective, hS]
    rfl
  apply selected_borel_center_two models M I V k hk hr Sstar
  · exact map_mono hSM
  · apply map_injective (f := (coreQuotientEquiv M I hc).toMonoidHom)
      (coreQuotientEquiv M I hc).injective
    rw [starImage_map_coreQuotientEquiv, embeddedCenter_map, hSS,
      starImage_map_coreQuotientEquiv, hV]

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
