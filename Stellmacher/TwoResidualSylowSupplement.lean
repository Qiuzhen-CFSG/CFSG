module

public import Stellmacher.SectionsOneToFourDefs
public import BenderSuzuki.External.Huppert.IV.Residual

/-!
# The 2-residual and a Sylow supplement

In a finite group, the 2-residual together with any Sylow 2-subgroup
generates the whole group.  This is standard residual infrastructure used in
the local-to-global passage of Stellmacher (2.4), Journal of Algebra 190
(1997), p. 20.

The explicit Section 2 notation defines the residual as an intersection of
normal subgroups of 2-power index.  We first identify that definition with
Huppert's residual, whose quotient is a 2-group.  The image of a Sylow
2-subgroup is then Sylow in that quotient and hence is the whole quotient;
pulling the equality back gives the stated generation result.  The
identification is kept private so this module exposes only the stable
supplement theorem required by callers.
-/

open BenderSuzuki.External

namespace Stellmacher

universe u

private theorem twoResidualAmbient_top_eq_hktPResidual_low
    {G : Type u} [Group G] [Finite G] :
    twoResidualAmbient (⊤ : Subgroup G) = hktPResidual 2 G := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · let R : Subgroup G := hktPResidual 2 G
    have hRnormal : R.Normal := hktPResidual_normal
    let _ : R.Normal := hRnormal
    have hRquot : IsPGroup 2 (G ⧸ R) := hktPResidual_quotient_isPGroup
    let Rtop : Subgroup (⊤ : Subgroup G) := R.subgroupOf ⊤
    have hRtopNormal : Rtop.Normal := hRnormal.subgroupOf ⊤
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hRquot
    have hRtopIndex : Rtop.index = 2 ^ n := by
      calc
        Rtop.index = R.relIndex ⊤ := rfl
        _ = R.index := Subgroup.relIndex_top_right R
        _ = Nat.card (G ⧸ R) := Subgroup.index_eq_card R
        _ = 2 ^ n := hn
    have hRtop_mem : Rtop ∈
        {N : Subgroup (⊤ : Subgroup G) |
          N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n} :=
      ⟨hRtopNormal, n, hRtopIndex⟩
    have hsInf_le : twoResidualSubgroup (⊤ : Subgroup G) ≤ Rtop :=
      sInf_le hRtop_mem
    calc
      twoResidualAmbient (⊤ : Subgroup G) =
          (twoResidualSubgroup (⊤ : Subgroup G)).map
            (⊤ : Subgroup G).subtype := rfl
      _ ≤ Rtop.map (⊤ : Subgroup G).subtype := Subgroup.map_mono hsInf_le
      _ = R := Subgroup.map_subgroupOf_eq_of_le le_top
      _ = hktPResidual 2 G := rfl
  · intro x hx
    change x ∈ (twoResidualSubgroup (⊤ : Subgroup G)).map
      (⊤ : Subgroup G).subtype
    refine ⟨⟨x, by simp⟩, ?_, rfl⟩
    change (⟨x, by simp⟩ : (⊤ : Subgroup G)) ∈ sInf
      {N : Subgroup (⊤ : Subgroup G) |
        N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n}
    rw [Subgroup.mem_sInf]
    intro R hR
    let N : Subgroup G := R.map (⊤ : Subgroup G).subtype
    have hNnormal : N.Normal :=
      hR.1.map (⊤ : Subgroup G).subtype (fun y => ⟨⟨y, by simp⟩, rfl⟩)
    let _ : N.Normal := hNnormal
    obtain ⟨n, hn⟩ := hR.2
    have hN_eq : N.subgroupOf (⊤ : Subgroup G) = R := by
      apply Subgroup.map_injective_of_ker_le
        (f := (⊤ : Subgroup G).subtype)
        (H := N.subgroupOf ⊤) (K := R)
      · simp
      · simp
      · simp [N]
    have hNindex : N.index = 2 ^ n := by
      calc
        N.index = N.relIndex ⊤ := (Subgroup.relIndex_top_right N).symm
        _ = (N.subgroupOf (⊤ : Subgroup G)).index := rfl
        _ = R.index := by rw [hN_eq]
        _ = 2 ^ n := hn
    have hquot : IsPGroup 2 (G ⧸ N) := by
      rw [IsPGroup.iff_card]
      exact ⟨n, by simpa [← Subgroup.index_eq_card N] using hNindex⟩
    have hxN : x ∈ N := hktPResidual_le N hNnormal hquot hx
    rcases hxN with ⟨y, hy, hyx⟩
    have hy_eq : y = (⟨x, by simp⟩ : (⊤ : Subgroup G)) :=
      Subtype.ext hyx
    simpa [hy_eq] using hy

/-- The 2-residual together with any Sylow 2-subgroup generates a finite
group. -/
public theorem twoResidualAmbient_top_sup_sylow
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G) :
    twoResidualAmbient (⊤ : Subgroup G) ⊔ (S : Subgroup G) = ⊤ := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup G := hktPResidual 2 G
  let _ : R.Normal := hktPResidual_normal
  let q : G →* G ⧸ R := QuotientGroup.mk' R
  have hquot : IsPGroup 2 (G ⧸ R) := hktPResidual_quotient_isPGroup
  let T : Sylow 2 (G ⧸ R) :=
    S.mapSurjective (QuotientGroup.mk'_surjective R)
  have hTtop : (T : Subgroup (G ⧸ R)) = ⊤ :=
    (T.3 (hquot.to_subgroup ⊤) le_top).symm
  have hsup : R ⊔ (S : Subgroup G) = ⊤ := by
    calc
      R ⊔ (S : Subgroup G) = q.ker ⊔ (S : Subgroup G) := by
        rw [QuotientGroup.ker_mk']
      _ = (S : Subgroup G) ⊔ q.ker := by rw [sup_comm]
      _ = ((S : Subgroup G).map q).comap q :=
        (Subgroup.comap_map_eq q (S : Subgroup G)).symm
      _ = ⊤ := by
        rw [show (S : Subgroup G).map q = ⊤ by simpa [T] using hTtop,
          Subgroup.comap_top]
  rw [twoResidualAmbient_top_eq_hktPResidual_low]
  exact hsup

end Stellmacher
