module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.DegreeDivisibility.Fusion
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceRankOne.MarkedRoot

/-!
# Normality of the literal circle Sylow in the marked Borel

The marked intersection M∩L is the normalizer in L of its actual Sylow
subgroup P. An element of B∩M normalizes L and M, hence sends P to a
p-subgroup of this same normalizer. Uniqueness of its Sylow p-subgroup
forces P to be preserved. This supplies the relative normality used in
the product-order bound at the end of GLS IV, Chapter 2, Lemma 16.4(c).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory
open scoped Pointwise
universe u v

private theorem normalizes_sylow_image_of_normalizes_range
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    {p : ℕ} [Fact p.Prime] (f : H →* G) (hf : Function.Injective f)
    (M : Subgroup G) (P : Sylow p H)
    (hmark : M.comap f = normalizer (P : Set H)) {g : G}
    (hgM : g ∈ M) (hgC : g ∈ normalizer (f.range : Set G)) :
    g ∈ normalizer ((P : Subgroup H).map f : Set G) := by
  let W := (P : Subgroup H).map f
  let X := W.conjBy g
  have hWM : W ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    change x ∈ M.comap f
    rw [hmark]
    exact (P : Subgroup H).le_normalizer hx
  have hXM : X ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem hgM (hWM hx)) (M.inv_mem hgM)
  have hXC : X ≤ f.range := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hgC x).mp (map_le_range f (P : Subgroup H) hx)
  have hXp : IsPGroup p X := (P.isPGroup'.map f).map (MulAut.conj g).toMonoidHom
  have hXH : IsPGroup p (X.comap f) := hXp.of_injective (f.subgroupComap X) (fun a b he => Subtype.ext (hf (congrArg Subtype.val he)))
  have hXN : X.comap f ≤ normalizer (P : Set H) := hmark ▸ comap_mono hXM
  have hXP : X.comap f ≤ (P : Subgroup H) := by
    intro x hx
    have hh : x ∈ X.comap f ⊓ normalizer (P : Set H) := ⟨hx, hXN hx⟩
    rw [hXH.inf_normalizer_sylow P] at hh
    exact hh.2
  have hXW : X ≤ W := by
    rw [← map_comap_eq_self hXC]
    exact map_mono hXP
  have he : X = W := eq_of_le_of_card_ge hXW
    (card_map_of_injective (K := W) (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).ge
  exact mem_normalizer_iff_map_conj_eq.mpr he

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The actual circle Sylow marked by the source Borel is normalized by B∩M. -/
public theorem source16_circle_marked_sylow_normalized
    (h : IsProductDisconnected Z M) (B : Subgroup G)
    (P : Sylow 2 (localCircle Z B))
    (hmark : M.comap (localCircleHom Z B) = normalizer (P : Set (localCircle Z B))) :
    B ⊓ M ≤ normalizer ((P : Subgroup (localCircle Z B)).map
      (localCircleHom Z B) : Set G) := by
  have hrange : (localCircleHom Z B).range = localCircleIn Z B := by
    rw [localCircleHom, MonoidHom.range_comp]
    simp only [range_subtype, localCircleIn]
  intro g hg
  apply normalizes_sylow_image_of_normalizes_range (localCircleHom Z B)
    (localCircleHom_injective Z B) M P hmark hg.2
  rw [hrange]
  exact source16_normalizer_preserves_localCircle h B (B.le_normalizer hg.1)

/-- Any circle Sylow whose ambient image lies in M is the marked Borel
Sylow. Thus the marker is discharged for the Sylow obtained by intersection. -/
public theorem source16_circle_sylow_borel
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    (B : Subgroup G) (hB : B ≠ ⊤) (hBM : ¬ B ≤ M)
    (hne : ∃ z ∈ Z, z ∈ B ∧ z ∈ M)
    (hns : ¬ Group.IsSolvable (localCircle Z B))
    (P : Sylow 2 (localCircle Z B))
    (hPM : (P : Subgroup (localCircle Z B)).map (localCircleHom Z B) ≤ M) :
    M.comap (localCircleHom Z B) = normalizer (P : Set (localCircle Z B)) := by
  obtain ⟨S, hS, _⟩ := localCircle_exists_marked_sylow h r ha B hB hBM hne hns
  have hPN : (P : Subgroup (localCircle Z B)) ≤ normalizer (S : Set (localCircle Z B)) := by
    rw [← hS]
    intro x hx
    exact hPM (mem_map_of_mem (localCircleHom Z B) hx)
  have hPS : (P : Subgroup (localCircle Z B)) ≤ (S : Subgroup (localCircle Z B)) := by
    intro x hx
    have hh : x ∈ (P : Subgroup (localCircle Z B)) ⊓ normalizer (S : Set (localCircle Z B)) :=
      ⟨hx,hPN hx⟩
    rw [P.isPGroup'.inf_normalizer_sylow S] at hh
    exact hh.2
  have he : P = S := Sylow.ext (P.is_maximal' S.isPGroup' hPS).symm
  simpa only [he] using hS

/-- The circle Sylow has trivial intersection with the original two-point
stabilizer: a nontrivial two-subgroup intersection would contain an involution,
which is distinguished inside the circle and cannot belong to D. -/
public theorem source16_circle_sylow_disjoint_pair
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (B : Subgroup G) (hB : B ≠ ⊤) (hBM : ¬ B ≤ M)
    (hne : ∃ z ∈ Z, z ∈ B ∧ z ∈ M) {t : G} (htM : t ∉ M)
    (P : Sylow 2 (localCircle Z B)) :
    Disjoint ((P : Subgroup (localCircle Z B)).map (localCircleHom Z B))
      (residualPairStabilizer M t) := by
  let W := (P : Subgroup (localCircle Z B)).map (localCircleHom Z B)
  let E := W ⊓ residualPairStabilizer M t
  apply disjoint_iff.mpr
  by_contra hE
  let : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).mpr hE
  have hEp : IsPGroup 2 E := (P.isPGroup'.map (localCircleHom Z B)).to_le inf_le_left
  obtain ⟨k,hk,hcard⟩ := hEp.nontrivial_iff_card.mp inferInstance
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := E) 2
    (hcard ▸ dvd_pow_self 2 (by omega))
  have hxi : PFAppendixIII.IsInvolution (x : G) :=
    BenderSuzuki.IsInvolution.map_of_injective (orderOf_eq_prime_iff.mp hx).symm
      E.subtype E.subtype_injective
  obtain ⟨y,hy,hye⟩ := x.property.1
  have hyi : PFAppendixIII.IsInvolution y := by
    refine ⟨fun he => hxi.ne_one (hye.symm.trans (he ▸ map_one _)), ?_⟩
    apply localCircleHom_injective Z B
    rw [map_pow, hye, hxi.sq_eq_one, map_one]
  have hyZ := localCircle_involution_mem h r B hB hBM hne hyi
  exact not_mem_Z_of_mem_residualPairStabilizer h htM x.property.2 (hye ▸ hyZ)

end BenderSuzuki.ZD
