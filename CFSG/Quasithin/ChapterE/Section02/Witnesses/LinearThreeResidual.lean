module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.ResidualCentralImage
public import CFSG.Quasithin.ChapterE.Section02.Structure.LinearThree.Placement
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.RootScalars
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The residual-fixed degree-three source has binary field

The original residual-centralization assumption gives a nonidentity central
point of the maximal subgroup inside the chosen elementary subgroup. The
corefree long-root placement puts that point in the center of the model
Sylow subgroup. For fields larger than two, a Borel scalar moves every
nonidentity point of this root group, giving a contradiction. The source
wrapper transports the prescribed subgroup and residual through the literal
maximal-core quotient.

Source: Aschbacher--Smith, E.2.17, the nonsolvable reduction on printed p.230.
-/

public section
open Subgroup
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3Even.MinimalParabolicWitness
open Matrix.PSL3Even.UnipotentGeometry
namespace CFSG.Quasithin.ChapterE.Witnesses
variable {H : Type*} [Group H] [Finite H]

theorem coreFree_linear_three_parameter_eq_one_of_residual_centralizes
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup K] (e : K ≃* PSL(3,F))
    (T : Sylow 2 H) (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hcore : (ChapterB.minimalParabolicMax T hP).normalCore = ⊥)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal) (hne : V ≠ ⊥)
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) : n = 1 := by
  by_contra hn1
  have hn' : 1 < n := by omega
  let M := ChapterB.minimalParabolicMax T hP
  have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  obtain ⟨g,hU,hB,hplace⟩ := Structure.LinearThree.exists_longRoot_placement
    F hn hF K e T hgen hP hcore V hVT hTV
  let f := modelEmbedding F K (e.trans (MulAut.conj g))
  have hf := modelEmbedding_injective F K (e.trans (MulAut.conj g))
  obtain ⟨v,hv,hvne,hvc⟩ := source_maximal_center_point T hP V hVT hvn hne hres
  obtain ⟨z,hz,hzv⟩ := hplace hv
  have hcv : ∀ y ∈ M, y * v = v * y := by
    obtain ⟨c,hc,hcv⟩ := hvc
    intro y hy
    rw [←hcv]
    exact congrArg Subtype.val (mem_center_iff.mp hc ⟨y,hy⟩)
  have hzC : z ∈ (center (unipotentSylow F hn hF)).map
      (unipotentSylow F hn hF : Subgroup PSL(3,F)).subtype := by
    change z ∈ (center (unipotent F)).map (unipotent F).subtype
    rwa [←projectiveCenter_eq_mapped_center]
  have hz1 : z = 1 := RootScalars.sylow_center_fixed_eq_one F hn' hF
    (MulEquiv.refl _) (unipotentSylow F hn hF) z hzC (by
      intro b hb
      have hbB : b ∈ borel F := by
        change b ∈ normalizer (unipotent F : Set PSL(3,F)) at hb
        rwa [normalizer_unipotent F hn hF] at hb
      have hbM : f b ∈ M := by
        change b ∈ M.comap f
        rw [hB]
        exact hbB
      apply hf
      change f (b*z*b⁻¹) = f z
      rw [map_mul,map_mul,map_inv]
      have hh : f b * f z = f z * f b := by rw [hzv]; exact hcv _ hbM
      rw [hh,mul_inv_cancel_right])
  exact hvne (hzv.symm.trans ((congrArg f hz1).trans f.map_one))
theorem source_linear_three_parameter_eq_one_of_residual_centralizes
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 (2^n))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) : n = 1 := by
  let J := ChapterB.minimalParabolicCore T hP
  let M := ChapterB.minimalParabolicMax T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.map q
  let D := K.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  have hi := Structure.source_normal_simple_image T hP hs K hK hgen
  have hmin : ChapterB.IsMinimalParabolicOver S ⊤ := (Structure.source_star_minimal_core_free T hP).1
  have hcore : ChapterB.minimalParabolicCore S hmin=⊥ := (Structure.source_star_minimal_core_free T hP).2
  have hmax : ChapterB.minimalParabolicMax S hmin=M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hWS : W ≤ (S : Subgroup (H ⧸ J)) := map_mono hVT
  have hSW : (W.subgroupOf (S : Subgroup (H ⧸ J))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWS).mpr
      ((map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hvn)).trans (le_normalizer_map q))
  have hne : W ≠ ⊥ := by
    intro hh
    have hle := (map_eq_bot_iff V).mp hh
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using hle)
  have hres' : (pResidual 2 (ChapterB.minimalParabolicMax S hmin)).map
      (ChapterB.minimalParabolicMax S hmin).subtype ≤ centralizer (W : Set (H ⧸ J)) := by
    rw [hmax,←map_embedded_pResidual]
    exact (map_mono hres).trans (map_centralizer_le_centralizer_image (V : Set H) q)
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let : D.Normal := hi.2.2.1
  let : IsSimpleGroup D := hi.1
  exact coreFree_linear_three_parameter_eq_one_of_residual_centralizes F hn hcard D e S
    hi.2.2.2 hmin hcore W hWS hSW hne hres'

end CFSG.Quasithin.ChapterE.Witnesses
