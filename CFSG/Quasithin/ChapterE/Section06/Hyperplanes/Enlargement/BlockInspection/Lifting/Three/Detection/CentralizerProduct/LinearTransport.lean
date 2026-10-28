module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection.CentralizerProduct.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection.CentralizerProduct.FactorAction
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.NaturalCentralizers

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Marked

/-!
# Transport control for natural factors of the E.6.7 envelope

The corank-two bound in E.6.7 forces a natural factor to have field order
four. The inner V-action on its common Sylow subgroup then identifies
C_L(U) with that Sylow subgroup S: a nontrivial U-action is represented by
a noncentral element of Ω₁(Z(S)), whose centralizer is a two-group.

If l*c transports U into V and c centralizes L, the conjugate l⁻¹*S*l
centralizes U. Sylow maximality forces l to normalize S. The marked natural
model identifies N_L(S) with the full Borel L∩M, giving the required
coordinate control. All central extensions allowed by shortness are retained.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7,
printed p.246, the block case of E.6.23, pp.254–255, and C.1.7–13,
pp.123–125. This proves the natural-factor transporter contract; the
central-product assembly remains in the parent module.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection
open InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G] [Finite G]

private theorem natural_centralizer_eq_sylow {L U V : Subgroup G}
    (hL : ChapterC.IsL2EvenBlock L 2) (S : Sylow 2 L)
    (hSV : ∀ s ∈ (S : Subgroup L), (s : G) ∈ centralizer (V : Set G))
    (hUV : U ≤ V)
    (haction : ∀ v ∈ V, ∃ z : L,
      z ∈ Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ∧
      ∀ x : L, (z : G) * (x : G) * (z : G)⁻¹ = v * (x : G) * v⁻¹)
    (hn : ¬ L ≤ centralizer (U : Set G)) :
    (centralizer (U : Set G)).subgroupOf L = (S : Subgroup L) := by
  classical
  have hnU : ¬ U ≤ centralizer (L : Set G) := fun hc => hn (le_centralizer_iff.mp hc)
  obtain ⟨u, hu, hunc⟩ := SetLike.not_le_iff_exists.mp hnU
  obtain ⟨z, hz, hzu⟩ := haction u (hUV hu)
  have hnz : z ∉ center L := by
    intro hzc
    apply hunc
    apply mem_centralizer_iff.mpr
    intro x hx
    have hzx : (z : G) * x * (z : G)⁻¹ = x := by
      have hc := congrArg Subtype.val (mem_center_iff.mp hzc (⟨x, hx⟩ : L))
      change x * (z : G) = (z : G) * x at hc
      rw [← hc, mul_inv_cancel_right]
    have he : u * x * u⁻¹ = x := (hzu ⟨x, hx⟩).symm.trans hzx
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hp := BlockCase.naturalFourCentralizers L hL S z hz hnz
  have hCz : (centralizer (U : Set G)).subgroupOf L ≤ centralizer ({z} : Set L) := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    have hux := mem_centralizer_iff.mp hx u hu
    change u * (x : G) = (x : G) * u at hux
    have he : (z : G) * (x : G) * (z : G)⁻¹ = (x : G) := by
      rw [hzu x, hux, mul_inv_cancel_right]
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  apply S.is_maximal' (hp.to_le hCz)
  intro s hs
  exact centralizer_le hUV (hSV s hs)

private theorem transporter_of_sylow_centralizer {L M U V : Subgroup G}
    (S : Sylow 2 L)
    (hSV : ∀ s ∈ (S : Subgroup L), (s : G) ∈ centralizer (V : Set G))
    (hC : (centralizer (U : Set G)).subgroupOf L = (S : Subgroup L))
    (hN : normalizer (S : Set L) ≤ M.subgroupOf L) :
    FactorTransporter L M U V := by
  intro l hl c hc htrans
  let lL : L := ⟨l, hl⟩
  let f := (MulAut.conj lL⁻¹).toMonoidHom
  have hconj : (S : Subgroup L).map f ≤ (centralizer (U : Set G)).subgroupOf L := by
    rintro y ⟨s, hs, rfl⟩
    apply mem_centralizer_iff.mpr
    intro u hu
    change u * ((f s : L) : G) = ((f s : L) : G) * u
    let g := MulAut.conj (l * c)
    have hy : g ((f s : L) : G) = (s : G) := by
      have hcy := mem_centralizer_iff.mp hc (f s) (f s).property
      change (l * c) * ((f s : L) : G) * (l * c)⁻¹ = (s : G)
      calc
        _ = l * (c * ((f s : L) : G) * c⁻¹) * l⁻¹ := by group
        _ = l * ((f s : L) : G) * l⁻¹ := by rw [← hcy, mul_inv_cancel_right]
        _ = (s : G) := by
          change l * (l⁻¹ * (s : G) * (l⁻¹)⁻¹) * l⁻¹ = _
          group
    apply g.injective
    simp only [map_mul, hy]
    exact mem_centralizer_iff.mp (hSV s hs) (g u)
      (htrans (mem_map_of_mem (MulAut.conj (l * c)).toMonoidHom hu))
  have he : (S : Subgroup L) = (S : Subgroup L).map f :=
    (S.mapSurjective (f := f) (MulAut.conj lL⁻¹).surjective).is_maximal'
      S.isPGroup' (hconj.trans_eq hC)
  have hn : lL⁻¹ ∈ normalizer (S : Set L) :=
    mem_normalizer_iff_map_conj_eq.mpr he.symm
  exact hN ((normalizer (S : Set L)).inv_mem_iff.mp hn)

/-- A natural factor of the corank-two envelope controls its coordinate in every transporter. -/
theorem envelope_factor_natural_transporter
    {K : GroupClass} {T : Sylow 2 G} {M V U A : Subgroup G}
    (h : HypothesisE61 K T M V) (h21 : OddCoreFree V)
    (hU : U ∈ obstructionFamily M V) (_hplane : IsHyperplane V U)
    (hA : A ∈ obstructionFamily M V) (_hAU : A ≤ U)
    (hcorank : subgroupCorank V A = 2)
    (d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V A
      (layerEnvelope (centralizer (A : Set G)) (sylowCentralizer (T : Subgroup G) V)))
    (i : Fin d.count) {n : ℕ} (hL : ChapterC.IsL2EvenBlock (d.block i) n)
    (hn : ¬ d.block i ≤ centralizer (U : Set G)) :
    FactorTransporter (d.block i) M U V := by
  obtain ⟨X, _, _, _, _, _, _, _, hB, hbound⟩ := d.rankOne i n hL
  rw [hcorank] at hbound
  have hn2 : n = 2 := by have := hL.1; omega
  subst n
  obtain ⟨S, hS, haction⟩ := envelope_factor_sylow_action h h21 hA d i
  have hSQ (s : d.block i) (hs : s ∈ (S : Subgroup (d.block i))) :
      (s : G) ∈ sylowCentralizer (T : Subgroup G) V := by
    have hm := mem_map_of_mem (d.block i).subtype hs
    rw [hS] at hm
    exact hm.2
  have hSV (s : d.block i) (hs : s ∈ (S : Subgroup (d.block i))) :
      (s : G) ∈ centralizer (V : Set G) := (hSQ s hs).2
  have hSM : (S : Subgroup (d.block i)) ≤ M.subgroupOf (d.block i) :=
    fun s hs => h.sylow_le (hSQ s hs).1
  have hC := natural_centralizer_eq_sylow hL S hSV hU.1 haction hn
  obtain ⟨F, _, _, _, _, ⟨a⟩⟩ := L2Torus.exists_markedBlockModel hL hB
  have hN : normalizer (S : Set (d.block i)) = M.subgroupOf (d.block i) := by
    rw [← S.coe_coe, a.sylow_eq_root_comap S hSM,
      ← comap_normalizer_eq_of_surjective _ a.linearMap_surjective]
    exact a.borel.symm
  exact transporter_of_sylow_centralizer S hSV hC hN.le

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection
