module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanVanishing

/-!
# The strict nonsolvable-alpha six-path

The strict (D>Z) branch of (10.10) uses the residual supplied by the
Cartan construction on the literal six-walk
`g • y -- g • u -- t -- α -- β -- u -- y`.
This module records the geometric part separately from the local linear
quotient: the residual and the Cartan complement fix every vertex of that
walk, while its terminal intersection is trivial.  The right-regularity
argument can therefore consume this witness without reproving the path
calculation.

Source: DGS, *Groups and Graphs* (1985), (10.10), printed p.164.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

private theorem strict_six_path_of_residual
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hua : u ≠ α) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β)
    (K R : Subgroup (G₀ L S))
    (hKfix : K ≤ stabilizer F t ⊓ stabilizer F α ⊓ stabilizer F β ⊓
      stabilizer F u ⊓ stabilizer F y)
    (g : G₀ L S) (hg : g ∈ graphLocalGroup F α)
    (hgK : g ∈ normalizer (K : Set (G₀ L S))) (hgt : g • β = t)
    (hR : R = (D F β t ⊓ Q F u) ⊓ Q F (g • u))
    (_hRne : R ≠ ⊥) (_hRy : R ⊓ Q F y = ⊥) :
    ∃ p : BasedWalk (graph F) 6 (g • y), p.Nonbacktracking ∧
      K ≤ pathStabilizer F p ∧ R ≤ pathStabilizer F p ∧
      IsPGroup 2 R := by
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide, Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hα : (g : G₀ L S) • α = α := sylowGenerated_le _ hg
  have hgygu : (graph F).Adj (g • y) (g • u) := by
    exact (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hy.symm
  have hgut : (graph F).Adj (g • u) t := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hβu
    change (graph F).Adj (g • β) (g • u) at hh
    rw [hgt] at hh
    exact hh.symm
  let p : BasedWalk (graph F) 6 (g • y) :=
    ⟨⟨g • u, hgygu⟩,
      ⟨⟨t, hgut⟩,
        ⟨⟨α, ht.symm⟩,
          ⟨⟨β, hab⟩,
            ⟨⟨u, hβu⟩,
              ⟨⟨y, hy⟩, PUnit.unit⟩⟩⟩⟩⟩⟩
  have hgyt : g • y ≠ t := by
    intro he
    apply hyne
    apply (MulAction.injective (g : G₀ L S))
    simpa only [hgt] using he
  have hguα : g • u ≠ α := by
    intro he
    apply hua
    apply (MulAction.injective (g : G₀ L S))
    exact he.trans hα.symm
  have hp : p.Nonbacktracking := by
    refine ⟨hgyt.symm, hguα.symm, htne.symm, hua, hyne, True.intro⟩
  have hR_D : R ≤ D F β t := by
    rw [hR]
    exact inf_le_left.trans inf_le_left
  have hR_Qu : R ≤ Q F u := by
    rw [hR]
    exact inf_le_left.trans inf_le_right
  have hR_Qgu : R ≤ Q F (g • u) := by
    rw [hR]
    exact inf_le_right
  have hR_t : R ≤ stabilizer F t := by
    exact hR_D.trans (show D F β t ≤ Q F t from inf_le_right) |>.trans
      (Q_le_stabilizer F t)
  have hR_beta : R ≤ stabilizer F β := by
    exact hR_D.trans (show D F β t ≤ Q F β from inf_le_left) |>.trans
      (Q_le_stabilizer F β)
  have hR_Qbeta : R ≤ Q F β := hR_D.trans (show D F β t ≤ Q F β from inf_le_left)
  have hR_u : R ≤ stabilizer F u := hR_Qu.trans (Q_le_stabilizer F u)
  have hR_gu : R ≤ stabilizer F (g • u) :=
    hR_Qgu.trans (Q_le_stabilizer F (g • u))
  have hQu_y : Q F u ≤ stabilizer F y :=
    ((source_Z_Q_U (reduced_triple h) u).2.trans
      (ballKernel_one_le_edge F hy)).trans inf_le_right
  have hQgu_gy : Q F (g • u) ≤ stabilizer F (g • y) :=
    ((source_Z_Q_U (reduced_triple h) (g • u)).2.trans
      (ballKernel_one_le_edge F hgygu.symm)).trans inf_le_right
  have hR_y : R ≤ stabilizer F y := hR_Qu.trans hQu_y
  have hR_gy : R ≤ stabilizer F (g • y) := hR_Qgu.trans hQgu_gy
  have hR_alpha : R ≤ stabilizer F α := by
    have hQbeta_alpha : Q F β ≤ stabilizer F α :=
      ((source_Z_Q_U (reduced_triple h) β).2.trans
        (ballKernel_one_le_edge F hab.symm)).trans inf_le_right
    exact hR_Qbeta.trans hQbeta_alpha
  have hK_α : K ≤ stabilizer F α :=
    hKfix.trans inf_le_left |>.trans inf_le_left |>.trans inf_le_left |>.trans inf_le_right
  have hK_β : K ≤ stabilizer F β :=
    hKfix.trans inf_le_left |>.trans inf_le_left |>.trans inf_le_right
  have hK_u : K ≤ stabilizer F u := hKfix.trans inf_le_left |>.trans inf_le_right
  have hK_y : K ≤ stabilizer F y := hKfix.trans inf_le_right
  have hK_t : K ≤ stabilizer F t :=
    hKfix.trans inf_le_left |>.trans inf_le_left |>.trans inf_le_left |>.trans inf_le_left
  have htransport (v : Vertex F) (hv : K ≤ stabilizer F v) (k : G₀ L S) (hk : k ∈ K) :
      k • (g • v) = g • v := by
    have hk' : (g : G₀ L S)⁻¹ * k * g ∈ K :=
      (mem_set_normalizer_iff''.mp hgK k).mp hk
    calc
      k • (g • v) = (k * g) • v := (mul_smul _ _ _).symm
      _ = (g * (g⁻¹ * k * g)) • v := by congr 1; group
      _ = g • ((g⁻¹ * k * g) • v) := mul_smul _ _ _
      _ = g • v := congrArg (g • ·) (MulAction.mem_stabilizer_iff.mp (hv hk'))
  have hK_t_eq : ∀ k ∈ K, k • t = t := by
    intro k hk
    exact MulAction.mem_stabilizer_iff.mp (hK_t hk)
  have hK_α_eq : ∀ k ∈ K, k • α = α := by
    intro k hk
    exact MulAction.mem_stabilizer_iff.mp (hK_α hk)
  have hK_β_eq : ∀ k ∈ K, k • β = β := by
    intro k hk
    exact MulAction.mem_stabilizer_iff.mp (hK_β hk)
  have hK_u_eq : ∀ k ∈ K, k • u = u := by
    intro k hk
    exact MulAction.mem_stabilizer_iff.mp (hK_u hk)
  have hK_y_eq : ∀ k ∈ K, k • y = y := by
    intro k hk
    exact MulAction.mem_stabilizer_iff.mp (hK_y hk)
  have hR_gy_eq : ∀ r ∈ R, r • (g • y) = g • y := by
    intro r hr
    exact MulAction.mem_stabilizer_iff.mp (hR_gy hr)
  have hR_gu_eq : ∀ r ∈ R, r • (g • u) = g • u := by
    intro r hr
    exact MulAction.mem_stabilizer_iff.mp (hR_gu hr)
  have hR_t_eq : ∀ r ∈ R, r • t = t := by
    intro r hr
    exact MulAction.mem_stabilizer_iff.mp (hR_t hr)
  have hR_alpha_eq : ∀ r ∈ R, r • α = α := by
    intro r hr
    exact MulAction.mem_stabilizer_iff.mp (hR_alpha hr)
  have hR_beta_eq : ∀ r ∈ R, r • β = β := by
    intro r hr
    exact MulAction.mem_stabilizer_iff.mp (hR_beta hr)
  have hR_u_eq : ∀ r ∈ R, r • u = u := by
    intro r hr
    exact MulAction.mem_stabilizer_iff.mp (hR_u hr)
  have hR_y_eq : ∀ r ∈ R, r • y = y := by
    intro r hr
    exact MulAction.mem_stabilizer_iff.mp (hR_y hr)
  have hKpath : K ≤ pathStabilizer F p := fun k hk w hw => by
      simp only [p, BasedWalk.vertices, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | h | h | h | h | h | h
      · rw [h]; exact htransport y hK_y k hk
      · rw [h]; exact htransport u hK_u k hk
      · rw [h]; exact MulAction.mem_stabilizer_iff.mp (hK_t hk)
      · rw [h]; exact MulAction.mem_stabilizer_iff.mp (hK_α hk)
      · rw [h]; exact MulAction.mem_stabilizer_iff.mp (hK_β hk)
      · rw [h]; exact MulAction.mem_stabilizer_iff.mp (hK_u hk)
      · rw [h]; exact MulAction.mem_stabilizer_iff.mp (hK_y hk)
  have hRpath : R ≤ pathStabilizer F p := fun r hr w hw => by
      simp only [p, BasedWalk.vertices, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | h | h | h | h | h | h
      · rw [h]; exact hR_gy_eq r hr
      · rw [h]; exact hR_gu_eq r hr
      · rw [h]; exact hR_t_eq r hr
      · rw [h]; exact hR_alpha_eq r hr
      · rw [h]; exact hR_beta_eq r hr
      · rw [h]; exact hR_u_eq r hr
      · rw [h]; exact hR_y_eq r hr
  exact ⟨p,hp,hKpath,hRpath,
    (isPGroup_pCoreIn 2 (stabilizer F u)).to_le hR_Qu⟩

/-- The strict source residual supplies the literal six-path fixer. -/
theorem original_bTwo_strict_six_path_geometry
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0)) :
    let _E := stabilizer F α ⊓ stabilizer F β
    ∃ K : Subgroup (G₀ L S),
      K ≤ stabilizer F t ⊓ stabilizer F α ⊓ stabilizer F β ⊓
        stabilizer F u ⊓ stabilizer F y ∧
      ∃ g ∈ graphLocalGroup F α, g ∈ normalizer (K : Set (G₀ L S)) ∧
        g • β = t ∧
        let R := bTwoResidual F β t u (g • u)
        ∃ p : BasedWalk (graph F) 6 (g • y), p.Nonbacktracking ∧
          K ≤ pathStabilizer F p ∧ R ≤ pathStabilizer F p ∧
          IsPGroup 2 R ∧ R ≠ ⊥ ∧ R ⊓ Q F y = ⊥ := by
  dsimp only
  have hua : u ≠ α := by
    intro he
    have hh := hc.1
    rw [he,SimpleGraph.dist_self,hb] at hh
    omega
  obtain ⟨K,hfix,hd,hgen,hoK,hcomm,hprod,g,hg,hgK,hgt,a,ha,haK,hau,
    hW,hR,hdec,hdis,hdisu,hKn,hRC,hJC,hthree,hconj,hRne,hzero⟩ :=
    original_bTwo_path_cartan_residual_trivial h hc hne hb hβu ht htne hy hyne hns
  let R := bTwoResidual F β t u (g • u)
  obtain ⟨p,hp,hKp,hRp,hRpg⟩ := strict_six_path_of_residual h hua hβu ht htne hy hyne
    K R hfix g hg hgK hgt hR hRne hzero
  exact ⟨K,hfix,g,hg,hgK,hgt,p,hp,hKp,hRp,hRpg,hRne,hzero⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
