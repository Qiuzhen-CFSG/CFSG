module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.DegreeDivisibility.Numerics
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.DegreeDivisibility.ModelTransitivity
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.CentralOmega
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.SylowCensus

/-!
# Root normalizers and the actual model transitivity in Lemma 16.4(c)

The circle Sylow is marked by the original Borel. Its Omega image Q is
therefore normalized by B∩M. Elements of B centralize u, so this gives
normalization of Q⟨u⟩. The concrete normalizer transitivity in each original
odd central cover supplies the conjugators on Q#, through the literal circle
map; these conjugators also centralize u.

Source: GLS IV, Chapter 2, Lemma 16.4(c).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory RankOneModelGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem normalizes_root_join_of_centralizes (Q : Subgroup G) (u : G) :
    normalizer (Q : Set G) ⊓ centralizer ({u} : Set G) ≤
      normalizer ((Q ⊔ zpowers u : Subgroup G) : Set G) := by
  intro g hg
  apply normalizer_inf_normalizer_le_normalizer_sup Q (zpowers u)
  refine ⟨hg.1, ?_⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  congr 1
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg.2)

/-- The whole marked Borel intersection normalizes the source Q⟨u⟩. -/
public theorem source16_borel_normalizes_root_join
    (h : IsProductDisconnected Z M) {u : G}
    (P : Sylow 2 (localCircle Z (centralizer ({u} : Set G))))
    (hmark : M.comap (localCircleHom Z (centralizer ({u} : Set G))) =
      normalizer (P : Set (localCircle Z (centralizer ({u} : Set G))))) :
    let B := centralizer ({u} : Set G)
    let Q := (omegaOneAmbient (P : Subgroup (localCircle Z B))).map (localCircleHom Z B)
    B ⊓ M ≤ normalizer ((Q ⊔ zpowers u : Subgroup G) : Set G) := by
  let B := centralizer ({u} : Set G)
  let f := localCircleHom Z B
  let H := (P : Subgroup (localCircle Z B)).map f
  let Q := (omegaOneAmbient (P : Subgroup (localCircle Z B))).map f
  have hQ : Q = omegaOneAmbient H := map_omegaOneAmbient_injective f (localCircleHom_injective Z B) _
  have hBQ : B ⊓ M ≤ normalizer (Q : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hQ, map_omegaOneAmbient_injective _ (MulAut.conj g).injective,
      mem_normalizer_iff_map_conj_eq.mp (source16_circle_marked_sylow_normalized h B P hmark hg)]
  exact (le_inf hBQ inf_le_left).trans (normalizes_root_join_of_centralizes Q u)

/-- Actual N_L(P) conjugators from the four source covering models map to
N_G(Q)∩C_G(u), preserving the marked Q elements. -/
public theorem source16_circle_root_transitivity
    {u : G} (P : Sylow 2 (localCircle Z (centralizer ({u} : Set G))))
    {n : ℕ} (hn : 2 ≤ n)
    (hperfect : commutator (localCircle Z (centralizer ({u} : Set G))) = ⊤)
    (hodd : Odd (Nat.card (center (localCircle Z (centralizer ({u} : Set G))))))
    (hmodel : IsSimpleBenderGroupAtExponent n
      (localCircle Z (centralizer ({u} : Set G)) ⧸
        center (localCircle Z (centralizer ({u} : Set G))))) :
    let B := centralizer ({u} : Set G)
    let Q := (omegaOneAmbient (P : Subgroup (localCircle Z B))).map (localCircleHom Z B)
    ∀ z ∈ Q, z ≠ 1 → ∀ x ∈ Q, x ≠ 1 →
      ∃ a ∈ normalizer (Q : Set G) ⊓ centralizer ({u} : Set G), MulAut.conj a z = x := by
  let B := centralizer ({u} : Set G)
  let C := localCircle Z B
  let f := localCircleHom Z B
  let Q := (omegaOneAmbient (P : Subgroup C)).map f
  dsimp only
  intro z hz hz1 x hx hx1
  obtain ⟨zC, hzC, rfl⟩ := hz
  obtain ⟨xC, hxC, rfl⟩ := hx
  obtain ⟨a, ha, he⟩ := oddCentralCover_omega_normalizer_transitive hn hperfect hodd hmodel
    P zC hzC (fun he => hz1 (he ▸ f.map_one)) xC hxC (fun he => hx1 (he ▸ f.map_one))
  have haQ : a ∈ normalizer (omegaOneAmbient (P : Subgroup C) : Set C) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_omegaOneAmbient_injective _ (MulAut.conj a).injective,
      mem_normalizer_iff_map_conj_eq.mp ha]
  refine ⟨f a, ⟨(omegaOneAmbient (P : Subgroup C)).le_normalizer_map f
    (mem_map_of_mem f haQ), (a : B).property⟩, ?_⟩
  simpa only [MulAut.conj_apply, map_mul, map_inv] using congrArg f he

end BenderSuzuki.ZD
