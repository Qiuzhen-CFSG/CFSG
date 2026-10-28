module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalPaths

/-!
# Excluding a linear quotient at the last odd vertex

In the epsilon-two branch, either b=2 or b≥6. The first singular path
fits at the end of the critical path, whose endpoint has a natural SL₂
center action. An escaping critical center excludes that endpoint type.
At the preceding type, the radius-two actor supplies the same contradiction
if the local quotient is SL₂. Characteristic-two PSL₂ is transported to
SL₂, excluding both literal models at the last odd vertex.

The earlier local and natural-center hypotheses remain explicit; this is
the path exclusion, not the final unconditional distance bound.
Source: DGS, *Groups and Graphs* (1985), (7.5)(5), printed p.130.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.BasedWalk Theory.GroupAction.CubicTree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem graph_epsilonTwo_last_odd_not_linear
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) y ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) y : Subgroup G) : Set G))
    {v w u : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w))
    (hsyl : Stellmacher.IsSylowSubgroupIn
      (Z (family P) v ⊔ Q (family P) w) (stabilizer (family P) w))
    (hbranch : ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k) :
    b (family P) = 2 ∨
      (6 ≤ b (family P) ∧ ∃ t y : Vertex (family P),
        (graph (family P)).Adj w t ∧ (graph (family P)).Adj t y ∧
        (graph (family P)).dist v t + 1 = b (family P) ∧
        (graph (family P)).dist v y + 2 = b (family P) ∧
        V (family P) v 2 ≤ Q (family P) y ∧
        (¬ V (family P) v 2 ≤ Q (family P) t) ∧
        ∀ (k : Type u) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
          (¬ Nonempty ((L t ⧸ pCore 2 (L t)) ≃* SL(2,k))) ∧
          (¬ Nonempty ((L t ⧸ pCore 2 (L t)) ≃*
            Matrix.ProjectiveSpecialLinearGroup (Fin 2) k))) := by
  rcases graph_epsilonTwo_radius_two_configuration h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hdu hepsilon hnat₀ hnat₁ hsyl with hb | ⟨hb,t,y,hwt,hty,hdt,hdy,hcore,hesc,_⟩
  · exact Or.inl hb
  rcases graph_epsilonTwo_regularity_length h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hdu hepsilon hnat₀ hnat₁ with hb' | ⟨s,hs,hsb,hshort,hbad,_⟩
  · exact Or.inl hb'
  refine Or.inr ⟨hb,t,y,hwt,hty,hdt,hdy,hcore,hesc,?_⟩
  intro k _ _ _
  have hnlin : ¬ Nonempty ((L t ⧸ pCore 2 (L t)) ≃* SL(2,k)) := by
    intro heq
    cases s with
    | zero => omega
    | succ m =>
      obtain ⟨x,r,hr,hbad⟩ := hbad
      obtain ⟨q,hq,hqy⟩ := BasedWalk.exists_geodesic ((connected_graph h) v y)
      let q₁ := q.snoc (show (graph (family P)).Adj q.endpoint t from hqy.symm ▸ hty.symm)
      have he₁ : q₁.endpoint = t := BasedWalk.endpoint_snoc _ _
      let q₂ := q₁.snoc (show (graph (family P)).Adj q₁.endpoint w from he₁.symm ▸ hwt.symm)
      have he₂ : q₂.endpoint = w := BasedWalk.endpoint_snoc _ _
      have hp₁ : q₁.Nonbacktracking := BasedWalk.nonbacktracking_of_geodesic q₁ (by rw [he₁]; omega)
      have hp₂ : q₂.Nonbacktracking := BasedWalk.nonbacktracking_of_geodesic q₂ (by rw [he₂,hc.1]; omega)
      let c₂ := d q₂.endpoint q₂.penultimate q₂.adj_penultimate_endpoint.symm
      have hn₂ : HasNaturalCenter c₂.Pstar (Z (family P) q₂.endpoint) (Q (family P) q₂.endpoint) := by
        simpa only [c₂,hstar,he₂] using hnat₁
      have hfix₂ : Z (family P) v ≤ pathStabilizer (family P) q₂ :=
        graph_center_le_pathStabilizer h q₂ (by omega)
      have hesc₂ : ¬ Z (family P) v ≤ Q (family P) q₂.endpoint := by
        rw [he₂]
        exact fun hh => hc.2 (hh.trans (source_Z_Q_U h w).2)
      have ht₂ : q₂.endpoint.type ≠ r.endpoint.type := by
        intro htype
        obtain ⟨f,hf,hfin,halg,π,hπ,hk,_⟩ := hn₂
        let : CharP f 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) f).injective 2
        let := graph_Z_elementary h v
        exact hbad (graph_linear_terminal_nonsingular h hB hbranch (by omega) hshort q₂ r hp₂ hr htype
          c₂ (by rw [hstar]; exact hodd q₂.endpoint) π hπ hk (Z (family P) v)
          (IsElementaryAbelian.isPGroup 2 _) hfix₂ hesc₂)
      have ht₁ : q₁.endpoint.type = r.endpoint.type := by
        have had := hwt.1
        rw [he₂] at ht₂
        rw [he₁]
        cases hw : w.type <;> cases ht : t.type <;> cases hx : r.endpoint.type <;> simp_all
      let c₁ := d q₁.endpoint q₁.penultimate q₁.adj_penultimate_endpoint.symm
      have hc₁ : c₁.Pstar = L t := by rw [hstar,he₁]
      have hlin : Nonempty ((c₁.Pstar ⧸ pCore 2 c₁.Pstar) ≃* SL(2,k)) := by rwa [hc₁]
      obtain ⟨e⟩ := hlin
      let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c₁.Pstar))
      have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
      have hk : π.ker = (Q (family P) q₁.endpoint).subgroupOf c₁.Pstar := by
        have hcore' : (Q (family P) q₁.endpoint).subgroupOf c₁.Pstar = pCore 2 c₁.Pstar := by
          have hh : Q (family P) q₁.endpoint = c₁.Pstar.pCoreIn 2 := c₁.same_core.symm
          rw [hh]
          exact comap_map_eq_self_of_injective c₁.Pstar.subtype_injective _
        rw [hcore']
        ext a
        change e (QuotientGroup.mk' (pCore 2 c₁.Pstar) a) = 1 ↔ a ∈ pCore 2 c₁.Pstar
        rw [map_eq_one_iff e e.injective]
        exact QuotientGroup.eq_one_iff a
      have hfix₁ : V (family P) v 2 ≤ pathStabilizer (family P) q₁ :=
        graph_radius_two_le_extended_pathStabilizer h q _ (by omega) (by rw [hqy]; exact hcore)
      exact hbad (graph_linear_terminal_nonsingular h hB hbranch (by omega) hshort q₁ r hp₁ hr ht₁
        c₁ (by rw [hstar]; exact hodd q₁.endpoint) π hπ hk (V (family P) v 2)
        (graph_V_isPGroup_of_short h hS v (by omega)) hfix₁ (by rw [he₁]; exact hesc))
  refine ⟨hnlin,?_⟩
  rintro ⟨e⟩
  exact hnlin ⟨e.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
    ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
