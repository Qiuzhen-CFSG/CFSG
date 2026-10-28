module
public import Theory.GroupAction.RankTwoCosetGeometry.QuinticTwoPathActors
/-!
# Three-path escape from separated local kernels

Let K be the intersection of the radius-one kernels at the standard edge.
If its normalizer in the second vertex group is exactly the edge group,
then intersections belonging to distinct neighbors are distinct. Finiteness
of that vertex group turns containment of two conjugate intersections into
equality. Along a three-path, the intersection of the middle kernels fixes
the whole path and consequently supplies an actor moving the final cubic star.

Only the second vertex group must be finite; the ambient group and graph
may be infinite. The original quintic application proves the normalizer
condition from the faithful action on its elementary closure.
Source: Aschbacher--Smith F.3.2--4 and F.7.3, pp.270 and311--312,
with the original local setup of14.2.20--21, pp.988--989.
-/

public noncomputable section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] (F : Bool → Subgroup G) [Finite (F true)]

private theorem base_kernel_intersection_escape
    (hn : F true ⊓ normalizer
      ((ballKernel F (base F false) 1 ⊓ ballKernel F (base F true) 1 : Subgroup G) : Set G) =
      F false ⊓ F true)
    {d : Vertex F} (hd : (graph F).Adj (base F true) d) (hne : d ≠ base F false) :
    ¬ ballKernel F (base F false) 1 ⊓ ballKernel F (base F true) 1 ≤
      ballKernel F d 1 := by
  let K := ballKernel F (base F false) 1 ⊓ ballKernel F (base F true) 1
  have hK : K ≤ F true := inf_le_right.trans (by
    simpa only [stabilizer, stabilizer_base] using ballKernel_le_stabilizer F (base F true) 1)
  let : Finite K := Finite.of_injective (inclusion hK) (inclusion_injective hK)
  obtain ⟨h, hh, he⟩ := locally_transitive F
    (show (graph F).Adj (base F true) (base F false) from
      ⟨(by change true ≠ false; decide), incident_base F true false⟩) hd
  have hh' : h • base F true = base F true := hh
  have hm : K.map (MulAut.conj h).toMonoidHom =
      ballKernel F d 1 ⊓ ballKernel F (base F true) 1 := by
    change (ballKernel F (base F false) 1 ⊓ ballKernel F (base F true) 1).map
      (MulAut.conj h).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj h).injective,
      ← ballKernel_translate, ← ballKernel_translate, he, hh']
  intro hle
  have hkmap : K ≤ K.map (MulAut.conj h).toMonoidHom := by
    rw [hm]
    exact le_inf hle inf_le_right
  have hcard : Nat.card (K.map (MulAut.conj h).toMonoidHom) = Nat.card K :=
    card_map_of_injective (MulAut.conj h).injective
  let : Finite (K.map (MulAut.conj h).toMonoidHom) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.ne_of_gt (Nat.card_pos : 0 < Nat.card K))
  have heq : K.map (MulAut.conj h).toMonoidHom = K :=
    (eq_of_le_of_card_ge hkmap hcard.le).symm
  have hhN : h ∈ normalizer (K : Set G) := mem_normalizer_iff_map_conj_eq.mpr heq
  have hhH : h ∈ F true := by simpa only [stabilizer, stabilizer_base] using hh
  have hhB : h ∈ F false := (hn ▸ (show h ∈ F true ⊓ normalizer (K : Set G) from ⟨hhH, hhN⟩)).1
  have hhfix : h • base F false = base F false := by
    apply MulAction.mem_stabilizer_iff.mp
    simpa only [stabilizer_base] using hhB
  exact hne (he.symm.trans hhfix)

/-- Separation of the incident core intersections gives cubic escape on every
three-path from the quintic root, even when the ambient graph is infinite. -/
theorem three_path_kernel_escape_of_intersection_normalizer
    (hn : F true ⊓ normalizer
      ((ballKernel F (base F false) 1 ⊓ ballKernel F (base F true) 1 : Subgroup G) : Set G) =
      F false ⊓ F true)
    (p : BasedWalk (graph F) 3 (base F true)) (hp : p.Nonbacktracking) :
    ¬ pathStabilizer F p ≤ ballKernel F p.endpoint 1 := by
  rcases p with ⟨⟨b, hab⟩, ⟨⟨c, hbc⟩, ⟨⟨d, hcd⟩, pend⟩⟩⟩
  have hb : b.type = false := by
    have hh := hab.1
    change true ≠ b.type at hh
    cases ht : b.type <;> simp_all
  have hc : c.type = true := by
    have hh := hbc.1
    rw [hb] at hh
    cases ht : c.type <;> simp_all
  obtain ⟨g, hg, hg'⟩ := incident_common_translate F hbc.2
  rw [hb] at hg
  change g • base F false = b at hg
  rw [hc] at hg'
  have hd : (graph F).Adj (base F true) (g⁻¹ • d) := by
    have hh := (translationGraphIso F g⁻¹).toHom.map_adj hcd
    change (graph F).Adj (g⁻¹ • c) (g⁻¹ • d) at hh
    simpa only [←hg', inv_smul_smul] using hh
  have hne : g⁻¹ • d ≠ base F false := by
    intro he
    have hh := congrArg (g • ·) he
    simp only [smul_inv_smul, hg] at hh
    exact hp.2.1 hh
  intro hle
  apply base_kernel_intersection_escape F hn hd hne
  intro x hx
  have hbfix : g*x*g⁻¹ ∈ ballKernel F b 1 := by
    rw [←hg]
    exact (conj_mem_ballKernel_iff F g x (base F false) 1).mpr hx.1
  have hcfix : g*x*g⁻¹ ∈ ballKernel F c 1 := by
    rw [←hg']
    exact (conj_mem_ballKernel_iff F g x (base F true) 1).mpr hx.2
  have hpath : ∀ z ∈ [base F true, b, c, d], (g*x*g⁻¹) • z = z := by
    simp only [List.forall_mem_cons]
    exact ⟨hbfix _ ((mem_ball_one F _ _).mpr (.inl hab.symm)),
      hbfix _ (center_mem_ball F b 1), hcfix _ (center_mem_ball F c 1),
      hcfix _ ((mem_ball_one F _ _).mpr (.inl hcd)), by intro z hz; cases hz⟩
  have hout : g*x*g⁻¹ ∈ ballKernel F d 1 := hle hpath
  have he := (conj_mem_ballKernel_iff F g x (g⁻¹ • d) 1)
  rw [smul_inv_smul] at he
  exact he.mp hout
end Subgroup.CosetGeometry.RankTwo
