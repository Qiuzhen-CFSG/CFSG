module
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic

/-!
# Binary automorphisms in arbitrary degree

An automorphism preserves transvections through their intrinsic central-Sylow
characterization. A transvection subgroup has a common image or common kernel;
self-centralization identifies the image of a point radical. Inverse transpose
orients this image, and equivariance reconstructs a linear conjugating map.

This extends the proofs in `OuterCyclic.RadicalOrientation.TransvectionSubgroups`,
`OuterCyclic.RadicalOrientation.Duality` and `OuterCyclic.PointRigidity` beyond
dimensions four and five. Their private calculations are reproduced here with
the dimension hypotheses actually used, preserving the existing module APIs.
The result is needed for the elementary outer-Sylow degree bound in G.10.15(3).

Source: GLS3, Theorem 2.5.12(b–e,i) and §2.7,
`refs/KGroup/GLS3/chapter2.tex`, especially lines 1111–1115.
-/

public section
namespace BinaryLinear.ElementaryOuterSylow
open OuterCyclic Matrix
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem binary_cases (a : ZMod 2) : a = 0 ∨ a = 1 :=
  (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a

private theorem scalar_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (binary_cases a).resolve_left ha

private theorem exists_value_one {f : V →ₗ[ZMod 2] ZMod 2} (hf : f ≠ 0) :
    ∃ x, f x = 1 := by
  have h : ∃ x, f x ≠ 0 := by
    by_contra! h
    exact hf (LinearMap.ext h)
  obtain ⟨x, hx⟩ := h
  exact ⟨x, scalar_one hx⟩

/-- Different nonzero binary forms can be separated by a vector. -/
private theorem exists_one_zero {f g : V →ₗ[ZMod 2] ZMod 2}
    (hf : f ≠ 0) (hfg : f ≠ g) : ∃ x, f x = 1 ∧ g x = 0 := by
  by_contra! h
  have h1 (x : V) (hx : f x = 1) : g x = 1 := scalar_one (h x hx)
  obtain ⟨y, hy⟩ := exists_value_one hf
  have hgy := h1 y hy
  apply hfg
  ext x
  rcases binary_cases (f x) with hx | hx
  · rcases binary_cases (g x) with hgx | hgx
    · exact hx.trans hgx.symm
    · have hsum := h1 (x + y) (by simp [hx, hy])
      simp only [map_add, hgx, hgy] at hsum
      exact False.elim (by revert hsum; decide)
  · exact hx.trans (h1 x hx).symm

/-- Two transvections whose product is trivial or a transvection share a direction
or a form. -/
private theorem transvection_pair {v w : V} {f g : V →ₗ[ZMod 2] ZMod 2}
    (hv : v ≠ 0) (hw : w ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfv : f v = 0) (hgw : g w = 0)
    (hprod : transvection v f hfv * transvection w g hgw = 1 ∨
      IsTransvection (transvection v f hfv * transvection w g hgw)) :
    v = w ∨ f = g := by
  by_cases hfg : f = g
  · exact Or.inr hfg
  left
  obtain ⟨x, hfx, hgx⟩ := exists_one_zero hf hfg
  obtain ⟨y, hgy, hfy⟩ := exists_one_zero hg (Ne.symm hfg)
  have hx : (transvection v f hfv * transvection w g hgw) x = x + v := by
    change (x + g x • w) + f (x + g x • w) • v = x + v
    simp [hgx, hfx]
  have hy : (transvection v f hfv * transvection w g hgw) y =
      y + (w + f w • v) := by
    change (y + g y • w) + f (y + g y • w) • v = y + (w + f w • v)
    simp [hgy, hfy, add_assoc]
  rcases hprod with hprod | hprod
  · have hz : x + v = x := by simpa [hprod] using hx.symm
    exact False.elim (hv (add_eq_left.mp hz))
  · obtain ⟨u, k, _, _, hku, he⟩ := hprod
    have hx' : v = k x • u := by
      have h := hx
      rw [he] at h
      change x + k x • u = x + v at h
      exact (add_left_cancel h).symm
    have hkx : k x = 1 := by
      apply scalar_one
      intro hz
      exact hv (by simpa [hz] using hx')
    have hvu : v = u := by simpa [hkx] using hx'
    have hy' : w + f w • v = k y • v := by
      have h := hy
      rw [he] at h
      change y + k y • u = y + (w + f w • v) at h
      rw [← hvu] at h
      exact (add_left_cancel h).symm
    have hwv : w = (k y - f w) • v := by
      rw [sub_smul]
      exact eq_sub_iff_add_eq.mpr hy'
    rcases binary_cases (k y - f w) with hz | ho
    · exact False.elim (hw (by simpa [hz] using hwv))
    · simpa [ho] using hwv.symm

private theorem transvection_pair_of_mem (H : Subgroup (BinaryLinear.GL V))
    (hH : ∀ t ∈ H, t ≠ 1 → IsTransvection t)
    {v w : V} {f g : V →ₗ[ZMod 2] ZMod 2}
    (hv : v ≠ 0) (hw : w ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfv : f v = 0) (hgw : g w = 0)
    (hs : transvection v f hfv ∈ H) (ht : transvection w g hgw ∈ H) :
    v = w ∨ f = g := by
  apply transvection_pair hv hw hf hg hfv hgw
  by_cases he : transvection v f hfv * transvection w g hgw = 1
  · exact Or.inl he
  · exact Or.inr (hH _ (H.mul_mem hs ht) he)

/-- A binary transvection subgroup has a common image line or a common fixed
hyperplane. This proves containment, without a maximality assumption. -/
theorem transvectionSubgroup_le_point_or_hyperplane {n : ℕ} (hn : 2 ≤ n)
    (H : Subgroup (LinearGroup n)) (hH : ∀ t ∈ H, t ≠ 1 → IsTransvection t) :
    (∃ v : Space n, v ≠ 0 ∧ H ≤ pointRadical n v) ∨
    (∃ f : Space n →ₗ[ZMod 2] ZMod 2, f ≠ 0 ∧ H ≤ hyperplaneRadical n f) := by
  classical
  by_cases hH0 : H = ⊥
  · refine Or.inl ⟨fun _ => 1, ?_, hH0 ▸ bot_le⟩
    intro hz
    have h := congrFun hz (⟨0, by omega⟩ : Fin n)
    exact one_ne_zero h
  have hs : ∃ s ∈ H, s ≠ 1 := by
    by_contra! h
    apply hH0
    exact le_antisymm (fun t ht => Subgroup.mem_bot.mpr (h t ht)) bot_le
  obtain ⟨s, hs, hs1⟩ := hs
  obtain ⟨v, f, hv, hf, hfv, rfl⟩ := hH s hs hs1
  by_cases hpoint : H ≤ pointRadical n v
  · exact Or.inl ⟨v, hv, hpoint⟩
  have ht : ∃ t ∈ H, t ∉ pointRadical n v := by
    simpa only [SetLike.le_def, not_forall, Classical.not_imp, exists_prop] using hpoint
  obtain ⟨t, ht, htp⟩ := ht
  have ht1 : t ≠ 1 := by
    intro he
    subst t
    exact htp (pointRadical n v).one_mem
  obtain ⟨w, g, hw, hg, hgw, rfl⟩ := hH t ht ht1
  have hvw : v ≠ w := by
    intro he
    subst w
    exact htp (transvection_mem (Submodule.mem_span_singleton_self v)
      (Submodule.span_le.mpr (by simpa using hgw)))
  have hfg : f = g :=
    (transvection_pair_of_mem H hH hv hw hf hg hfv hgw hs ht).resolve_left hvw
  refine Or.inr ⟨f, hf, ?_⟩
  intro u hu
  by_cases hu1 : u = 1
  · exact hu1 ▸ (hyperplaneRadical n f).one_mem
  obtain ⟨z, k, hz, hk, hkz, rfl⟩ := hH u hu hu1
  have hfk : f = k := by
    rcases transvection_pair_of_mem H hH hv hz hf hk hfv hkz hs hu with hvz | hfk
    · have hwz : w ≠ z := by
        intro he
        exact hvw (hvz.trans he.symm)
      exact hfg.trans
        ((transvection_pair_of_mem H hH hw hz hg hk hgw hkz ht hu).resolve_left hwz)
    · exact hfk
  subst k
  exact transvection_mem (show z ∈ f.ker from hkz) le_rfl


private theorem duality_pairing_inv {n : ℕ} (g : LinearGroup n) (x y : Space n) :
    dotProduct (graphLinear n g x) y = dotProduct x (g⁻¹ y) := by
  simpa only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using
    graphLinear_dotProduct g x (g⁻¹ y)

private theorem duality_normal_pairing {n : ℕ}
    (f : Space n →ₗ[ZMod 2] ZMod 2) (x : Space n) :
    dotProduct (fun i => f (Pi.single i 1)) x = f x := by
  conv_rhs => rw [pi_eq_sum_univ' x]
  simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The annihilator of a hyperplane is its coordinate normal line. -/
private theorem duality_mem_normal_span {n : ℕ}
    (f : Space n →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) (z : Space n)
    (hz : ∀ x ∈ f.ker, dotProduct z x = 0) :
    z ∈ Submodule.span (ZMod 2) {fun i => f (Pi.single i 1)} := by
  have hu : ∃ u, f u ≠ 0 := by
    by_contra! h
    exact hf (LinearMap.ext h)
  obtain ⟨u, hu⟩ := hu
  have hu1 : f u = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hu
  have hpair (x : Space n) : dotProduct z x = f x * dotProduct z u := by
    have hx : x - f x • u ∈ f.ker := by
      change f (x - f x • u) = 0
      simp only [map_sub, map_smul, hu1, smul_eq_mul, mul_one, sub_self]
    have h := hz (x - f x • u) hx
    simpa only [dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_eq_zero] using h
  apply Submodule.mem_span_singleton.mpr
  refine ⟨dotProduct z u, ?_⟩
  ext i
  have h := hpair (Pi.single i 1)
  simpa only [dotProduct_single, mul_one, Pi.smul_apply, smul_eq_mul, mul_comm] using h.symm

private theorem duality_map_le {n : ℕ} (f : Space n →ₗ[ZMod 2] ZMod 2)
    (hf : f ≠ 0) :
    (hyperplaneRadical n f).map (graphLinear n).toMonoidHom ≤
      pointRadical n (fun i => f (Pi.single i 1)) := by
  rintro t ⟨s, hs, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom]
  have hsi := (hyperplaneRadical n f).inv_mem hs
  refine ⟨?_, ?_⟩
  · have hfix : graphLinear n s (fun i => f (Pi.single i 1)) =
        (fun i => f (Pi.single i 1)) := by
      have he (x : Space n) :
          dotProduct (graphLinear n s (fun i => f (Pi.single i 1))) x =
            dotProduct (fun i => f (Pi.single i 1)) x := by
        rw [duality_pairing_inv, duality_normal_pairing, duality_normal_pairing]
        have h := hsi.2 x
        change f (s⁻¹ x - x) = 0 at h
        exact sub_eq_zero.mp (by simpa only [map_sub] using h)
      funext i
      simpa only [dotProduct_single, mul_one] using he (Pi.single i 1)
    intro v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simpa only [map_smul] using congrArg (a • ·) hfix
  · intro x
    apply duality_mem_normal_span f hf
    intro z hz
    rw [sub_dotProduct, duality_pairing_inv, hsi.1 z hz, sub_self]

/-- Actual inverse transpose sends every hyperplane radical to a point radical. -/
theorem graph_hyperplaneRadical {n : ℕ} (hn : 2 ≤ n)
    (f : Space n →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) :
    ∃ w : Space n, w ≠ 0 ∧
      (hyperplaneRadical n f).map (graphLinear n).toMonoidHom = pointRadical n w := by
  let w : Space n := fun i => f (Pi.single i 1)
  have hw : w ≠ 0 := by
    intro hw0
    apply hf
    apply LinearMap.ext
    intro x
    change f x = 0
    rw [← duality_normal_pairing]
    change dotProduct w x = 0
    rw [hw0, zero_dotProduct]
  refine ⟨w, hw, ?_⟩
  have hker0 : f.ker ≠ ⊥ := by
    intro hker
    have hdim := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hker)
    have hdim' : n ≤ 1 := by simpa [Space] using hdim
    omega
  have hker1 : f.ker ≠ ⊤ := mt LinearMap.ker_eq_top.mp hf
  have hle := duality_map_le f hf
  apply le_antisymm hle
  intro t ht
  apply centralizer_map_radical_le f.ker hker0 hker1 (graphLinear n)
  exact Subgroup.mem_centralizer_iff.mpr
    (fun s hs => radical_commute (Submodule.span (ZMod 2) {w}) (hle hs) ht)


private theorem conj_mem_pointRadical {n : ℕ} (g : LinearGroup n) (v : Space n)
    {t : LinearGroup n} (ht : t ∈ pointRadical n v) :
    MulAut.conj g t ∈ pointRadical n (g v) := by
  refine ⟨?_, ?_⟩
  · intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    change g (t (g.symm (c • g v))) = c • g v
    rw [map_smul, LinearEquiv.symm_apply_apply, map_smul,
      ht.1 v (Submodule.mem_span_singleton_self v), map_smul]
  · intro w
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (ht.2 (g.symm w))
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    have h := congrArg g hc
    simpa only [map_smul, map_sub, LinearEquiv.apply_symm_apply, MulAut.conj_apply,
      LinearEquiv.mul_apply, LinearEquiv.coe_inv] using h

private theorem map_pointRadical_conj {n : ℕ} (g : LinearGroup n) (v : Space n) :
    (pointRadical n v).map (MulAut.conj g).toMonoidHom = pointRadical n (g v) := by
  apply le_antisymm
  · rintro t ⟨s, hs, rfl⟩
    exact conj_mem_pointRadical g v hs
  · intro t ht
    refine ⟨MulAut.conj g⁻¹ t, ?_, ?_⟩
    · change MulAut.conj g⁻¹ t ∈ pointRadical n v
      simpa only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using
        conj_mem_pointRadical g⁻¹ (g v) ht
    · simp [MulAut.conj_apply, mul_assoc]

private noncomputable def pointMap {n : ℕ} (a : MulAut (LinearGroup n))
    (ha : PreservesPointRadicals a) (v : Space n) : Space n :=
  if hv : v = 0 then 0 else (ha v hv).choose

private theorem pointMap_zero {n : ℕ} (a : MulAut (LinearGroup n))
    (ha : PreservesPointRadicals a) : pointMap a ha 0 = 0 := by
  simp [pointMap]

private theorem pointMap_spec {n : ℕ} (a : MulAut (LinearGroup n))
    (ha : PreservesPointRadicals a) {v : Space n} (hv : v ≠ 0) :
    pointMap a ha v ≠ 0 ∧
      (pointRadical n v).map a.toMonoidHom = pointRadical n (pointMap a ha v) := by
  simpa only [pointMap, dif_neg hv] using (ha v hv).choose_spec

private theorem pointMap_injective {n : ℕ} (a : MulAut (LinearGroup n))
    (ha : PreservesPointRadicals a) : Function.Injective (pointMap a ha) := by
  intro v w h
  by_cases hv : v = 0
  · subst v
    by_contra hw
    exact (pointMap_spec a ha (Ne.symm hw)).1 (h.symm.trans (pointMap_zero a ha))
  by_cases hw : w = 0
  · subst w
    exact False.elim ((pointMap_spec a ha hv).1 (h.trans (pointMap_zero a ha)))
  apply pointRadical_injective hv hw
  apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
  rw [(pointMap_spec a ha hv).2, (pointMap_spec a ha hw).2, h]

/-- Conjugation of radicals makes the induced vector map equivariant. -/
private theorem pointMap_equivariant {n : ℕ} (a : MulAut (LinearGroup n))
    (ha : PreservesPointRadicals a) (g : LinearGroup n) (v : Space n) :
    pointMap a ha (g v) = a g (pointMap a ha v) := by
  by_cases hv : v = 0
  · subst v
    simp [pointMap_zero]
  have hgv : g v ≠ 0 := fun h => hv (g.map_eq_zero_iff.mp h)
  have hfv := (pointMap_spec a ha hv).1
  apply pointRadical_injective (pointMap_spec a ha hgv).1
    (fun h => hfv ((a g).map_eq_zero_iff.mp h))
  calc
    pointRadical n (pointMap a ha (g v)) =
        (pointRadical n (g v)).map a.toMonoidHom := (pointMap_spec a ha hgv).2.symm
    _ = ((pointRadical n v).map a.toMonoidHom).map
        (MulAut.conj (a g)).toMonoidHom := by
      rw [← map_pointRadical_conj, Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext t
      simp [MulAut.conj_apply]
    _ = pointRadical n (a g (pointMap a ha v)) := by
      rw [(pointMap_spec a ha hv).2, map_pointRadical_conj]

private theorem binary_add_self {n : ℕ} (v : Space n) : v + v = 0 := by
  calc
    v + v = ((1 : ZMod 2) + 1) • v := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]

private theorem mem_binary_span_pair {n : ℕ} {x y z : Space n}
    (hz : z ∈ Submodule.span (ZMod 2) {x, y}) :
    z = 0 ∨ z = x ∨ z = y ∨ z = x + y := by
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hz
  have binary (c : ZMod 2) : c = 0 ∨ c = 1 :=
    (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
  rcases binary c with rfl | rfl <;> rcases binary d with rfl | rfl <;> simp

private theorem pointMap_add {n : ℕ} (a : MulAut (LinearGroup n))
    (ha : PreservesPointRadicals a) (x y : Space n) :
    pointMap a ha (x + y) = pointMap a ha x + pointMap a ha y := by
  by_cases hx : x = 0
  · subst x
    simp [pointMap_zero]
  by_cases hy : y = 0
  · subst y
    simp [pointMap_zero]
  by_cases hxy : x = y
  · subst y
    simp only [binary_add_self, pointMap_zero]
  let W := Submodule.span (ZMod 2) {pointMap a ha x, pointMap a ha y}
  have hfx : pointMap a ha x ∈ W := Submodule.subset_span (by simp)
  have hfy : pointMap a ha y ∈ W := Submodule.subset_span (by simp)
  have hW : W ≠ ⊥ := by
    intro h
    exact (pointMap_spec a ha hx).1 (by simpa only [h, Submodule.mem_bot] using hfx)
  -- Every element of the radical of W fixes both images. Its inverse image
  -- under a fixes x and y, hence x + y; equivariance then recovers W.
  have hsum : pointMap a ha (x + y) ∈ W := by
    apply (mem_iff_fixed_radical hW _).mpr
    intro g hg
    have hax : a.symm g x = x := by
      apply pointMap_injective a ha
      rw [pointMap_equivariant, a.apply_symm_apply, hg.1 _ hfx]
    have hay : a.symm g y = y := by
      apply pointMap_injective a ha
      rw [pointMap_equivariant, a.apply_symm_apply, hg.1 _ hfy]
    have h := pointMap_equivariant a ha (a.symm g) (x + y)
    simpa only [map_add, hax, hay, a.apply_symm_apply] using h.symm
  rcases mem_binary_span_pair hsum with hz | he | he | he
  · have h : x + y = 0 := pointMap_injective a ha (hz.trans (pointMap_zero a ha).symm)
    have h' := congrArg (fun z => z + y) h
    exact False.elim (hxy (by simpa only [add_assoc, binary_add_self, add_zero, zero_add] using h'))
  · exact False.elim (hy (add_eq_left.mp (pointMap_injective a ha he)))
  · exact False.elim (hx (add_eq_right.mp (pointMap_injective a ha he)))
  · exact he

/-- Point-radical preservation reconstructs an inner automorphism in any degree. -/
theorem eq_conj_of_preservesPointRadicals {n : ℕ} (a : MulAut (LinearGroup n))
    (ha : PreservesPointRadicals a) : ∃ g : LinearGroup n, a = MulAut.conj g := by
  let f : Space n →ₗ[ZMod 2] Space n :=
    { toFun := pointMap a ha
      map_add' := pointMap_add a ha
      map_smul' := by
        intro c v
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
        · simp [pointMap_zero]
        · simp }
  have hf : Function.Bijective f :=
    ⟨pointMap_injective a ha, Finite.surjective_of_injective (pointMap_injective a ha)⟩
  let g : LinearGroup n := LinearEquiv.ofBijective f hf
  refine ⟨g, ?_⟩
  apply MulEquiv.ext
  intro t
  apply LinearEquiv.ext
  intro v
  obtain ⟨w, rfl⟩ := g.surjective v
  change a t (g w) = g (t (g.symm (g w)))
  rw [LinearEquiv.symm_apply_apply]
  exact (pointMap_equivariant a ha t w).symm


/-- Every binary linear automorphism in dimension at least two is inner or
inverse transpose composed with an inner automorphism. -/
theorem inner_graph {n : ℕ} (hn : 2 ≤ n) (a : MulAut (LinearGroup n)) :
    ∃ g : LinearGroup n, a = MulAut.conj g ∨ a = graphLinear n * MulAut.conj g :=
  inner_graph_of_point_geometry
    (preservesPointRadicals_or_graph_of_transvection_geometry hn
      (transvectionSubgroup_le_point_or_hyperplane hn) (graph_hyperplaneRadical hn))
    eq_conj_of_preservesPointRadicals a

/-- An actual outer automorphism has the graph formula, without a degree ceiling. -/
theorem outer_eq_graph_inner {n : ℕ} (hn : 2 ≤ n) (a : MulAut (LinearGroup n))
    (ha : a ∉ MulAut.innerSubgroup _) :
    ∃ g : LinearGroup n, a = graphLinear n * MulAut.conj g := by
  obtain ⟨g, hi | hg⟩ := inner_graph hn a
  · exact (ha ⟨g, hi.symm⟩).elim
  · exact ⟨g, hg⟩

end BinaryLinear.ElementaryOuterSylow
