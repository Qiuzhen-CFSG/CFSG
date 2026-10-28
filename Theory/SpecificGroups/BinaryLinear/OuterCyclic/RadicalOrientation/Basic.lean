module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Geometry

/-!
# Radicals and the characteristic set of binary transvections

Every nonidentity element of a point radical is a rank-one transvection.
Automorphisms therefore carry point radicals to subgroups consisting of the
identity and transvections. The centralizer calculation for radicals shows
that containment of such an image in any radical is already equality.

Point radicals form one conjugacy class. Consequently an automorphism that
carries one point radical to a point radical preserves the entire family;
this step needs no reconstruction of the incidence graph.

These are elementary geometric ingredients for the binary specialization
of GLS3, Theorem 2.5.12(b–e,i) and §2.7, especially the matrix formulas in
`refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115. They do not assert the
common-image/common-kernel classification of transvection subgroups or the
action of inverse transpose on hyperplane radicals.
-/

@[expose] public section

namespace BinaryLinear.OuterCyclic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The radical fixing a linear hyperplane pointwise. -/
def hyperplaneRadical (n : ℕ) (f : Space n →ₗ[ZMod 2] ZMod 2) :
    Subgroup (LinearGroup n) := radical f.ker

/-- Every nonidentity element of a point radical is a transvection. -/
theorem pointRadical_isTransvection {n : ℕ} {v : Space n} (hv : v ≠ 0)
    {t : LinearGroup n} (ht : t ∈ pointRadical n v) (ht1 : t ≠ 1) :
    IsTransvection t := by
  let d : Space n →ₗ[ZMod 2] Space n := t.toLinearMap - LinearMap.id
  let c : Space n →ₗ[ZMod 2] Submodule.span (ZMod 2) {v} :=
    d.codRestrict _ ht.2
  let f : Space n →ₗ[ZMod 2] ZMod 2 :=
    (LinearEquiv.coord (ZMod 2) (Space n) v hv).toLinearMap.comp c
  have hfd (x : Space n) : f x • v = t x - x :=
    LinearEquiv.coord_apply_smul (ZMod 2) (Space n) v hv (c x)
  have hfv : f v = 0 := by
    have h := hfd v
    rw [ht.1 v (Submodule.mem_span_singleton_self v), sub_self] at h
    exact (smul_eq_zero.mp h).resolve_right hv
  have he : t = transvection v f hfv := by
    apply LinearEquiv.ext
    intro x
    change t x = x + f x • v
    rw [hfd]
    abel
  have hf : f ≠ 0 := by
    intro hf0
    apply ht1
    rw [he]
    apply LinearEquiv.ext
    intro x
    change x + f x • v = x
    simp [hf0]
  exact ⟨v, f, hv, hf, hfv, he⟩

/-- The characteristic-transvection theorem applies to the entire image radical. -/
theorem map_pointRadical_isTransvection {n : ℕ} (hn : 2 ≤ n)
    (a : MulAut (LinearGroup n)) {v : Space n} (hv : v ≠ 0)
    {t : LinearGroup n} (ht : t ∈ (pointRadical n v).map a.toMonoidHom)
    (ht1 : t ≠ 1) : IsTransvection t := by
  obtain ⟨s, hs, rfl⟩ := ht
  exact (isTransvection_map_linear hn a s).mpr
    (pointRadical_isTransvection hv hs (fun h => ht1 (by simp [h])))

/-- Binary transvections are involutions. -/
theorem IsTransvection.inv_eq_self {t : BinaryLinear.GL V} (ht : IsTransvection t) :
    t⁻¹ = t := by
  obtain ⟨w, f, _, _, hfw, rfl⟩ := ht
  rfl

/-- A subgroup consisting of the identity and transvections is commutative. -/
theorem transvectionSubgroup_commute (H : Subgroup (BinaryLinear.GL V))
    (hH : ∀ t ∈ H, t ≠ 1 → IsTransvection t)
    {s t : BinaryLinear.GL V} (hs : s ∈ H) (ht : t ∈ H) : s * t = t * s := by
  have hinv (u : BinaryLinear.GL V) (hu : u ∈ H) : u⁻¹ = u := by
    by_cases hu1 : u = 1
    · simp [hu1]
    · exact (hH u hu hu1).inv_eq_self
  have h := mul_inv_rev s t
  rwa [hinv (s * t) (H.mul_mem hs ht), hinv t ht, hinv s hs] at h

/-- Any two elements of a block-unipotent radical commute. -/
theorem radical_commute (W : Submodule (ZMod 2) V) {s t : BinaryLinear.GL V}
    (hs : s ∈ radical W) (ht : t ∈ radical W) : s * t = t * s := by
  ext x
  have hsx := hs.1 (t x - x) (ht.2 x)
  have htx := ht.1 (s x - x) (hs.2 x)
  simp only [map_sub] at hsx htx
  change s (t x) = t (s x)
  calc
    s (t x) = (t x - x) + s x := (sub_eq_iff_eq_add.mp hsx)
    _ = (s x - x) + t x := by abel
    _ = t (s x) := (sub_eq_iff_eq_add.mp htx).symm

/-- An automorphic image of a nondegenerate radical is self-centralizing. -/
theorem centralizer_map_radical_le (W : Submodule (ZMod 2) V)
    (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) (a : MulAut (BinaryLinear.GL V)) :
    Subgroup.centralizer ((radical W).map a.toMonoidHom : Set (BinaryLinear.GL V)) ≤
      (radical W).map a.toMonoidHom := by
  intro t ht
  refine ⟨a.symm t, centralizer_radical_le hW0 hW1 ?_, a.apply_symm_apply t⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro s hs
  apply a.injective
  simpa only [map_mul, a.apply_symm_apply] using
    (Subgroup.mem_centralizer_iff.mp ht) (a s) ⟨s, hs, rfl⟩

/-- Containment in another radical is equality for an image of a point radical. -/
theorem map_pointRadical_eq_of_le_radical {n : ℕ} (hn : 2 ≤ n)
    (a : MulAut (LinearGroup n)) {v : Space n} (hv : v ≠ 0)
    (W : Submodule (ZMod 2) (Space n))
    (h : (pointRadical n v).map a.toMonoidHom ≤ radical W) :
    (pointRadical n v).map a.toMonoidHom = radical W := by
  have hV0 : Submodule.span (ZMod 2) {v} ≠ ⊥ :=
    mt Submodule.span_singleton_eq_bot.mp hv
  have hV1 : Submodule.span (ZMod 2) {v} ≠ ⊤ := by
    intro he
    have hd := finrank_span_singleton (K := ZMod 2) hv
    rw [he, finrank_top] at hd
    have hn1 : n = 1 := by simpa [Space] using hd
    omega
  apply le_antisymm h
  intro t ht
  apply centralizer_map_radical_le _ hV0 hV1 a
  exact Subgroup.mem_centralizer_iff.mpr (fun s hs => radical_commute W (h hs) ht)

/-- Linear conjugation transports the radical of a subspace to its image. -/
theorem radical_map_conj (g : BinaryLinear.GL V) (W : Submodule (ZMod 2) V) :
    (radical W).map (MulAut.conj g).toMonoidHom = radical (W.map g.toLinearMap) := by
  have forward (e : BinaryLinear.GL V) (U : Submodule (ZMod 2) V) :
      (radical U).map (MulAut.conj e).toMonoidHom ≤ radical (U.map e.toLinearMap) := by
    rintro t ⟨s, hs, rfl⟩
    refine ⟨?_, ?_⟩
    · rintro w ⟨u, hu, rfl⟩
      change e (s (e.symm (e u))) = e u
      rw [e.symm_apply_apply, hs.1 u hu]
    · intro x
      refine ⟨s (e.symm x) - e.symm x, hs.2 _, ?_⟩
      simp only [LinearEquiv.coe_coe, map_sub, e.apply_symm_apply]
      rfl
  apply le_antisymm (forward g W)
  intro t ht
  refine ⟨(MulAut.conj g.symm) t, ?_, ?_⟩
  · have h := forward g.symm (W.map g.toLinearMap) ⟨t, ht, rfl⟩
    simpa only [← Submodule.map_comp, g.symm_comp, Submodule.map_id,
      MulEquiv.coe_toMonoidHom, SetLike.mem_coe] using h
  · change g * (g.symm * t * g.symm⁻¹) * g⁻¹ = t
    change g * (g⁻¹ * t * (g⁻¹)⁻¹) * g⁻¹ = t
    group

/-- Conjugation acts on point radicals by its natural action on vectors. -/
theorem pointRadical_map_conj {n : ℕ} (g : LinearGroup n) (v : Space n) :
    (pointRadical n v).map (MulAut.conj g).toMonoidHom = pointRadical n (g v) := by
  simpa only [pointRadical, Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe] using
    radical_map_conj g (Submodule.span (ZMod 2) {v})

/-- The linear group acts transitively on nonzero binary vectors. -/
theorem exists_linearEquiv_apply_eq [FiniteDimensional (ZMod 2) V]
    {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : BinaryLinear.GL V, g v = w := by
  let d := (LinearEquiv.coord (ZMod 2) V v hv).trans
    (LinearEquiv.coord (ZMod 2) V w hw).symm
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq d
  refine ⟨g, ?_⟩
  have h := hg ⟨v, Submodule.mem_span_singleton_self v⟩
  have hd : d ⟨v, Submodule.mem_span_singleton_self v⟩ =
      ⟨w, Submodule.mem_span_singleton_self w⟩ := by
    apply (LinearEquiv.coord (ZMod 2) V w hw).injective
    simp [d, LinearEquiv.coord_self]
  rw [hd] at h
  exact h.symm

/-- Automorphisms intertwine conjugation and hence subgroup conjugation. -/
theorem map_conj_map {G : Type*} [Group G] (a : MulAut G) (g : G) (H : Subgroup G) :
    (H.map (MulAut.conj g).toMonoidHom).map a.toMonoidHom =
      (H.map a.toMonoidHom).map (MulAut.conj (a g)).toMonoidHom := by
  simp only [Subgroup.map_map]
  congr 1
  ext x
  exact map_mul a (g * x) g⁻¹ |>.trans (by simp)

/-- One point-radical image determines the orientation of the whole conjugacy class. -/
theorem preservesPointRadicals_of_one {n : ℕ} (a : MulAut (LinearGroup n))
    {v w : Space n} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : (pointRadical n v).map a.toMonoidHom = pointRadical n w) :
    PreservesPointRadicals a := by
  intro u hu
  obtain ⟨g, hg⟩ := exists_linearEquiv_apply_eq hv hu
  refine ⟨(a g) w, fun hz => hw ((a g).map_eq_zero_iff.mp hz), ?_⟩
  rw [← hg, ← pointRadical_map_conj, map_conj_map, h, pointRadical_map_conj]

end BinaryLinear.OuterCyclic
