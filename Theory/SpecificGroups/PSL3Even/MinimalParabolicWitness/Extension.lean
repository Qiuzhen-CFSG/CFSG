module

public import Theory.SpecificGroups.PSL3Even.MinimalParabolicWitness.Diagram
public import Theory.Order.UniqueMaximalOver

/-!
# The Borel in a minimal parabolic extension of PSL₃

For a normal copy K of PSL₃ in H=KT, mark T∩K as the standard Sylow.
The Sylow normalizer is proper and contains T, so it lies in the unique
maximal overgroup M. If every element of T fixed the diagram, both proper
parabolic products with T would lie in M and generate H. Thus some element
exchanges the nodes. The preceding geometric calculation then forces M∩K
to be exactly the original marked Borel.

Source: Aschbacher--Smith, E.2.2, printed pp.215--216.
-/

public section
open scoped MatrixGroups Pointwise
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3.LinearThree.OuterExtensions
namespace Matrix.PSL3Even.MinimalParabolicWitness
variable {H : Type*} [Group H] [Finite H]
variable (F : Type*) [Field F] [Finite F]
variable (K : Subgroup H) [K.Normal] (e : K ≃* PSL(3,F))

/-- The original normal subgroup embedded through its marked matrix model. -/
@[expose] noncomputable def modelEmbedding : PSL(3,F) →* H := K.subtype.comp e.symm.toMonoidHom

/-- The action is the actual conjugation action on the original normal subgroup. -/
@[expose] noncomputable def modelAction : H →* MulAut PSL(3,F) :=
  (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : H →* MulAut K)

omit [Finite H] [Finite F] [K.Normal] in
theorem modelEmbedding_injective : Function.Injective (modelEmbedding F K e) :=
  K.subtype_injective.comp e.symm.injective

omit [Finite H] [Finite F] [K.Normal] in
@[simp] theorem modelEmbedding_range : (modelEmbedding F K e).range = K := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩; exact (e.symm y).property
  · intro hx; exact ⟨e ⟨x,hx⟩, by simp [modelEmbedding]⟩

omit [Finite H] [Finite F] in
theorem modelEmbedding_action (h : H) (x : PSL(3,F)) :
    modelEmbedding F K e (modelAction F K e h x) =
      MulAut.conj h (modelEmbedding F K e x) := by
  simp [modelEmbedding, modelAction, MulAut.congr_apply, MulAut.conjNormal_apply,
    MulAut.conj_apply]

omit [Finite H] [Finite F] in
theorem map_modelAction (D : Subgroup PSL(3,F)) (h : H) :
    (D.map (modelAction F K e h).toMonoidHom).map (modelEmbedding F K e) =
      (D.map (modelEmbedding F K e)).map (MulAut.conj h).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  exact modelEmbedding_action F K e h x

omit [Finite H] [Finite F] in
private theorem preserves_comap (D : Subgroup H) (h : H)
    (hd : h ∈ normalizer (D : Set H)) :
    (D.comap (modelEmbedding F K e)).map (modelAction F K e h).toMonoidHom =
      D.comap (modelEmbedding F K e) := by
  apply Subgroup.map_injective (modelEmbedding_injective F K e)
  rw [map_modelAction, map_comap_eq, modelEmbedding_range]
  exact mem_normalizer_iff_map_conj_eq.mp
    (inf_normalizer_le_normalizer_inf ⟨show h ∈ normalizer (K : Set H) from (by rw [normalizer_eq_top]; trivial), hd⟩)

omit [Finite H] [K.Normal] in
private theorem proper_product (T A : Subgroup H) (hAK : A ≤ K)
    (hI : K ⊓ T ≤ A) (hn : T ≤ normalizer (A : Set H)) (hA : ¬ K ≤ A) :
    A ⊔ T ≠ ⊤ := by
  intro he
  apply hA
  intro x hx
  have hm : x ∈ (A : Set H) * (T : Set H) := by
    rw [← coe_mul_of_right_le_normalizer_left A T hn, he]
    trivial
  obtain ⟨a,ha,t,ht,hat⟩ := hm
  have htK : t ∈ K := by
    have hh := K.mul_mem (K.inv_mem (hAK ha)) hx
    rwa [← hat, inv_mul_cancel_left] at hh
  rw [← hat]
  exact A.mul_mem ha (hI ⟨htK,ht⟩)

variable {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)

/-- Unique maximality derives a nontrivial diagram action and the exact original
Borel intersection; neither is a hypothesis. -/
theorem diagram_and_borel (T M : Subgroup H) (hgen : K ⊔ T = ⊤)
    (hU : T.comap (modelEmbedding F K e) = unipotent F)
    (hunique : Order.HasUniqueMaximalOver T ⊤)
    (hM : T ≤ M ∧ IsCoatom M) :
    (∃ t ∈ T, diagramAction F hn hF (modelAction F K e t) ≠ 1) ∧
      M.comap (modelEmbedding F K e) = borel F := by
  let f := modelEmbedding F K e
  have hf : Function.Injective f := modelEmbedding_injective F K e
  have hfr : f.range = K := modelEmbedding_range F K e
  have hUM : (unipotent F).map f = T ⊓ K := by
    rw [← hU, map_comap_eq, hfr, inf_comm]
  have hpres (t : H) (ht : t ∈ T) :
      (unipotent F).map (modelAction F K e t).toMonoidHom = unipotent F := by
    rw [← hU]
    exact preserves_comap F K e T t (T.le_normalizer ht)
  have hbound (D : Subgroup H) (hTD : T ≤ D) (hD : D ≠ ⊤) : D ≤ M :=
    hunique.le_maximal ⟨hM.1,hM.2.covBy_top⟩ hTD (lt_top_iff_ne_top.mpr hD)
  have hKnot : ¬ K ≤ M := by
    intro h
    exact hM.2.ne_top (top_unique (hgen ▸ sup_le h hM.1))
  have hproper : M.comap f ≠ ⊤ := by
    intro h
    apply hKnot
    rw [← hfr]
    rintro x ⟨y,rfl⟩
    exact show y ∈ M.comap f from h ▸ mem_top y
  have hN : normalizer ((unipotent F).map f : Set H) ≤ M := by
    apply hbound
    · rw [hUM]
      exact le_inf (T.le_normalizer) (le_normalizer_of_normal : T ≤ normalizer (K : Set H)) |>.trans inf_normalizer_le_normalizer_inf
    · intro he
      have hh := congrArg (comap f) he
      rw [comap_normalizer_eq_of_le_range ((unipotent F).map_le_range f),
        comap_map_eq_self_of_injective hf, comap_top, normalizer_unipotent F hn hF] at hh
      exact parabolic_ne_top F true (top_unique (hh ▸ borel_le_parabolic F true))
  have hB : borel F ≤ M.comap f := by
    apply map_le_iff_le_comap.mp
    have hh : (borel F).map f ≤ normalizer ((unipotent F).map f : Set H) := by
      rw [← normalizer_unipotent F hn hF]
      exact (unipotent F).le_normalizer_map f
    exact hh.trans hN
  have hswap : ∃ t ∈ T, diagramAction F hn hF (modelAction F K e t) ≠ 1 := by
    by_contra! hall
    have hP (b : Bool) : (parabolic F b).map f ≤ M := by
      have hnorm : T ≤ normalizer ((parabolic F b).map f : Set H) := by
        intro t ht
        apply mem_normalizer_iff_map_conj_eq.mpr
        change ((parabolic F b).map (modelEmbedding F K e)).map
          (MulAut.conj t).toMonoidHom = _
        rw [← map_modelAction, map_parabolic_of_preserves_unipotent F hn hF _ (hpres t ht),
          hall t ht, Equiv.Perm.one_apply]
      have hpK : (parabolic F b).map f ≤ K := by rw [← hfr]; exact map_le_range _ _
      have hI : K ⊓ T ≤ (parabolic F b).map f := by
        rw [inf_comm, ← hUM]
        exact map_mono ((unipotent_le_borel F).trans (borel_le_parabolic F b))
      have hproperP : ¬ K ≤ (parabolic F b).map f := by
        intro h
        apply parabolic_ne_top F b
        apply top_unique
        intro x _
        obtain ⟨y,hy,he⟩ := h (hfr ▸ show f x ∈ f.range from ⟨x,rfl⟩)
        exact (hf he) ▸ hy
      exact le_sup_left.trans (hbound _ le_sup_right
        (proper_product K T _ hpK hI hnorm hproperP))
    apply hKnot
    rw [← hfr, MonoidHom.range_eq_map, ← parabolics_sup_eq_top F, Subgroup.map_sup]
    exact sup_le (hP true) (hP false)
  refine ⟨hswap, ?_⟩
  obtain ⟨t,ht,hs⟩ := hswap
  exact eq_borel_of_swapping_actor F hn hF _ (hpres t ht) hs _ hB hproper
    (preserves_comap F K e M t (M.le_normalizer (hM.1 ht)))

end Matrix.PSL3Even.MinimalParabolicWitness
