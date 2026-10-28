module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.GlobalRelations

/-!
# BorelCollection

The angular order separates either simple root on the right. Torus and signed Weyl equations then reduce reflection times Borel to Borel times reflection times its simple root.

Source: GLS3 2.3.5--8 and Table 2.4; Steinberg, section 11, Lemmas 62--64.
The source fields, local equations and exhaustive row selection remain source
producer obligations; binary type tags do not supply these data.
-/

@[expose] public noncomputable section

namespace ReeF4.RootPresentationRecognition.Global.Data
open Subgroup Theory.GroupTheory OrderedRootPresentation
open SignedGeometry WeylPresentation CentralCovers.TwoPrimary
variable {m : ℕ} {G : Type*} [Group G] (d : Global.Data m G) (R : d.Relations)
open scoped Pointwise

def unipotent : Subgroup G := join (AngularPresentation.Parameter m) (d.x true) sourceOrder
def borel : Subgroup G := d.unipotent ⊔ d.h.range

theorem root_mem_unipotent (i : PositiveTables.Root) (a : AngularPresentation.Parameter m i) :
    d.x true i a ∈ d.unipotent :=
  range_le_join _ _ sourceOrder (mem_sourceOrder i) ⟨a,rfl⟩

theorem root_mem_borel (i : PositiveTables.Root) (a : AngularPresentation.Parameter m i) :
    d.x true i a ∈ d.borel := mem_sup_left (d.root_mem_unipotent i a)

theorem torus_mem_borel (t : Parabolics.fixedTorus m) : d.h t ∈ d.borel :=
  mem_sup_right ⟨t,rfl⟩

include R in
/-- Torus/root equations imply normalization of the whole positive subgroup. -/
theorem torus_normalizes : d.h.range ≤ normalizer d.unipotent := by
  rw [le_normalizer_iff]
  rintro _ ⟨t,rfl⟩ u hu
  have hle : d.unipotent ≤ d.unipotent.comap (MulAut.conj (d.h t)).toMonoidHom := by
    apply join_le
    intro i _
    rintro _ ⟨a,rfl⟩
    change d.h t * d.x true i a * (d.h t)⁻¹ ∈ d.unipotent
    rw [R.torus_root]
    exact d.root_mem_unipotent _ _
  exact hle hu

include R in
/-- Borel existence follows from the local equations, without any faithfulness premise. -/
theorem mem_borel_iff (b : G) : b ∈ d.borel ↔
    ∃ t : Parabolics.fixedTorus m, ∃ u ∈ d.unipotent, b = d.h t * u := by
  have he := coe_mul_of_left_le_normalizer_right d.h.range d.unipotent (d.torus_normalizes R)
  change b ∈ d.unipotent ⊔ d.h.range ↔ _
  rw [sup_comm, ← SetLike.mem_coe, he]
  constructor
  · rintro ⟨_,⟨t,rfl⟩,u,hu,rfl⟩
    exact ⟨t,u,hu,rfl⟩
  · rintro ⟨t,u,hu,rfl⟩
    exact ⟨_,⟨t,rfl⟩,u,hu,rfl⟩

/-- The seven nonsimple factors for a chosen reflection. -/
def rest (s : Bool) : Subgroup G :=
  join (AngularPresentation.Parameter m) (d.x true)
    (sourceOrder.filter (fun i => i ≠ SignedCharts.simpleIndex s))

private theorem word_last (l : List PositiveTables.Root) (i : PositiveTables.Root)
    (p : Tuple (AngularPresentation.Parameter m) (l ++ [i])) :
    ∃ u ∈ join (AngularPresentation.Parameter m) (d.x true) l,
    ∃ a : AngularPresentation.Parameter m i,
      word (AngularPresentation.Parameter m) (fun i => d.x true i) (l ++ [i]) p =
        u * d.x true i a := by
  induction l with
  | nil => exact ⟨1,one_mem _,p.1,by simp [word]⟩
  | cons j l ih =>
    obtain ⟨u,hu,a,he⟩ := ih p.2
    refine ⟨d.x true j p.1 * u, mul_mem_sup (show d.x true j p.1 ∈ (d.x true j).range from ⟨_,rfl⟩) hu,a,?_⟩
    change d.x true j p.1 * word _ _ (l ++ [i]) p.2 = _
    rw [he,mul_assoc]

include R in
/-- Separating either simple factor uses the actual angular order. The first
factor is moved to the right by collecting the inverse word. -/
theorem unipotent_right_simple (s : Bool) (u : G) (hu : u ∈ d.unipotent) :
    ∃ c ∈ d.rest s, ∃ a : AngularPresentation.Parameter m (SignedCharts.simpleIndex s),
      u = c * d.simpleRoot s a := by
  cases s
  · have hp := R.positive.exists_word (AngularPresentation.table m)
      AngularPresentation.order_nodup u hu
    have ho : sourceOrder =
        sourceOrder.filter (fun i => i ≠ SignedCharts.simpleIndex false) ++ [.inl 0] := by decide
    rw [ho] at hp
    obtain ⟨p,hp⟩ := hp
    obtain ⟨c,hc,a,he⟩ := d.word_last _ _ p
    exact ⟨c,hc,a,hp.symm.trans he⟩
  · have hp := R.positive.exists_word (AngularPresentation.table m)
      AngularPresentation.order_nodup u⁻¹ (inv_mem hu)
    have ho : sourceOrder = .inr 0 ::
        sourceOrder.filter (fun i => i ≠ SignedCharts.simpleIndex true) := by decide
    rw [ho] at hp
    obtain ⟨p,hp⟩ := hp
    refine ⟨(word _ (fun i => d.x true i) _ p.2)⁻¹,
      inv_mem (word_mem_join _ _ _ _),p.1⁻¹,?_⟩
    change d.x true (.inr 0) p.1 * word _ (fun i => d.x true i) _ p.2 = u⁻¹ at hp
    apply inv_injective
    simpa only [mul_inv_rev,inv_inv,map_inv] using hp.symm

include R in
/-- Every nonsimple positive root stays positive under the chosen reflection. -/
theorem reflection_other (s : Bool) (i : PositiveTables.Root)
    (hi : i ≠ SignedCharts.simpleIndex s) (a : AngularPresentation.Parameter m i) :
    d.reflection s * d.x true i a * (d.reflection s)⁻¹ ∈ d.unipotent := by
  obtain ⟨v,rfl⟩ := (PositiveTables.rootChartEquiv m i).surjective a
  cases i with
  | inl i =>
    change CoefficientField m at v
    change d.reflection s * d.pair (true,i) v * (d.reflection s)⁻¹ ∈ _
    rw [R.pair]
    have hp : (step false s (true,i)).1 = true := by
      apply (step_positive_iff false s i).mpr
      cases s
      · exact Or.inr (fun h => hi (by subst i; rfl))
      · exact Or.inl (by decide)
    change d.x (step false s (true,i)).1 (.inl (step false s (true,i)).2) _ ∈ _
    rw [hp]
    exact d.root_mem_unipotent _ _
  | inr i =>
    change CoefficientField m × CoefficientField m at v
    change d.reflection s * d.quartet (true,i) v.1 v.2 * (d.reflection s)⁻¹ ∈ _
    rw [R.quartet]
    have hp : (step true s (true,i)).1 = true := by
      apply (step_positive_iff true s i).mpr
      cases s
      · exact Or.inl (by decide)
      · exact Or.inr (fun h => hi (by subst i; rfl))
    change d.x (step true s (true,i)).1 (.inr (step true s (true,i)).2) _ ∈ _
    rw [hp]
    exact d.root_mem_unipotent _ _

include R in
theorem reflection_rest (s : Bool) {c : G} (hc : c ∈ d.rest s) :
    d.reflection s * c * (d.reflection s)⁻¹ ∈ d.unipotent := by
  have hle : d.rest s ≤ d.unipotent.comap (MulAut.conj (d.reflection s)).toMonoidHom := by
    apply join_le
    intro i hi
    rintro _ ⟨a,rfl⟩
    exact d.reflection_other R s i (of_decide_eq_true (List.mem_filter.mp hi).2) a
  exact hle hc

include R in
/-- Multiplication of a full Borel element by a reflection leaves only its
own simple root on the right of that reflection. -/
theorem reflection_borel (s : Bool) (b : G) (hb : b ∈ d.borel) :
    ∃ c ∈ d.borel, ∃ a : AngularPresentation.Parameter m (SignedCharts.simpleIndex s),
      d.reflection s * b = c * d.reflection s * d.simpleRoot s a := by
  obtain ⟨t,u,hu,rfl⟩ := (d.mem_borel_iff R b).mp hb
  obtain ⟨v,hv,a,rfl⟩ := d.unipotent_right_simple R s u hu
  refine ⟨d.h (NormalizerPresentation.action m (simple s) t) *
    (d.reflection s * v * (d.reflection s)⁻¹),
    mul_mem (d.torus_mem_borel _) (mem_sup_left (d.reflection_rest R s hv)),a,?_⟩
  rw [← R.weyl_torus]
  group

include R in
/-- The complete ascending table, including the two-parameter Suzuki root. -/
theorem ascent (s : Bool) (k : Fin 8)
    (a : AngularPresentation.Parameter m (SignedCharts.simpleIndex s)) :
    (d.n (alternating (!s) k))⁻¹ * d.simpleRoot s a * d.n (alternating (!s) k) ∈ d.borel := by
  obtain ⟨v,rfl⟩ := (PositiveTables.rootChartEquiv m (SignedCharts.simpleIndex s)).surjective a
  cases s
  · exact ascent_mem false d.n d.pair R.pair d.borel
      (fun i a => d.root_mem_borel (.inl i) _) k v
  · exact ascent_mem true d.n (fun r (v : CoefficientField m × CoefficientField m) => d.quartet r v.1 v.2)
      (fun s r v => R.quartet s r v.1 v.2) d.borel
      (fun i a => d.root_mem_borel (.inr i) _) k v

end ReeF4.RootPresentationRecognition.Global.Data
