module
public import Theory.GroupTheory.MarkedInnerStrongClosure.OmegaAction
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.InnerAction.Models
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ProjectedComponent

/-!
# Whole-U inner action on the selected Bender component

The actual Sylow S of H meets its subnormal component L in a Sylow P.
The original inner action of z has a nonidentity involutory implementer t
in P. Transitivity on the nonidentity elements of Ω₁(P), and its order
greater than two, put that whole omega into U by cancelling the common
centralizing factor of returning z-conjugates.

The proved component normalization and U≤S give Sylow stability. Elementarity
and strong closure supply omega fixation and square-one displacements. The
complete Bender-model criterion then proves every U actor inner, and its
implementer lies in Ω₁(P). This constructs both implementer directions for
the existing projected-component consumer, retaining its full normalizer
action image and every source maximality/balance hypothesis.

Source: Aschbacher--Smith, Proposition 2.2.2, printed pp.519--520, combined
manuscript of 1 March 2004. The earlier owner still selects the model and
supplies the marked z-action, Sylow placement, O(H)=1, and the actual model
normalizer facts. I.3.2 balance remains with its existing source owner.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- The first omega of the literal ambient component Sylow intersection. -/
@[expose] def componentOmega (H L : Subgroup G) (S : Sylow 2 H) : Subgroup G :=
  omegaOneAmbient ((S : Subgroup H).map H.subtype ⊓ L)

private theorem component_sylow (H L : Subgroup G) (S : Sylow 2 H)
    (hL : IsComponentIn L H) :
    ∃ P : Sylow 2 L, (P : Subgroup L) =
      ((S : Subgroup H).map H.subtype).subgroupOf L := by
  obtain ⟨P0, hP0⟩ := S.exists_subgroupOf_eq_of_subnormal (L.subgroupOf H) hL.2.1
  let e := subgroupOfEquivOfLe hL.1
  refine ⟨P0.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyS : (y : H) ∈ (S : Subgroup H) := by
      change y ∈ (S : Subgroup H).subgroupOf (L.subgroupOf H)
      rw [← hP0]
      exact hy
    exact mem_map_of_mem H.subtype hyS
  · rintro ⟨y, hy, he⟩
    change (y : G) = (x : G) at he
    let y0 : L.subgroupOf H := ⟨y, by change (y : G) ∈ L; rw [he]; exact x.property⟩
    refine ⟨y0, ?_, Subtype.ext he⟩
    change y0 ∈ (P0 : Subgroup (L.subgroupOf H))
    rw [hP0]
    exact hy

omit [Finite G] in
private theorem centerless_of_disjoint (L : Subgroup G)
    (hdis : Disjoint L (centralizer (L : Set G))) : center L = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply Subtype.ext
  exact hdis.le_bot ⟨x.property, fun y hy =>
    congrArg Subtype.val (mem_center_iff.mp hx (⟨y, hy⟩ : L))⟩

/-- The model's square-displacement implication supplies both actual inner
implementer directions, after constructing every local action hypothesis. -/
theorem LocalControlWitness.inner_omega_action_of_criterion
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hdis : Disjoint L (centralizer (L : Set G)))
    (hzin : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹)
    (hcriterion : MarkedInnerStrongClosure.SquareDisplacementInner L)
    (hsize : 2 < Nat.card (componentOmega H L S))
    (htrans : ∀ a ∈ componentOmega H L S, a ≠ 1 →
      ∀ b ∈ componentOmega H L S, b ≠ 1 →
      ∃ n ∈ L ⊓ normalizer (componentOmega H L S : Set G), n * a * n⁻¹ = b) :
    (∀ u : w.U, ∃ q : componentOmega H L S,
      (u : G) * (q : G)⁻¹ ∈ centralizer (L : Set G)) ∧
    (∀ q : componentOmega H L S, ∃ u : w.U,
      (u : G) * (q : G)⁻¹ ∈ centralizer (L : Set G)) := by
  let : IsElementaryAbelian 2 w.U := w.elementary
  let S' : Subgroup G := (S : Subgroup H).map H.subtype
  have hU : IsStronglyClosedSet (w.U : Set G) S' ⊤ :=
    ⟨hUS, fun x hx g hg hgs => w.strongly_closed.2 x hx g hg (hST hgs)⟩
  have hUL := w.normalizes_component_of_oddCore_eq_bot H S hUS hST hcore L hL
  obtain ⟨P, hP⟩ := component_sylow H L S hL
  have hPm : (P : Subgroup L).map L.subtype = S' ⊓ L := by
    rw [hP, subgroupOf_map_subtype]
  have hQ : (omegaOneAmbient (P : Subgroup L)).map L.subtype = componentOmega H L S := by
    rw [map_omegaOneAmbient_injective L.subtype L.subtype_injective, hPm]
    rfl
  have hPS : (P : Subgroup L).map L.subtype ≤ S' := hPm ▸ inf_le_left
  have hQS : (omegaOneAmbient (P : Subgroup L)).map L.subtype ≤ S' :=
    (map_mono (omegaOneAmbient_le _)).trans hPS
  have hcL : center L = ⊥ := centerless_of_disjoint L hdis
  obtain ⟨t, ht⟩ := hzin
  have htn : t ≠ 1 := by
    intro he
    apply hLM
    intro x hx
    apply w.centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    have hh := ht ⟨x, hx⟩
    rw [he] at hh
    simp only [one_mul, inv_one, mul_one] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have hztwo : w.z ^ 2 = 1 := w.z_order ▸ pow_orderOf_eq_one w.z
  have ht2 : t ^ 2 = 1 := by
    apply MulAut.conj_injective_of_center_eq_bot hcL
    apply MulEquiv.ext
    intro x
    apply L.subtype_injective
    simp only [MulAut.conj_apply, one_mul, inv_one, mul_one, Subgroup.subtype_apply]
    calc
      _ = ((t * (t * x * t⁻¹) * t⁻¹ : L) : G) := by
        simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = w.z * (w.z * (x : G) * w.z⁻¹) * w.z⁻¹ := by rw [ht, ht]
      _ = w.z ^ 2 * (x : G) * (w.z ^ 2)⁻¹ := by simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = (x : G) := by rw [hztwo]; simp
  have htP : t ∈ P := (MulAut.involution_mem_sylow_of_centralizes P t ht2
    (fun x hx => L.subtype_injective (by
      change ((t * x * t⁻¹ : L) : G) = (x : G)
      rw [ht, (w.z_central (x : G) (hST (hPS (mem_map_of_mem L.subtype hx)))).eq]
      simp only [mul_assoc, mul_inv_cancel, mul_one]))).1
  have htQ : t ∈ omegaOneAmbient (P : Subgroup L) :=
    (omegaOneAmbient_le_iff _ _).mp le_rfl t htP ht2
  have hsize' : 2 < Nat.card (omegaOneAmbient (P : Subgroup L)) := by
    rw [← hQ, card_map_of_injective L.subtype_injective] at hsize
    exact hsize
  have hQU : (omegaOneAmbient (P : Subgroup L)).map L.subtype ≤ w.U := by
    apply MarkedInnerStrongClosure.map_le_of_transitive_inner_marker S' w.U hU
      L.subtype (omegaOneAmbient (P : Subgroup L)) hQS hsize' w.z w.z_mem ⟨t, htQ⟩ ht
    intro a ha
    have haG : (a : G) ≠ 1 := fun h => ha (Subtype.ext (Subtype.ext h))
    have htG : (t : G) ≠ 1 := fun h => htn (Subtype.ext h)
    have htQG : (t : G) ∈ componentOmega H L S := hQ ▸ mem_map_of_mem L.subtype htQ
    have haQG : (a : G) ∈ componentOmega H L S := hQ ▸ mem_map_of_mem L.subtype a.property
    obtain ⟨g, hg, he⟩ := htrans t htQG htG a haQG haG
    exact isConj_iff.mpr ⟨⟨g, hg.1⟩, Subtype.ext he⟩
  constructor
  · intro u
    let a := L.normalizerMonoidHom ⟨u, hUL u.property⟩
    obtain ⟨ha2, has, haf, had⟩ := MarkedInnerStrongClosure.omega_action_inputs
      S' w.U L hU hUL (P : Subgroup L) hP hQU u
    obtain ⟨g, hg, he⟩ := MarkedInnerStrongClosure.inner_implementer_mem_omega hcL P a ha2 has
      (hcriterion P a ha2 has haf had ⟨t, htP, htn, ht2⟩)
    refine ⟨⟨g, hQ ▸ mem_map_of_mem L.subtype hg⟩, ?_⟩
    rw [mem_centralizer_iff]
    intro x hx
    have hh := congrArg (fun α : MulAut L => α (g⁻¹ * (⟨x, hx⟩ : L) * g)) he
    have hhG := congrArg Subtype.val hh
    change (u : G) * ((g : G)⁻¹ * x * (g : G)) * (u : G)⁻¹ =
      (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ at hhG
    have hc : ((u : G) * (g : G)⁻¹) * x * ((u : G) * (g : G)⁻¹)⁻¹ = x := by
      calc
        _ = (u : G) * ((g : G)⁻¹ * x * (g : G)) * (u : G)⁻¹ := by group
        _ = (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ := hhG
        _ = x := by group
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  · intro q
    have hqU : (q : G) ∈ w.U := (hQ ▸ hQU) q.property
    exact ⟨⟨q, hqU⟩, by simp⟩

/-- The complete simple Bender list supplies whole-U inner implementers and
onto implementers in the literal component omega. Only the marked original
z-action and the existing concrete normalizer transitivity are used. -/
theorem LocalControlWitness.inner_omega_action_of_bender_model
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hdis : Disjoint L (centralizer (L : Set G)))
    (hmodel : ClassificationModels.IsBenderModel L)
    (hzin : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹)
    (hsize : 2 < Nat.card (componentOmega H L S))
    (htrans : ∀ a ∈ componentOmega H L S, a ≠ 1 →
      ∀ b ∈ componentOmega H L S, b ≠ 1 →
      ∃ n ∈ L ⊓ normalizer (componentOmega H L S : Set G), n * a * n⁻¹ = b) :
    (∀ u : w.U, ∃ q : componentOmega H L S,
      (u : G) * (q : G)⁻¹ ∈ centralizer (L : Set G)) ∧
    (∀ q : componentOmega H L S, ∃ u : w.U,
      (u : G) * (q : G)⁻¹ ∈ centralizer (L : Set G)) :=
  w.inner_omega_action_of_criterion H S hUS hST hcore L hL hLM hdis hzin
    (InnerActionModels.of_bender_model hmodel) hsize htrans

/-- The actual Bender component consumer with both whole-U action premises
discharged. Model selection, maximality, balance and the concrete normalizer
image facts retain exactly their source roles. -/
theorem LocalControlWitness.false_of_bender_omega_component
    (w : LocalControlWitness T M) {C : GroupClass} (hG : IsSimpleQTKE C G)
    (hTM : (T : Subgroup G) ≤ M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥) (L : Subgroup G) (hL : IsComponentIn L H)
    (hmax : Maximal (fun K => K ∈ badCentralizerComponents w) L)
    (hbalance : ∀ v ∈ componentFixedSubgroup w L, v ≠ 1 →
      ∃ K : Subgroup G, IsComponentIn K (centralizer ({v} : Set G)) ∧ L ≤ K)
    (hdis : Disjoint L (centralizer (L : Set G)))
    (hmodel : ClassificationModels.IsBenderModel L)
    (hzin : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹)
    (hsize : 2 < Nat.card (componentOmega H L S))
    (hcyclic : IsCyclic (normalizerAction L (componentOmega H L S)).range)
    (hodd : Odd (Nat.card (normalizerAction L (componentOmega H L S)).range))
    (htrans : ∀ a ∈ componentOmega H L S, a ≠ 1 →
      ∀ b ∈ componentOmega H L S, b ≠ 1 →
      ∃ n ∈ L ⊓ normalizer (componentOmega H L S : Set G), n * a * n⁻¹ = b) : False := by
  obtain ⟨hi, ho⟩ := w.inner_omega_action_of_bender_model H S hUS hST hcore L hL
    hmax.1.1 hdis hmodel hzin hsize htrans
  exact w.false_of_inner_component hG hTM L (componentOmega H L S) hmax hbalance
    ((omegaOneAmbient_le _).trans inf_le_right) hdis hi ho hsize hcyclic hodd htrans

end CFSG.Quasithin.Chapter2.BenderFusion
