module

public import Theory.GroupTheory.ElementFusionWeakClosure
public import Theory.ElementaryAbelian.BinaryRankDifference
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global

/-!
# Fusion, intersections and the rank parameter in 12.6

The arguments following Lemma 12.6.19 use element fusion to correct actual
conjugators into centralizers. Trivial intersection of distinct M-conjugates
suffices; normality of V in M is not needed. A centralizer escaping N_G(V)
then fixes a subgroup in two distinct conjugates, converting the intersection
bound to the source parameter r(G,V).

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 12.6.20(1–3) and Lemma 12.6.21, printed pp.828–829.
The fusion theorem 12.6.19, nonsingular centralizer theorem 12.6.2, and
intrinsic module calculations remain explicit inputs to these bridges.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter12.Section06.CentralLine
open Subgroup ChapterE
variable {G : Type*} [Group G]

/-- Element fusion in the source module, controlled by the original L. -/
def ControlsElementFusion (L V : Subgroup G) : Prop :=
  ∀ v ∈ V, ∀ g : G, MulAut.conj g v ∈ V →
    ∃ l ∈ L, MulAut.conj l v = MulAut.conj g v

/-- The TI property inside M, without asserting that M normalizes V. -/
def HasTIConjugatesIn (V M : Subgroup G) : Prop :=
  ∀ m ∈ M, V ⊓ V.map (MulAut.conj m).toMonoidHom = ⊥ ∨
    V.map (MulAut.conj m).toMonoidHom = V

/-- Lemma 12.6.20(2): the correcting element belongs to the actual C_G(v). -/
theorem centralizer_conjugator {L V : Subgroup G}
    (hL : L ≤ normalizer (V : Set G)) (hf : ControlsElementFusion L V)
    {v g : G} (hv : v ∈ V)
    (hvg : v ∈ V.map (MulAut.conj g).toMonoidHom) :
    ∃ c : centralizer ({v} : Set G),
      V.map (MulAut.conj (c : G)).toMonoidHom =
        V.map (MulAut.conj g).toMonoidHom := by
  apply exists_centralizer_conjugator_of_element_fusion _ hvg
  intro a ha
  obtain ⟨l, hl, he⟩ := hf v hv a ha
  exact ⟨l, hL hl, he⟩

/-- A nonidentity element with centralizer in M is in a unique conjugate
of V, using the TI property in M and L-controlled fusion. -/
theorem unique_conjugate_of_centralizer_le {L V M : Subgroup G}
    (hL : L ≤ normalizer (V : Set G)) (hf : ControlsElementFusion L V)
    (hTI : HasTIConjugatesIn V M) {v g : G}
    (hv : v ∈ V) (hv1 : v ≠ 1)
    (hC : centralizer ({v} : Set G) ≤ M)
    (hvg : v ∈ V.map (MulAut.conj g).toMonoidHom) :
    V.map (MulAut.conj g).toMonoidHom = V := by
  obtain ⟨c, hc⟩ := centralizer_conjugator hL hf hv hvg
  rcases hTI c (hC c.property) with hi | he
  · have hx : v ∈ V ⊓ V.map (MulAut.conj (c : G)).toMonoidHom :=
      ⟨hv, hc.symm ▸ hvg⟩
    exact (hv1 (mem_bot.mp (hi ▸ hx))).elim
  · exact hc.symm.trans he

/-- The nonidentity intersection lies in the exceptional orbit. For 12.6.20,
S is the weight-four set; identity is deliberately excluded. -/
theorem intersection_mem_of_centralizers {L V M : Subgroup G} {S : Set G}
    (hL : L ≤ normalizer (V : Set G)) (hf : ControlsElementFusion L V)
    (hTI : HasTIConjugatesIn V M)
    (hC : ∀ v ∈ V, v ≠ 1 → v ∉ S → centralizer ({v} : Set G) ≤ M)
    {g : G} (hg : g ∉ normalizer (V : Set G)) :
    ∀ v ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom, v ≠ 1 → v ∈ S := by
  intro v hv hv1
  by_contra hn
  apply hg
  exact mem_normalizer_iff_map_conj_eq.mpr
    (unique_conjugate_of_centralizer_le hL hf hTI hv.1 hv1 (hC v hv.1 hv1 hn) hv.2)

/-- If g centralizes U ≤ V, then U is in the literal intersection V ∩ gVg⁻¹. -/
theorem le_intersection_of_centralizes {U V : Subgroup G} (hUV : U ≤ V)
    {g : G} (hg : g ∈ centralizer (U : Set G)) :
    U ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  intro u hu
  refine ⟨hUV hu, u, hUV hu, ?_⟩
  change g * u * g⁻¹ = u
  rw [← hg u hu, mul_inv_cancel_right]

/-- The intersection dimension estimate implies the lower bound for the
actual E.3 parameter, including an empty family of escaping centralizers. -/
theorem globalR_lower_bound [Finite G] {V : Subgroup G}
    [IsElementaryAbelian 2 V] {d k : ℕ}
    (hd : d ≤ Nat.log 2 (Nat.card V))
    (hi : ∀ g ∉ normalizer (V : Set G),
      Nat.log 2 (Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) ≤ k) :
    ((d - k : ℕ) : ℕ∞) ≤ globalR V := by
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hUV, hC⟩
  obtain ⟨g, hg, hgN⟩ := Set.not_subset.mp hC
  have hUI := le_intersection_of_centralizes hUV hg
  have hcard : Nat.card U ≤ Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hUI) (Subgroup.inclusion_injective hUI)
  have hU : Nat.log 2 (Nat.card U) ≤ k :=
    (Nat.log_mono_right hcard).trans (hi g hgN)
  have hr := log_card_sub_log_card_eq_log_relIndex V U hUV
  have hbound : d - k ≤ subgroupCorank V U := by
    unfold subgroupCorank
    omega
  exact_mod_cast hbound

/-- Centralizer containment transports along an actual M-conjugator. -/
theorem centralizer_le_of_conjugate {M : Subgroup G} {x l : G} (hl : l ∈ M)
    (hC : centralizer ({MulAut.conj l x} : Set G) ≤ M) :
    centralizer ({x} : Set G) ≤ M := by
  intro c hc
  have hcx : c * x = x * c := mem_centralizer_singleton_iff.mp hc
  have hc' : MulAut.conj l c ∈ centralizer ({MulAut.conj l x} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg (MulAut.conj l) hcx
  have hm := M.mul_mem (M.mul_mem (M.inv_mem hl) (hC hc')) hl
  simpa [MulAut.conj_apply, mul_assoc] using hm

/-- Lemma 12.6.21's orbit argument: one escaping centralizer, the exclusion
of all other weights, and transitivity on weight four give escape at every
weight-four vector. The existence premise is the relevant 12.2.13 alternative. -/
theorem centralizer_escape_on_orbit {L V M : Subgroup G} {S : Set G}
    (hLM : L ≤ M)
    (horbit : ∀ x ∈ S, ∀ y ∈ S, ∃ l ∈ L, MulAut.conj l x = y)
    (hC : ∀ v ∈ V, v ≠ 1 → v ∉ S → centralizer ({v} : Set G) ≤ M)
    (hescape : ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ M) :
    ∀ v ∈ S, ¬ centralizer ({v} : Set G) ≤ M := by
  obtain ⟨x, hxV, hx1, hxC⟩ := hescape
  have hxS : x ∈ S := by
    by_contra hn
    exact hxC (hC x hxV hx1 hn)
  intro v hvS hvC
  obtain ⟨l, hl, he⟩ := horbit x hxS v hvS
  exact hxC (centralizer_le_of_conjugate (hLM hl) (he.symm ▸ hvC))

end CFSG.Quasithin.Chapter12.Section06.CentralLine
