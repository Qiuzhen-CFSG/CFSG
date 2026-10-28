module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowInputs
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.SpecificGroups.Alternating.SixSylowNormalizer

/-!
# Conditional assembly of the A₇ Sylow-normalizer argument

The two marked central points exist by the natural-module fixed-weight theorem.
The Sylow subgroup normalizes their local terminal derived subgroups. An element
of N(T) taking the weight-two point to the weight-six point transfers the first
residual into the second through the ambient O^{3′}-centralizer identity.
Its image in the literal O₂,Z quotient is an A₅ subgroup normalized by a Sylow
2-subgroup of A₆, contradicting the finite-group obstruction.

The last two theorems apply this argument to the earlier normalizer containment
and then to the existing fusion consumer. They remain conditional on the local
models, ambient residuals and escaping omega-centre action; no constructor for
these inputs is asserted here. The unconditional characteristic-subgroup lemma
also recovers source 3.3.6(c) from the actual setup and normalizer uniqueness.

Source: Aschbacher--Smith, 3.3.6(c), 3.3.22, printed pp.587,597--598;
the consumer is 12.3.5, printed p.809.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}
namespace SylowNormalizer

/-- Every natural chosen module has the two central representatives needed below. -/
theorem points_nonempty (E : S.NaturalCoordinates) (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    Nonempty (Points E) := by
  obtain ⟨x,hx,hxc⟩ := E.central_representative_weight structural (n := 2) (Or.inl rfl)
  obtain ⟨y,hy,hyc⟩ := E.central_representative_weight structural (n := 6) (Or.inr (Or.inr rfl))
  exact ⟨⟨x,y,hx,hy,hxc,hyc⟩⟩

omit [Finite G] in
lemma pointResidual_normalized (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    {x : G} (hx : x ∈ centralizer (T : Set G)) :
    (T : Subgroup G) ≤ normalizer (pointResidual L x : Set G) := by
  have hc : (T : Subgroup G) ≤ centralizer ({x} : Set G) := by
    intro t ht
    rw [mem_centralizer_singleton_iff]
    exact hx t ht
  have hn : (T : Subgroup G) ≤ normalizer ((L ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) :=
    (le_inf hTL (hc.trans (centralizer ({x} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact hn.trans (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))

omit [Finite G] in
lemma pointThreeResidual_conj (x g : G) :
    (pointThreeResidual x).map (MulAut.conj g).toMonoidHom =
      pointThreeResidual (g*x*g⁻¹) := by
  have hc : (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g*x*g⁻¹} : Set G) := by
    apply le_antisymm
    · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
        map_centralizer_le_centralizer_image ({x} : Set G) (MulAut.conj g).toMonoidHom
    · intro y hy
      refine ⟨g⁻¹*y*g, ?_, ?_⟩
      · change g⁻¹*y*g ∈ centralizer ({x} : Set G)
        rw [mem_centralizer_singleton_iff] at hy ⊢
        have he := congrArg (fun a : G => g⁻¹*a*g) hy
        simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left, mul_inv_cancel_left] using he
      · change g*(g⁻¹*y*g)*g⁻¹=y
        group
  unfold pointThreeResidual
  rw [map_embedded_primeToResidual, hc]

lemma transported_five_le_six {P : Points E} (M : P.Models) (R : P.AmbientResiduals)
    {g : G} (hg : g*(P.two:G)*g⁻¹=P.six) :
    P.five.map (MulAut.conj g).toMonoidHom ≤ P.sixGroup := by
  have he : pointThreeResidual (P.six : G) = P.sixGroup := by
    simpa only [one_mul] using R.six_residual 1 P.fixed.one_mem
  calc
    _ ≤ (pointThreeResidual (P.two:G)).map (MulAut.conj g).toMonoidHom := map_mono M.five_le_three
    _ = pointThreeResidual (P.six:G) := by rw [pointThreeResidual_conj, hg]
    _ = _ := he

lemma quotient_obstruction (T : Sylow 2 G) (K A : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (q : K →* alternatingGroup (Fin 6)) (hq : Function.Surjective q)
    (e : (A.subgroupOf K).map q ≃* alternatingGroup (Fin 5)) : False := by
  obtain ⟨P,hP⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow T K hTK
  apply Theory.SpecificGroups.Alternating.SixSylowNormalizer.no_sylow_normalizes_five
    (P.mapSurjective hq) ((A.subgroupOf K).map q) e
  change (P : Subgroup K).map q ≤ _
  apply (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map q)
  rw [hP]
  exact (Subgroup.comap_mono hTA).trans (Subgroup.le_normalizer_comap K.subtype)

lemma no_transport {P : Points E} (M : P.Models) (R : P.AmbientResiduals)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    {g : G} (hg : g ∈ normalizer (T : Set G)) :
    g*(P.two:G)*g⁻¹ ≠ P.six := by
  intro he
  obtain ⟨e⟩ := M.five_image g hg he (transported_five_le_six M R he)
  have hTK := pointResidual_normalized hTL P.six_central
  have hTA := pointResidual_normalized hTL P.two_central
  have hn : (T : Subgroup G) ≤ normalizer (P.five.map (MulAut.conj g).toMonoidHom : Set G) := by
    have hmap := (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hTA).trans
      (Subgroup.le_normalizer_map (MulAut.conj g).toMonoidHom)
    have ht : (T : Subgroup G).map (MulAut.conj g).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp hg
    rwa [ht] at hmap
  exact quotient_obstruction T P.sixGroup _ hTK hn (projection _ M.six_quotient)
    (M.six_quotient.surjective.comp (QuotientGroup.mk'_surjective _)) e

lemma no_characteristic_sylow_normal (S : Setup T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (C : Subgroup T) [C.Characteristic] (hne : C ≠ ⊥) :
    ¬ L ⊔ (T : Subgroup G) ≤ normalizer (C.map (T : Subgroup G).subtype : Set G) := by
  intro hn
  apply hescape
  have hCB : C.map (T : Subgroup G).subtype ≤ L ⊔ (T : Subgroup G) :=
    (Subgroup.map_subtype_le C).trans le_sup_right
  have hCne : C.map (T : Subgroup G).subtype ≠ ⊥ := by
    intro he
    exact hne ((Subgroup.map_eq_bot_iff_of_injective C
      (f := (T : Subgroup G).subtype) (T : Subgroup G).subtype_injective).mp he)
  exact (normalizer_le_normalizer_characteristic_image (T : Subgroup G) C).trans
    (S.hypothesis.toHypothesis1221.normal_subgroup_normalizer_le
      S.chosen.sylow_normalizes_component hCB hCne hn)

/-- The source containment follows once the escaping omega-centre action
has been established from the preceding residual and model identities. -/
lemma normalizer_le_of_omega_action {P : Points E} (M : P.Models) (R : P.AmbientResiduals)
    (hmove : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) →
      ∃ g ∈ normalizer (T : Set G), g*(P.two:G)*g⁻¹=P.six) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hn
  obtain ⟨g,hg,he⟩ := hmove hn
  exact no_transport M R S.chosen.sylow_normalizes_component hg he

lemma controlsFusion_of_omega_action {P : Points E} (M : P.Models) (R : P.AmbientResiduals)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hmove : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) →
      ∃ g ∈ normalizer (T : Set G), g*(P.two:G)*g⁻¹=P.six)
    (x y : G) (hx : x ∈ V) (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : ∃ g : G, g*x*g⁻¹=y) : ∃ l ∈ L, l*x*l⁻¹=y :=
  E.controlsFusion structural (normalizer_le_of_omega_action M R hmove) x y hx hy hx1 hy1 hxy

end SylowNormalizer
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
