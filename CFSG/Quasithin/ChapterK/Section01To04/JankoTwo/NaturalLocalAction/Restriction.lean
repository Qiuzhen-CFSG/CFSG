module

public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.MarkedApplications
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.NaturalLocalAction.Actors

/-!
# The marked J₂ local action and its actual displacement module

All actions here are restrictions of the supplied embedding into the octonion
G₂ model. The full noncentral centralizer acts on the range of the displacement
of `GeneratorPair.a`, since it commutes with that involution. This defines the
literal module W needed for a comparison with the natural SL₂(4) action.

The constructed rank-four subgroup is transported to the original marked
source group. Equivariance transports its fixed codimension, cubicity and
quadraticity, so a calculation on the natural quotient supplies an actual
source actor. The missing root and representation comparisons are not included
as fields of the marking or asserted as conclusions here.

Source: Aschbacher–Smith, K.4.5, printed p.460/PDF p.471.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.JankoTwo
open Subgroup Representation Representation.BinaryOffender
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.InnerInvolutionCores
open NaturalLocalAction

variable {K G V : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

namespace MarkedModule
variable (D : MarkedModule (K := K) ρ)

/-- The literal degree-100 carrier embedded into the marked source group. -/
def carrierMap : Carrier →* G := D.inner.subtype.comp D.carrierEquiv.symm.toMonoidHom

theorem carrierMap_injective : Function.Injective D.carrierMap :=
  D.inner.subtype_injective.comp D.carrierEquiv.symm.injective

/-- The literal degree-100 carrier embedded into the actual octonion group. -/
def carrierEmbedding : Carrier →* Atlas.G2.Model K :=
  D.embedding.comp D.carrierEquiv.symm.toMonoidHom

theorem carrierEmbedding_injective : Function.Injective D.carrierEmbedding :=
  D.embedding_injective.comp D.carrierEquiv.symm.injective

/-- The binary action on the original source module, restricted to J₂. -/
abbrev carrierAction : Representation (ZMod 2) Carrier V := ρ.comp D.carrierMap

/-- The K-linear action restricted through this particular J₂ embedding. -/
abbrev naturalCarrierKAction : Representation K Carrier (Atlas.G2.Natural.Space K) :=
  (Atlas.G2.Natural.action K).comp D.carrierEmbedding

/-- Its binary restriction, on the actual octonion quotient. -/
abbrev naturalCarrierAction : Representation (ZMod 2) Carrier (Atlas.G2.Natural.Space K) :=
  (naturalAction K).comp D.carrierEmbedding

theorem carrier_equivariant (g : Carrier) (v : V) :
    D.equiv.toLinearEquiv (D.carrierAction g v) =
      D.naturalCarrierAction g (D.equiv.toLinearEquiv v) :=
  D.inner_equivariant (D.carrierEquiv.symm g) v

/-- The genuine full-centralizer action in its checked E₄ × A₅ coordinates. -/
abbrev localAction : Representation K (E4 × A5) (Atlas.G2.Natural.Space K) :=
  D.naturalCarrierKAction.comp centralizerEmbedding

private theorem local_commutes_displacement (g : E4 × A5)
    (v : Atlas.G2.Natural.Space K) :
    D.localAction g ((D.naturalCarrierKAction a - LinearMap.id : Module.End K (Atlas.G2.Natural.Space K)) v) =
      (D.naturalCarrierKAction a - LinearMap.id : Module.End K (Atlas.G2.Natural.Space K)) (D.localAction g v) := by
  have hc : centralizerEmbedding g * a = a * centralizerEmbedding g :=
    mem_centralizer_singleton_iff.mp (a_centralizer_equiv.symm g).property
  have he := congrArg (fun x : Carrier => D.naturalCarrierKAction x v) hc
  simp only [map_mul, Module.End.mul_apply] at he
  change D.naturalCarrierKAction (centralizerEmbedding g)
      (D.naturalCarrierKAction a v - v) =
    D.naturalCarrierKAction a (D.naturalCarrierKAction (centralizerEmbedding g) v) -
      D.naturalCarrierKAction (centralizerEmbedding g) v
  rw [map_sub, he]

/-- W is the actual displacement space [V,a], carrying the full centralizer action. -/
def localW : Subrepresentation D.localAction where
  toSubmodule := LinearMap.range (D.naturalCarrierKAction a - LinearMap.id)
  apply_mem_toSubmodule g v hv := by
    obtain ⟨w, rfl⟩ := hv
    exact ⟨D.localAction g w, (D.local_commutes_displacement g w).symm⟩

theorem mem_localW (v : Atlas.G2.Natural.Space K) :
    v ∈ D.localW ↔ ∃ w, D.naturalCarrierKAction a w - w = v := Iff.rfl

/-- Explicit compatibility with the ambient action; no unrelated E₄ × A₅ module is used. -/
theorem localW_action_val (g : E4 × A5) (w : D.localW.toSubmodule) :
    (D.localW.toRepresentation g w).val =
      Atlas.G2.Natural.action K (D.carrierEmbedding (centralizerEmbedding g)) w.val := rfl

/-- The actual rank-four actor in the original source group. -/
def sourceActor : Subgroup G := actor.map D.carrierMap

theorem sourceActor_le_inner : D.sourceActor ≤ D.inner := by
  rintro _ ⟨x, _, rfl⟩
  exact (D.carrierEquiv.symm x).property

theorem sourceActor_rank : rank D.sourceActor = 4 := by
  rw [sourceActor, rank_map_injective _ D.carrierMap_injective, actor_rank]

theorem sourceActor_elementary : IsElementaryTwo D.sourceActor := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 actor := actor_elementary.2
  refine ⟨?_, IsElementaryAbelian.map _⟩
  intro h
  have hr := D.sourceActor_rank
  rw [h, Representation.BinaryOffender.rank_bot] at hr
  omega

theorem noncentral_mem_sourceActor : D.carrierMap a ∈ D.sourceActor :=
  Subgroup.mem_map_of_mem _ a_mem_actor

theorem carrier_fixedCodim (A : Subgroup Carrier) :
    fixedCodim ρ (A.map D.carrierMap) = fixedCodim D.naturalCarrierAction A := by
  have hsource : fixedCodim D.carrierAction A = fixedCodim ρ (A.map D.carrierMap) := by
    unfold fixedCodim
    rw [fixedSpace_comp_map]
  have hnatural := fixedCodim_map_equivariant D.carrierAction D.naturalCarrierAction
    (MonoidHom.id Carrier) D.equiv.toLinearEquiv D.carrier_equivariant A
  rw [Subgroup.map_id] at hnatural
  exact hsource.symm.trans hnatural

private theorem carrier_displacement (g : Carrier) (v : V) :
    D.equiv.toLinearEquiv (displacement ρ (D.carrierMap g) v) =
      displacement D.naturalCarrierAction g (D.equiv.toLinearEquiv v) := by
  change D.equiv.toLinearEquiv (ρ (D.carrierMap g) v - v) =
    D.naturalCarrierAction g (D.equiv.toLinearEquiv v) - D.equiv.toLinearEquiv v
  rw [map_sub]
  exact congrArg (fun w => w - D.equiv.toLinearEquiv v) (D.carrier_equivariant g v)

/-- Cubicity is transported on this specific embedding and equivariant quotient. -/
theorem carrier_cubic_iff (A : Subgroup Carrier) :
    IsCubic ρ (A.map D.carrierMap) ↔ IsCubic D.naturalCarrierAction A := by
  constructor
  · intro h g hg k hk l hl w
    obtain ⟨v, rfl⟩ := D.equiv.toLinearEquiv.surjective w
    have he := congrArg D.equiv.toLinearEquiv
      (h _ (mem_map_of_mem _ hg) _ (mem_map_of_mem _ hk) _ (mem_map_of_mem _ hl) v)
    simpa only [D.carrier_displacement, map_zero] using he
  · rintro h _ ⟨g, hg, rfl⟩ _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩ v
    apply D.equiv.toLinearEquiv.injective
    simpa only [D.carrier_displacement, map_zero] using
      h g hg k hk l hl (D.equiv.toLinearEquiv v)

/-- Quadraticity is transported by the same actual equivariant map. -/
theorem carrier_quadratic_iff (A : Subgroup Carrier) :
    IsQuadratic ρ (A.map D.carrierMap) ↔ IsQuadratic D.naturalCarrierAction A := by
  constructor
  · intro h g hg k hk w
    obtain ⟨v, rfl⟩ := D.equiv.toLinearEquiv.surjective w
    have he : displacement ρ (D.carrierMap g) (displacement ρ (D.carrierMap k) v) = 0 :=
      sub_eq_zero.mpr (h _ (mem_map_of_mem _ hg) _ (mem_map_of_mem _ hk) v)
    have hz : displacement D.naturalCarrierAction g
        (displacement D.naturalCarrierAction k (D.equiv.toLinearEquiv v)) = 0 := by
      simpa only [D.carrier_displacement, map_zero] using congrArg D.equiv.toLinearEquiv he
    exact sub_eq_zero.mp hz
  · rintro h _ ⟨g, hg, rfl⟩ _ ⟨k, hk, rfl⟩ v
    apply sub_eq_zero.mp
    apply D.equiv.toLinearEquiv.injective
    change D.equiv.toLinearEquiv
      (displacement ρ (D.carrierMap g) (displacement ρ (D.carrierMap k) v)) =
        D.equiv.toLinearEquiv 0
    have he : displacement D.naturalCarrierAction g
        (displacement D.naturalCarrierAction k (D.equiv.toLinearEquiv v)) = 0 :=
      sub_eq_zero.mpr (h g hg k hk (D.equiv.toLinearEquiv v))
    simpa only [D.carrier_displacement, map_zero] using he

/-- Consumer of the remaining natural-action computation on the constructed actor.
The two representation premises remain to be proved; all subgroup and transport
requirements of the attaining witness are discharged. -/
theorem sourceActor_of_natural_calculation
    (hc : IsCubic D.naturalCarrierAction actor)
    (hd : fixedCodim D.naturalCarrierAction actor = 8) :
    IsElementaryTwo D.sourceActor ∧ rank D.sourceActor = 4 ∧
      IsCubic ρ D.sourceActor ∧ fixedCodim ρ D.sourceActor = 8 := by
  exact ⟨D.sourceActor_elementary, D.sourceActor_rank,
    (D.carrier_cubic_iff actor).mpr hc, (D.carrier_fixedCodim actor).trans hd⟩

end MarkedModule
end CFSG.Quasithin.ChapterK.JankoTwo
