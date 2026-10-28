module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionPreparation

/-!
# Separate source obligations in the equality extension argument

The extraspecial action calculation, the block and marked quotient
calculation, and the order-four fusion calculation have distinct inputs and
outputs. These structures specify their conclusions; they do not prove them.
The assembly module consumes them conditionally and retains their production
as source obligations.

All centralizers and quotients use the canonical K and P inside C_G(z).
The marked M/O₂(LT) quotient uses one quotient map for the image of L.
Its kernel is not required to lie in L, since it has order 32 in the
order-four case. No quotient assertion here asserts a splitting.

Source: Aschbacher--Smith, proof of 6.2.13, printed pp.687--688.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The extraspecial action calculation on p.687. This interface is an
intermediate target; its producer must construct it from the canonical pair. -/
structure EqualityExtensionAction (T L R : Subgroup G) (z : G) : Prop where
  sylow_centralizer : T ⊓ centralizer (layer L R : Set G) =
    layer L R ⊔ equalityCentralizer L R z
  core_centralizer : centralizer (equalityCore L R z : Set (centralizer ({z} : Set G))) =
    centralizer (equalityLayerClosure L R z : Set (centralizer ({z} : Set G)))
  quotient : Nonempty
    (((centralizer ({z} : Set G)) ⧸
      (equalityCore L R z ⊔ centralizer
        (equalityLayerClosure L R z : Set (centralizer ({z} : Set G))))) ≃*
      (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)))
  cubic_centralizer : ∃ X : Sylow 3 (centralizer ({z} : Set G)),
    equalityCore L R z ⊓ centralizer (X : Set (centralizer ({z} : Set G))) =
      coreCenter (equalityCore L R z)

/-- The block and marked quotient calculation, before excluding the four-group
case. The quotient kernel need not lie in L: it has order 32 in that case. -/
structure EqualityExtensionBlock (T L M R : Subgroup G) (z : G) : Prop where
  elementary : IsElementaryAbelian 2 (equalityCentralizer L R z)
  card : Nat.card (equalityCentralizer L R z) = 2 ∨
    Nat.card (equalityCentralizer L R z) = 4
  layer_core : layer L R = L.pCoreIn 2
  kernel_normal : (((L ⊔ T).pCoreIn 2).subgroupOf M).Normal
  marked_quotient : letI := kernel_normal
    ∃ e : (M ⧸ (((L ⊔ T).pCoreIn 2).subgroupOf M)) ≃* Equiv.Perm (Fin 5),
      (L.subgroupOf M).map (e.toMonoidHom.comp
        (QuotientGroup.mk' (((L ⊔ T).pCoreIn 2).subgroupOf M))) = alternatingGroup (Fin 5)

/-- The remaining fusion geometry on p.688, to be proved under |D|=4.
Elementary Q, D≤Q, D∩V=⟨z⟩ and normalizer control are discharged in the assembly. -/
structure EqualityExtensionFourFusion (T L R : Subgroup G) (z : G) : Prop where
  weak_closure : ∀ g : G, ((L ⊔ T).pCoreIn 2).conjBy g ≤ T →
    ((L ⊔ T).pCoreIn 2).conjBy g = (L ⊔ T).pCoreIn 2
  index : (equalityTransferSubgroup T L R z).relIndex T = 2
  fusion : ∀ t ∈ equalityTransferSubgroup T L R z, orderOf t = 2 → IsConj z t


end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
