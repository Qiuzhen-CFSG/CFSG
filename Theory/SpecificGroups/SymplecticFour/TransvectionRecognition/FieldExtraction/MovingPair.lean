module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.FieldExtraction.Descent
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.NormalClosure

/-!
# Trace-field models of the actual moving pair

The transvection normal closure inherits its literal rank-one witness and its
natural symplectic action. Once the original moving-pair geometry proves this
closure irreducible, minimal trace-field descent constructs its coefficient
model and compatible form. A companion theorem descends the whole pair
without identifying it with that closure.

These are the original-field consumers of the G.4.8 coefficient-model step
in Aschbacher--Smith E.2.7, printed pp.219--221.
-/

@[expose] public noncomputable section
open Subgroup Module
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open InvolutionTypes TwoConjugate Representation.TraceFieldDescent
variable {F : Type*} [Field F]

/-- The actual irreducible transvection normal closure has a minimal
coefficient model with an explicit scalar-extension equivalence and form. -/
theorem transvectionClosure_traceField_model
    (H : Subgroup (Sp F))
    (hi : Representation.IsIrreducible
      (((Representation.symplecticNatural 2).comp H.subtype).comp
        (transvectionClosure H).subtype))
    (hex : ∃ h ∈ H, IsB1 h) :
    Nonempty (Model
      (((Representation.symplecticNatural 2).comp H.subtype).comp
        (transvectionClosure H).subtype)
      (form F) (traceField (((Representation.symplecticNatural 2).comp H.subtype).comp
        (transvectionClosure H).subtype))) := by
  obtain ⟨d,hd,hb⟩ := hex
  let ρ := ((Representation.symplecticNatural 2).comp H.subtype).comp
    (transvectionClosure H).subtype
  let : Representation.IsIrreducible ρ := hi
  let t : transvectionClosure H := ⟨⟨d,hd⟩,Subgroup.subset_closure hb⟩
  have hr : finrank F (LinearMap.range (ρ t-1)) = 1 := by
    change finrank F (movedSpace d) = 1
    exact hb.2
  exact exists_traceField_model ρ t hr (form F) TwoLocalCover.form_alternating
    TwoLocalCover.form_nondegenerate (fun h => preserves_form (F := F) ((h : H) : Sp F))

/-- The same model on the literal moving pair's normal closure, with its
irreducibility premise discharged by the actual source geometry. -/
theorem moving_pair_transvectionClosure_traceField_model [CharP F 2] [Finite F]
    (hq : 2<Nat.card F) (a : EvenBorelTorus.ActorReduction.stabilizer (F:=F))
    (ha : ¬DiagramAutomorphisms.PreservesDiagram a.val)
    (V : Subgroup (Sp F)) [IsElementaryAbelian 2 V]
    (hV : V.map a.val.toMonoidHom=V)
    (hc : V≤(center (unipotent (F:=F))).map (unipotent (F:=F)).subtype)
    (hr : 2<Nat.card V) (hex : ∃ h∈oppositePair V, IsB1 h) :
    Nonempty (Model ((pairAction V).comp (transvectionClosure (oppositePair V)).subtype)
      (form F) (traceField ((pairAction V).comp (transvectionClosure (oppositePair V)).subtype))) :=
  transvectionClosure_traceField_model (oppositePair V)
    (moving_pair_transvectionClosure_irreducible hq a ha V hV hc hr hex) hex

/-- The whole original moving pair also has its own minimal trace-field model.
No identification of it with its transvection closure is needed here. -/
theorem moving_pair_traceField_model [CharP F 2] [Finite F]
    (hq : 2<Nat.card F) (a : EvenBorelTorus.ActorReduction.stabilizer (F:=F))
    (ha : ¬DiagramAutomorphisms.PreservesDiagram a.val)
    (V : Subgroup (Sp F)) (hV : V.map a.val.toMonoidHom=V)
    (hc : V≤(center (unipotent (F:=F))).map (unipotent (F:=F)).subtype)
    (hr : 2<Nat.card V) (hex : ∃ h∈oppositePair V, IsB1 h) :
    Nonempty (Model (pairAction V) (form F) (traceField (pairAction V))) := by
  obtain ⟨d,hd,hb⟩ := hex
  let : Representation.IsIrreducible (pairAction V) :=
    pairAction_irreducible_of_moving_actor hq a ha V hV hc hr
  have hdisp : finrank F (LinearMap.range (pairAction V ⟨d,hd⟩-1)) = 1 := by
    change finrank F (movedSpace d) = 1
    exact hb.2
  exact exists_traceField_model (pairAction V) ⟨d,hd⟩ hdisp (form F)
    TwoLocalCover.form_alternating TwoLocalCover.form_nondegenerate
    (fun h => preserves_form (F := F) (h : Sp F))

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
