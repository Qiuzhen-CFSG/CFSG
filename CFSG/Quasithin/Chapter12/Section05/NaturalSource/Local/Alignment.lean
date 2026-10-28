module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Actor
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.FlagSylow

/-!
# The Sylow-aligned exterior marking on the original module

Conjugate the extended actor into the standard flag group, changing its
quotient marking and exterior coordinates by the same SL₅(2) element.
The original V and the projection L → L/O₂(L) are unchanged. The source
application retains only the earlier structural 12.2.2 input that supplies
T-invariance of V; component and point-core assertions are not assumptions
of this construction.

Source: Aschbacher--Smith, notation preceding 12.5.2, printed p.817.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace ExteriorMarking
variable (a : ExteriorMarking D)

private def coordinateChange (g : Representation.SL5TenDimensional.Group) :
    Multiplicative Representation.SL5ExteriorSquare.V ≃*
      Multiplicative Representation.SL5ExteriorSquare.V :=
  (LinearMap.GeneralLinearGroup.toLinearEquiv
    ((Representation.SL5TenDimensional.exteriorAction 2).asGroupHom g)).toAddEquiv.toMultiplicative

private theorem coordinateChange_apply (g : Representation.SL5TenDimensional.Group)
    (w : Multiplicative Representation.SL5ExteriorSquare.V) :
    coordinateChange g w = Multiplicative.ofAdd
      (Representation.SL5TenDimensional.exteriorAction 2 g w.toAdd) := by
  change Multiplicative.ofAdd
    (((Representation.SL5TenDimensional.exteriorAction 2).asGroupHom g).val w.toAdd) = _
  rw [Representation.asGroupHom_apply]

private theorem action_conjugate (g h : Representation.SL5TenDimensional.Group)
    (w : Representation.SL5ExteriorSquare.V) :
    Representation.SL5TenDimensional.exteriorAction 2 g
      (Representation.SL5TenDimensional.exteriorAction 2 h w) =
    Representation.SL5TenDimensional.exteriorAction 2 (g * h * g⁻¹)
      (Representation.SL5TenDimensional.exteriorAction 2 g w) := by
  let σ := Representation.SL5TenDimensional.exteriorAction 2
  change (σ g * σ h) w = (σ (g * h * g⁻¹) * σ g) w
  rw [← map_mul, ← map_mul]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- Change the exterior coordinates and quotient marking by the same inner actor. -/
def conjugate (g : Representation.SL5TenDimensional.Group) : ExteriorMarking D where
  quotientEquiv := a.quotientEquiv.trans (MulAut.conj g)
  coordinates := a.coordinates.trans (coordinateChange g)
  equivariant l v := by
    change coordinateChange g (a.coordinates _) = _
    rw [a.equivariant, coordinateChange_apply]
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd
      (Representation.SL5TenDimensional.exteriorAction 2
        (g * a.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) * g⁻¹)
        (coordinateChange g (a.coordinates v)).toAdd)
    rw [coordinateChange_apply]
    exact congrArg Multiplicative.ofAdd (action_conjugate _ _ _)

/-- An extension of the literal actor can be aligned with the Sylow flag. -/
theorem sylowMarking_of_actor
    (α : (L ⊔ (T : Subgroup G) : Subgroup G) →* Representation.SL5TenDimensional.Group)
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G))
    (hc : ∀ l : L, α ⟨l, (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) l.property⟩ =
      a.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l))
    (he : ∀ (h : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
      a.coordinates ⟨(h : G) * v * (h : G)⁻¹,
        (mem_normalizer_iff.mp (hn h.property) v).mp v.property⟩ =
      Multiplicative.ofAdd (Representation.SL5TenDimensional.exteriorAction 2 (α h)
        (a.coordinates v).toAdd)) : Nonempty (SylowExteriorMarking D) := by
  let P := ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map α
  have hP : IsPGroup 2 P := T.isPGroup'.comap_subtype.map α
  obtain ⟨g, hg⟩ := Representation.SL5ExteriorSquare.exists_conjugate_le_flagGroup P hP
  refine ⟨{
    marking := a.conjugate g
    actor := (MulAut.conj g).toMonoidHom.comp α
    actor_component := ?_
    normalizes := hn
    equivariant := ?_
    sylow_flag := ?_ }⟩
  · intro l
    change MulAut.conj g (α _) = MulAut.conj g _
    rw [hc]
    rfl
  · intro h v
    change coordinateChange g (a.coordinates _) = _
    rw [he, coordinateChange_apply]
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd
      (Representation.SL5TenDimensional.exteriorAction 2 (g * α h * g⁻¹)
        (coordinateChange g (a.coordinates v)).toAdd)
    rw [coordinateChange_apply]
    exact congrArg Multiplicative.ofAdd (action_conjugate _ _ _)
  · intro t
    apply hg
    apply mem_map_of_mem
    exact mem_map_of_mem α t.property

include a in
/-- Construct a Sylow marking whenever T preserves the original V. -/
theorem exists_sylowExteriorMarking
    (hn : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    Nonempty (SylowExteriorMarking D) := by
  obtain ⟨α, hc, he⟩ := a.exists_join_actor hn
  exact a.sylowMarking_of_actor α (sup_le D.normalizes hn) hc he

end ExteriorMarking

/-- The source construction uses the earlier universal structural theorem,
whose proof is retained by the 12.2.2 owner. No ambient local conclusion is added. -/
theorem sylowExteriorMarking_source [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (a : ExteriorMarking D) : Nonempty (SylowExteriorMarking D) :=
  a.exists_sylowExteriorMarking ((structural G T L h).2.2 V D).1
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
