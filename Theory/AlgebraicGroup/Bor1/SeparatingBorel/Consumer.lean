module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.Source
public import Theory.AlgebraicGroup.Bor1.SingularTorusQuotient.ToralKernel

/-!
# The separating-Borel source theorem in the 13.15 envelope argument

The original hypotheses now produce the 13.12 witness certificate. Applying
the actual radical-quotient envelope theorem discharges the separating-Borel
premise of 13.15. Only the independent rank-one quotient intersection geometry
remains explicit, with its literal quotient map unchanged.

Source: Borel, *Linear Algebraic Groups*, IV, 13.12 and 13.15.
-/

public section
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
open SingularTorusQuotient
open SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

/-- The source witness certificate is now produced from the original
hypotheses, rather than assumed as the separating-Borel conclusion. -/
theorem separatingBorel_certificate
    (hG : Variety.IsConnected G) (T S P B : ClosedSubgroup G)
    (hT : IsMaximalTorus T) (hS : IsSubtorus S) (hP : IsSubtorus P)
    (hST : S ≤ T) (hPT : P ≤ T)
    (hScodim : Variety.dimension S.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (hPcodim : Variety.dimension P.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (hSP : S ≠ P)
    (hSn : ¬ Group.IsSolvable (Variety.Point S.centralizer.carrierVariety))
    (hPn : ¬ Group.IsSolvable (Variety.Point P.centralizer.carrierVariety))
    (hB : IsBorelSubgroup B) (hTB : T ≤ B) :
    Nonempty (Bor1Theorem13_12Certificate T B S P) := by
  obtain ⟨B',hB',hTB',hsep,hne⟩ :=
    exists_separating_borel hG T S P B hT hS hP hST hPT hScodim hPcodim hSP hSn hPn hB hTB
  exact ⟨⟨hB,hTB,B',hB',hTB',hsep,hne⟩⟩

/-- Actual 13.15 envelope consequence with the 13.12 separating witness
discharged. The remaining quotient-intersection premise is the independent
rank-one geometry theorem, retained with its original quotient map. -/
theorem envelope_fixed_le_radical_of_original_subtori
    (hG : Variety.IsConnected G) (T S P B U V : ClosedSubgroup G)
    (hT : IsMaximalTorus T) (hS : IsSubtorus S) (hP : IsSubtorus P)
    (hST : S ≤ T) (hPT : P ≤ T)
    (hScodim : Variety.dimension S.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (hPcodim : Variety.dimension P.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (hSP : S ≠ P)
    (hSn : ¬ Group.IsSolvable (Variety.Point S.centralizer.carrierVariety))
    (hPn : ¬ Group.IsSolvable (Variety.Point P.centralizer.carrierVariety))
    (hB : IsBorelSubgroup B) (hTB : T ≤ B)
    (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
    (hV : IsUnipotentRadicalOf B V)
    (R : ClosedSubgroup P.centralizer.carrierVariety) (hR : IsRadicalSubgroup R)
    {Q : Variety k} [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism P.centralizer.carrierVariety Q)
    (hq : Function.Surjective q.onPoints) (hker : q.kernel = R.toSubgroup)
    (hgeometry : ∀ A A' D : ClosedSubgroup Q,
      IsBorelSubgroup A → IsBorelSubgroup A' → IsMaximalTorus D →
      D ≤ A → D ≤ A' → A ≠ A' → IsSubtorus (A.inter A')) :
    (unipotentEnvelope (B.pointwiseCentralizer S) V).pointwiseCentralizer P ≤ U := by
  obtain ⟨B',hB',hTB',hsep,hne⟩ :=
    exists_separating_borel hG T S P B hT hS hP hST hPT hScodim hPcodim hSP hSn hPn hB hTB
  exact envelope_fixed_le_radical_of_rankOne_intersections hG hP hT hPT hTB hTB'
    hU hB hB' hV hsep (Ne.symm hne) R hR q hq hker hgeometry
end Theory.AlgebraicGroup.Bor1.SeparatingBorel
