module
public import Theory.SpecificGroups.G2.TernaryWeylCoordinates

/-!
# Full GL₂(3) compatibility on one ternary coordinate system

The Weyl normalization preserves the cubic, commutator form and marked
opposite derived line. Its possible scalar sign is exactly the determinant
twist of the actor. The two generator equations therefore identify the
whole GL₂(3) representation on these same coordinates. The explicit
short-to-long coordinate change intertwines the long action with that same
determinant twist; it does not identify the two conventions without it.

The original-group hypotheses are discharged in
G2Recognition.MaximalWeylCoordinates for Aschbacher–Smith I.4.5, p.417.
The literal model conventions retain the imported Atlas attribution in
LICENSES/ATLAS-CITATION.cff and LICENSES/ATLAS.txt.
-/

namespace Atlas.G2.TernaryLevi
/-- The scalar actor is the distinguished original coordinate involution. -/
public theorem shortQuotientAction_central (v : TernaryCore.V) :
    shortQuotientAction (-1) v=v⁻¹ := by
  let x := TernaryCore.short 0 v
  have hx : coreAction false (-1) x=TernaryCore.shortInvolution x := by
    apply Subtype.ext
    change embedding false (-1)*(x:Model (ZMod 3))*(embedding false (-1))⁻¹=_
    rw [embedding_central]
    exact (TernaryCore.shortInvolution_ambient x).symm
  calc
    _=shortQuotientAction (-1) (TernaryCore.shortQuotient x) :=
      congrArg (shortQuotientAction (-1)) (TernaryCore.shortQuotient_apply 0 v).symm
    _=TernaryCore.shortQuotient (coreAction false (-1) x) := shortQuotientAction_quotient _ x
    _=v⁻¹ := by rw [hx,TernaryCore.shortInvolution_apply,TernaryCore.shortQuotient_apply]

/-- The other scalar actor has the literal long-root coordinate involution. -/
public theorem longQuotientAction_central (v : TernaryCore.V) :
    longQuotientAction (-1) v=v⁻¹ := by
  let x := TernaryCore.long 0 v
  have hx : coreAction true (-1) x=TernaryCore.longInvolution x := by
    apply Subtype.ext
    change embedding true (-1)*(x:Model (ZMod 3))*(embedding true (-1))⁻¹=_
    rw [embedding_central]
    exact (TernaryCore.longInvolution_ambient x).symm
  calc
    _=longQuotientAction (-1) (TernaryCore.longQuotient x) :=
      congrArg (longQuotientAction (-1)) (TernaryCore.longQuotient_apply 0 v).symm
    _=TernaryCore.longQuotient (coreAction true (-1) x) := longQuotientAction_quotient _ x
    _=v⁻¹ := by rw [hx,TernaryCore.longInvolution_apply,TernaryCore.longQuotient_apply]
end Atlas.G2.TernaryLevi
namespace Atlas.G2.TernaryCore
/-- The same cubic and form coordinates extend to the whole GL₂(3) action;
the permitted determinant twist changes only the marking of the actor. -/
public theorem exists_shortAction_normalization
    (ρ : TernaryLevi.GL23 →* MulAut V)
    (hroot : ∀ v,ρ (TernaryLevi.generator false) v=shortRoot v)
    (hcentral : ∀ v,ρ (-1) v=v⁻¹)
    (hplane : ∀ v,v.toAdd 0=0 → v.toAdd 3=0 →
      (ρ (TernaryLevi.generator true) v).toAdd 0=0 ∧
      (ρ (TernaryLevi.generator true) v).toAdd 3=0) :
    ∃ (κ : TernaryLevi.GL23 ≃* TernaryLevi.GL23) (e : V ≃* V),
      κ (TernaryLevi.generator false)=TernaryLevi.generator false ∧
      (∀ a v,e (ρ a v)=TernaryLevi.shortQuotientAction (κ a) (e v)) ∧
      (∀ v z,shortForm (e v) (e z)=shortForm v z) ∧
      (∀ v,(e v).toAdd 0=0 ∧ (e v).toAdd 2=0 ∧ (e v).toAdd 3=0 ↔
        v.toAdd 0=0 ∧ v.toAdd 2=0 ∧ v.toAdd 3=0) := by
  obtain ⟨e,c,hc,heU,heW,hform,hline⟩ := exists_shortWeyl_normalization ρ hroot hcentral hplane
  have hcases : c=1 ∨ c= -1 := (by decide : ∀ c : ZMod 3,c*c=1 → c=1 ∨ c= -1) c hc
  rcases hcases with h | h
  · refine ⟨MulEquiv.refl _,e,rfl,?_,hform,hline⟩
    apply TernaryLevi.equivariant_of_generators ρ TernaryLevi.shortQuotientAction e
    intro b v
    cases b with
    | false => rw [hroot,heU,TernaryLevi.shortQuotientAction_root]
    | true =>
      apply Multiplicative.toAdd.injective
      rw [TernaryLevi.shortQuotientAction_weyl,heW,h,one_smul]
  · refine ⟨TernaryLevi.determinantTwist,e,TernaryLevi.determinantTwist_root,?_,hform,hline⟩
    apply TernaryLevi.equivariant_of_generators ρ
      (TernaryLevi.shortQuotientAction.comp TernaryLevi.determinantTwist.toMonoidHom) e
    intro b v
    change e (ρ (TernaryLevi.generator b) v)=
      TernaryLevi.shortQuotientAction (TernaryLevi.determinantTwist (TernaryLevi.generator b)) (e v)
    cases b with
    | false => rw [TernaryLevi.determinantTwist_root,hroot,heU,TernaryLevi.shortQuotientAction_root]
    | true =>
      rw [TernaryLevi.determinantTwist_weyl,map_mul]
      change e (ρ (TernaryLevi.generator true) v)=TernaryLevi.shortQuotientAction (-1)
        (TernaryLevi.shortQuotientAction (TernaryLevi.generator true) (e v))
      rw [TernaryLevi.shortQuotientAction_central,TernaryLevi.shortQuotientAction_weyl]
      apply Multiplicative.toAdd.injective
      rw [heW,h,neg_one_smul]
      rfl

/-- The literal long-root convention uses the determinant-twisted actor on
the same form-preserving short/long change of coordinates. -/
public theorem shortLongCoordinates_action (a : TernaryLevi.GL23) (v : V) :
    shortLongCoordinates (TernaryLevi.shortQuotientAction a v)=
      TernaryLevi.longQuotientAction (TernaryLevi.determinantTwist a) (shortLongCoordinates v) := by
  apply TernaryLevi.equivariant_of_generators TernaryLevi.shortQuotientAction
    (TernaryLevi.longQuotientAction.comp TernaryLevi.determinantTwist.toMonoidHom)
    shortLongCoordinates ?_ a v
  intro b v
  change shortLongCoordinates (TernaryLevi.shortQuotientAction (TernaryLevi.generator b) v)=
    TernaryLevi.longQuotientAction (TernaryLevi.determinantTwist (TernaryLevi.generator b)) (shortLongCoordinates v)
  cases b with
  | false => rw [TernaryLevi.determinantTwist_root,TernaryLevi.shortQuotientAction_root,
      TernaryLevi.longQuotientAction_root,shortLongCoordinates_root]
  | true =>
    rw [TernaryLevi.determinantTwist_weyl,map_mul]
    change shortLongCoordinates (TernaryLevi.shortQuotientAction (TernaryLevi.generator true) v)=
      TernaryLevi.longQuotientAction (-1)
        (TernaryLevi.longQuotientAction (TernaryLevi.generator true) (shortLongCoordinates v))
    rw [TernaryLevi.longQuotientAction_central,TernaryLevi.longQuotientAction_weyl,
      TernaryLevi.shortQuotientAction_weyl]
    exact shortLongCoordinates_weyl v
end Atlas.G2.TernaryCore
