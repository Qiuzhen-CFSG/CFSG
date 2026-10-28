module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PairPlus
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PairAction
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.PairOrthogonal

/-!
# The original faithful orthogonal pair in 12.6.26

The square form is preserved by the already constructed conjugation action.
Equality of its kernel with the central-quotient action kernel gives a
compatible first-isomorphism equivalence from the actual pair image in
H/O2(H). The two singular involution generators are the images of one
original element of V outside V5 and its specified conjugate.

PairPlus supplies extraspeciality, the explicit plus-type model, and the
two complementary singular four-spaces. The final theorem discharges the
extraspeciality premise of the action transport. The named action
specification retains every map and marking while limiting elaboration
of dependent quotient types. The dihedral order restriction, odd-core and
component exclusions, and abelian-span conclusion still require proof.
Source: Aschbacher--Smith F.9.5(6.ii), pp.319--320, and 12.6.26, p.831.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The literal square action of a conjugate pair. The witness retains the
ambient quotient map, its exact kernel, and the two images of one original
module element. This is a target specification, constructed from source
hypotheses below. -/
def SquarePairAction (H V W : Subgroup G) (g : G)
    (hs : IsExtraspecial 2 (W ⊔ W.map (MulAut.conj g).toMonoidHom : Subgroup G)) : Prop :=
  let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
  let P := W ⊔ W.map (MulAut.conj g).toMonoidHom
  letI := hs
  ∃ (hIH : I ≤ H) (n : I ≤ normalizer (P : Set G))
    (α : I →* (ExtraspecialSquare.form P).isometrySubgroup)
    (e : Setup.star H I ≃* α.range),
    α = (ExtraspecialSquare.isometryAction P).comp (seedConjugation I P n) ∧
    α.ker = (H.pCoreIn 2).subgroupOf I ∧
    (∀ i : I, (e ⟨QuotientGroup.mk' (pCore 2 H) (inclusion hIH i),
      mem_map_of_mem _ i.property⟩).val = α i) ∧
    ∃ a b : (ExtraspecialSquare.form P).isometrySubgroup, a^2=1 ∧ b^2=1 ∧
      (∀ v, ExtraspecialSquare.form P (a.val v-v)=0) ∧
      (∀ v, ExtraspecialSquare.form P (b.val v-v)=0) ∧
      α.range = zpowers a ⊔ zpowers b ∧
      ∃ v : V, v.val ∉ W ∧
        a = α ⟨v.val,mem_sup_left v.property⟩ ∧
        b = α ⟨(MulAut.conj g) v.val,
          mem_sup_right (mem_map_of_mem (MulAut.conj g).toMonoidHom v.property)⟩
end CFSG.Quasithin.Chapter12.Section06.Nonabelian

public section
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory
open ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- Transport of the original quotient image into the square-form isometry group.
The original plus-geometry theorem supplies extraspeciality below. -/
theorem SourceHypothesis.original_non_two_pair_square_action_of_extraspecial
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (g : G) (hg : g ∈ H)
    (hn : ¬ IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (hs : IsExtraspecial 2 ((D.fullSetup hZ T z).pairSeed g)) :
    Nonabelian.SquarePairAction H V (D.fullSetup hZ T z).V₅ g hs := by
  unfold Nonabelian.SquarePairAction
  let E := D.fullSetup hZ T z
  let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
  let P := E.pairSeed g
  let : IsExtraspecial 2 P := hs
  obtain ⟨hIH,n,α,e,hα,hker,hproj⟩ := S.original_non_two_pair_action D hZ z hz hTV hTz hbound hns hH g hg hn
  let β := (ExtraspecialSquare.isometryAction P).comp (seedConjugation I P n)
  have hk : α.ker=β.ker := by
    ext x
    change α x=1 ↔ ExtraspecialSquare.isometryAction P (seedConjugation I P n x)=1
    rw [ExtraspecialSquare.isometryAction_eq_one_iff,hα]
    rfl
  let j := (QuotientGroup.quotientKerEquivRange α).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans (QuotientGroup.quotientKerEquivRange β))
  have hj (i : I) : j ⟨α i,⟨i,rfl⟩⟩ = ⟨β i,⟨i,rfl⟩⟩ := by
    have hi : (QuotientGroup.quotientKerEquivRange α).symm ⟨α i,⟨i,rfl⟩⟩ =
        QuotientGroup.mk' α.ker i :=
      (QuotientGroup.quotientKerEquivRange α).symm_apply_apply (QuotientGroup.mk' α.ker i)
    change (QuotientGroup.quotientKerEquivRange β)
      ((QuotientGroup.quotientMulEquivOfEq hk)
        ((QuotientGroup.quotientKerEquivRange α).symm ⟨α i,⟨i,rfl⟩⟩)) = _
    rw [hi]
    rfl
  refine ⟨hIH,n,β,e.trans j,rfl,hk.symm.trans hker,?_,?_⟩
  · intro i
    have hi : e ⟨QuotientGroup.mk' (pCore 2 H) (inclusion hIH i),
        mem_map_of_mem _ i.property⟩ = ⟨α i,⟨i,rfl⟩⟩ := Subtype.ext (hproj i)
    change (j (e _)).val = β i
    rw [hi,hj]
  · have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
    exact Nonabelian.pair_square_generators h (E.perpendicular_index hz) g hg hn hs


/-- The original pair seed is plus type, and its actual quotient image has
the specified faithful square action with its original involution lifts.
The companion `original_non_two_pair_plus` identifies the two original
seed images as complementary singular four-spaces. -/
theorem SourceHypothesis.original_non_two_pair_orthogonal
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (g : G) (hg : g ∈ H)
    (hn : ¬ IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let E := D.fullSetup hZ T z
    Nonempty (E.pairSeed g ≃* DihedralCentralProductFourSix.FourModel) ∧
      ∃ hs : IsExtraspecial 2 (E.pairSeed g),
        Nonabelian.SquarePairAction H V E.V₅ g hs := by
  obtain ⟨hmodel,hs,_⟩ := S.original_non_two_pair_plus D hZ z hz hTV hTz hbound hns hH g hg hn
  exact ⟨hmodel,hs,
    S.original_non_two_pair_square_action_of_extraspecial D hZ z hz hTV hTz hbound hns hH g hg hn hs⟩

end CFSG.Quasithin.Chapter12.Section06
