module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Final
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.Radical
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.NaturalSubmodule
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.Complement.Recovery
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.FieldFour
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Natural
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.RankOne
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.RankOne.Projection

/-!
# Assembly of the common pair from its rank-one recognition

The proved geometry identifies the source axis, makes the two conjugates
disjoint, and gives the internal direct product. The actual natural marking
proves full commutator generation, so identification with O₂(I) also
identifies O₂(K). All maps retain the original chosen V, H and conjugator.

The rank-one extension derives the cover from the exact 11.3.7 starred
Sylow image. The original Hall action now constructs the literal projection
with kernel P and hence the natural marking, with an application below to
the original counterexample. Earlier 11.3.7 inputs retain their source owner.
The block extension now excludes Sp₄, proves multiplicity two and identifies
the literal axis and intersection with the original flag plane. The radical
extension proves P ≤ R₂, equality of their original action images, [V,P] = V₂,
and the elementary quotient PV/V of order q² with its faithful action map.
The natural-submodule extension constructs the literal V_K = ⟨(Z ∩ P)^H⟩
= ⟨V₁^H⟩, its natural K-action and rank 2n, and proves
O₂(LT) ∩ V_K = V₁ and [O₂(LT),V_K] ≤ V₁.
The centralization extension proves L=[L,V_K] and identifies both
[O₂(LT),L] and [O₂(L),L] with V. The literal block model and full covering
map L/V → SL₃(q) are constructed, and the ordinary multiplier calculation
leaves precisely the q=4 branch with nontrivial O₂(L/V).
The complement extension places the original P in L and realizes PV/V as
the literal T-invariant complement, with its full plane-radical image. The
field-four parabolic obstruction removes the exceptional covering two-core,
proving V=O₂(L)=C_L(V) and R₂∩L=PV while retaining q=4.
The Thompson extension proves J(PV)=P by its literal shear fixed-index
comparison. The original inner Sylow normalizer supplies a scalar-plane torus
element; perfection of L₂ then recovers P=O₂(L₂), including q=4.
The final counterexample application assembles the block, cover and
P=J(PV)=O₂(L₂)=O₂(K)=O₂(I). Only the displayed preceding-source inputs remain,
with final discharge owned by qt-d-1222-shadow-common-core.
The field-four model obstruction is proved and re-exported here. The fixed-space
premise is the exact earlier conclusion of 11.3.7(3).

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
first three paragraphs of printed p.774.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {h : G} {F : BinaryField}

/-- The natural-action marking removes the separate commutator premise in
identification of the two-core of the actual residual. -/
theorem PairNaturalMarking.core_eq (c : PairNaturalMarking V H h F)
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hcover : outsideResidual H ≤ pairGroup V h ⊔ H.pCoreIn 2)
    (hcore : pairCore V H h = (pairGroup V h).pCoreIn 2) :
    pairCore V H h = (outsideResidual H).pCoreIn 2 :=
  pairCore_eq_residual_core_of_moved s hh
    (residual_le_pairGroup_of_cover s hh hcover) hcore c.commutator_eq

/-- Application to the original chosen-source counterexample. The remaining
recognition premises concern precisely the literal pair; they are not inferred
from a family label or from an unrelated quotient action. -/
theorem source_pair_core_identifications
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H) (hh : h ∈ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hcover : outsideResidual H ≤ pairGroup V h ⊔ H.pCoreIn 2)
    (hcore : pairCore V H h = (pairGroup V h).pCoreIn 2)
    (c : PairNaturalMarking V H h F) :
    ((pairGroup V h).subgroupOf H).Normal ∧
      outsideResidual (pairGroup V h) = outsideResidual H ∧
      axis V H = V ⊓ centralizer (omegaClosure T H : Set G) ∧
      V ⊓ V.map (MulAut.conj h).toMonoidHom = ⊥ ∧
      IsElementaryAbelian 2 (pairCore V H h) ∧
      pairCore V H h = (outsideResidual H).pCoreIn 2 ∧
      pairCore V H h ⊓ V = axis V H ∧
      pairCore V H h ⊓ centralizer (V : Set G) = axis V H ∧
      (axis V H).map (MulAut.conj h).toMonoidHom ⊓ centralizer (V : Set G) = ⊥ ∧
      Nat.card (pairCore V H h) = Nat.card (axis V H) ^ 2 ∧
      ∃ e : axis V H × (axis V H).map (MulAut.conj h).toMonoidHom ≃* pairCore V H h,
        ∀ b d, (e (b, d) : G) = (b : G) * (d : G) := by
  have hk := residual_le_pairGroup_of_cover s hh hcover
  have hz := pair_intersection_eq_bot s hf hk
  exact ⟨pairGroup_normal_in_H s hh hk, pairGroup_residual_eq s hh hk,
    axis_eq_fixed s p hc, hz, pairCore_elementary s hh hz,
    c.core_eq s hh hcover hcore, pairCore_inf_seed hh, pairCore_fixed_eq_axis s hf hh hk,
    conjugate_axis_faithful s hf hh hk, pairCore_card s hh hz,
    pairCore_direct_product s hh hz⟩

/-- The original source assembly after constructing its literal rank-one
projection. The preceding 11.3.7 conclusions give residual containment here;
the projection gives the core equality and the natural marking. The theorem below
constructs this projection from the preceding source data. -/
theorem source_pair_core_identifications_of_projection
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H) (hh : h ∈ H)
    (hm : h ∉ normalizer (L : Set G))
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hnot : ¬ V ≤ H.pCoreIn 2)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (Rstar : Sylow 2 (residualStar T H))
    (hRstar : (Rstar : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H))
    (q : pairGroup V h →* Matrix.SpecialLinearGroup (Fin 2) S.field.Carrier)
    (hq : Function.Surjective q)
    (hker : q.ker = (pairCore V H h).subgroupOf (pairGroup V h))
    (R Q : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) S.field.Carrier))
    (hR : (V.subgroupOf (pairGroup V h)).map q = R)
    (hQ : ((V.map (MulAut.conj h).toMonoidHom).subgroupOf (pairGroup V h)).map q = Q) :
    pairCore V H h = (pairGroup V h).pCoreIn 2 ∧
      Nonempty (PairNaturalMarking V H h S.field) ∧
    ((pairGroup V h).subgroupOf H).Normal ∧
      outsideResidual (pairGroup V h) = outsideResidual H ∧
      axis V H = V ⊓ centralizer (omegaClosure T H : Set G) ∧
      V ⊓ V.map (MulAut.conj h).toMonoidHom = ⊥ ∧
      IsElementaryAbelian 2 (pairCore V H h) ∧
      pairCore V H h = (outsideResidual H).pCoreIn 2 ∧
      pairCore V H h ⊓ V = axis V H ∧
      pairCore V H h ⊓ centralizer (V : Set G) = axis V H ∧
      (axis V H).map (MulAut.conj h).toMonoidHom ⊓ centralizer (V : Set G) = ⊥ ∧
      Nat.card (pairCore V H h) = Nat.card (axis V H) ^ 2 ∧
      ∃ e : axis V H × (axis V H).map (MulAut.conj h).toMonoidHom ≃* pairCore V H h,
        ∀ b d, (e (b, d) : G) = (b : G) * (d : G) := by
  have hk := source_residual_le_pairGroup s hh hm hnot hmodel Rstar hRstar
  have hcore := pairCore_eq_twoCore_of_projection hh q hq hker
  obtain ⟨c⟩ := natural_pair_of_projection s hh hf hk q hq hker R Q hR hQ
  exact ⟨hcore,⟨c⟩,source_pair_core_identifications s p hc hh hf
    (hk.trans le_sup_left) hcore c⟩

/-- Application of the completed pair recognition to the original chosen-source
counterexample. Only the preceding 11.3.7 natural action, Sylow image,
fixed-space conclusion and Hall containment remain explicit; their producer is
qt-d-1222-shadow-common-action and final discharge stays with
qt-d-1222-shadow-common-core. No pair-recognition callback remains. -/
theorem source_pair_core_identifications_from_preceding
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H) (hh : h ∈ H)
    (hm : h ∉ normalizer (L : Set G))
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hnot : ¬ V ≤ H.pCoreIn 2)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (Rstar : Sylow 2 (residualStar T H))
    (hRstar : (Rstar : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H))
    (cK : NaturalQuotientMarking T H S.field)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hAL : oddCartanPart A ≤ L) :
    pairCore V H h = (pairGroup V h).pCoreIn 2 ∧
      Nonempty (PairNaturalMarking V H h S.field) ∧
    ((pairGroup V h).subgroupOf H).Normal ∧
      outsideResidual (pairGroup V h) = outsideResidual H ∧
      axis V H = V ⊓ centralizer (omegaClosure T H : Set G) ∧
      V ⊓ V.map (MulAut.conj h).toMonoidHom = ⊥ ∧
      IsElementaryAbelian 2 (pairCore V H h) ∧
      pairCore V H h = (outsideResidual H).pCoreIn 2 ∧
      pairCore V H h ⊓ V = axis V H ∧
      pairCore V H h ⊓ centralizer (V : Set G) = axis V H ∧
      (axis V H).map (MulAut.conj h).toMonoidHom ⊓ centralizer (V : Set G) = ⊥ ∧
      Nat.card (pairCore V H h) = Nat.card (axis V H) ^ 2 ∧
      ∃ e : axis V H × (axis V H).map (MulAut.conj h).toMonoidHom ≃* pairCore V H h,
        ∀ b d, (e (b, d) : G) = (b : G) * (d : G) := by
  have hk := source_residual_le_pairGroup s hh hm hnot hmodel Rstar hRstar
  obtain ⟨hcore,⟨c⟩⟩ := source_pair_recognition s hh hm hf hnot hmodel cK
    Rstar hRstar A hA hHall hAL
  exact ⟨hcore,⟨c⟩,source_pair_core_identifications s p hc hh hf
    (hk.trans le_sup_left) hcore c⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
